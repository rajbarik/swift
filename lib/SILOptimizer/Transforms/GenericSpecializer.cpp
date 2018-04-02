//===--- GenericSpecializer.cpp - Specialization of generic functions -----===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2017 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//
//
// Specialize calls to generic functions by substituting static type
// information.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "sil-generic-specializer"

#include "swift/SIL/OptimizationRemark.h"
#include "swift/SIL/SILFunction.h"
#include "swift/SIL/SILInstruction.h"
#include "swift/SILOptimizer/Utils/Generics.h"
#include "swift/SILOptimizer/Utils/Local.h"
#include "swift/SILOptimizer/PassManager/Transforms.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"

using namespace swift;

STATISTIC(NumFunctionsWithExistentialArgsSpecialized, "Number of functions with existential args specialized");
using ArgIndexList = llvm::SmallVector<unsigned, 8>;

namespace {

class GenericSpecializer : public SILFunctionTransform {

  bool specializeAppliesInFunction(SILFunction &F);

  /// The entry point to the transformation.
  void run() override {
    SILFunction &F = *getFunction();
    DEBUG(llvm::dbgs() << "***** GenericSpecializer on function:" << F.getName()
                       << " *****\n");

    if (specializeAppliesInFunction(F)){
      invalidateAnalysis(SILAnalysis::InvalidationKind::Everything);
    }
  }

};

/// ExistentialSpecializer class.
class ExistentialSpecializer : public SILFunctionTransform {

  /// Determine if the current function is a target for existential specialization of args.
  bool canSpecializeExistentialArgsInFunction(ApplySite &Apply, 
        llvm::SmallDenseMap<int, ExistentialTransformArgumentDescriptor> &ExistentialArgDescriptor);

  /// Can Callee be specialized?
  bool canSpecializeCalleeFunction(ApplySite &Apply);

  /// Specialize existential args in function F.
  void specializeExistentialArgsInAppliesWithinFunction(SILFunction &F);

  /// CallerAnalysis information.
  CallerAnalysis *CA;

public:

  void run() override {

    auto *F = getFunction();

    /// Don't optimize functions that should not be optimized.
    if (!F->shouldOptimize()) {
      return;
    }
    
    /// Get CallerAnalysis information handy.
    CA = PM->getAnalysis<CallerAnalysis>();

    /// Perform specialization.
    specializeExistentialArgsInAppliesWithinFunction(*F);
  }
};

} // end anonymous namespace

bool GenericSpecializer::specializeAppliesInFunction(SILFunction &F) {
  DeadInstructionSet DeadApplies;
  llvm::SmallSetVector<SILInstruction *, 8> Applies;
  OptRemark::Emitter ORE(DEBUG_TYPE, F.getModule());

  bool Changed = false;
  for (auto &BB : F) {
    // Collect the applies for this block in reverse order so that we
    // can pop them off the end of our vector and process them in
    // forward order.
    for (auto It = BB.rbegin(), End = BB.rend(); It != End; ++It) {
      auto *I = &*It;

      // Skip non-apply instructions, apply instructions with no
      // substitutions, apply instructions where we do not statically
      // know the called function, and apply instructions where we do
      // not have the body of the called function.
      ApplySite Apply = ApplySite::isa(I);
      if (!Apply || !Apply.hasSubstitutions())
        continue;

      auto *Callee = Apply.getReferencedFunction();
      if (!Callee)
        continue;
      if (!Callee->isDefinition()) {
        ORE.emit([&]() {
          using namespace OptRemark;
          return RemarkMissed("NoDef", *I)
                 << "Unable to specialize generic function "
                 << NV("Callee", Callee) << " since definition is not visible";
        });
        continue;
      }

      Applies.insert(Apply.getInstruction());
    }

    // Attempt to specialize each apply we collected, deleting any
    // that we do specialize (along with other instructions we clone
    // in the process of doing so). We pop from the end of the list to
    // avoid tricky iterator invalidation issues.
    while (!Applies.empty()) {
      auto *I = Applies.pop_back_val();
      auto Apply = ApplySite::isa(I);
      assert(Apply && "Expected an apply!");
      SILFunction *Callee = Apply.getReferencedFunction();
      assert(Callee && "Expected to have a known callee");

      if (!Callee->shouldOptimize())
        continue;

      // We have a call that can potentially be specialized, so
      // attempt to do so.
      llvm::SmallVector<SILFunction *, 2> NewFunctions;
      trySpecializeApplyOfGeneric(Apply, DeadApplies, NewFunctions, ORE);

      // Remove all the now-dead applies. We must do this immediately
      // rather than defer it in order to avoid problems with cloning
      // dead instructions when doing recursive specialization.
      while (!DeadApplies.empty()) {
        auto *AI = DeadApplies.pop_back_val();

        // Remove any applies we are deleting so that we don't attempt
        // to specialize them.
        Applies.remove(AI);

        recursivelyDeleteTriviallyDeadInstructions(AI, true);
        Changed = true;
      }

      // If calling the specialization utility resulted in new functions
      // (as opposed to returning a previous specialization), we need to notify
      // the pass manager so that the new functions get optimized.
      for (SILFunction *NewF : reverse(NewFunctions)) {
        notifyAddFunction(NewF, Callee);
      }
    }
  }

  return Changed;
}

/// Determine the following pattern.
/// %3 = global_addr @$P : $*SomeP
/// %4 = init_existential_addr %3 : $*SomeP, $SomeC
/// %5 = alloc_ref $SomeC
/// store %5 to %4 : $*SomeC
static SILValue findInitExistentialFromGlobalAddr(GlobalAddrInst *GAI) {
  /// Check for a single InitExistential.
  SILInstruction *SingleIE = NULL;
  for (auto Use : GAI->getUses()) {
    auto *User = Use->getUser();
    if(auto *InitExistential = dyn_cast<InitExistentialAddrInst>(User)) {
      if (SingleIE) return SILValue();
      SingleIE = InitExistential;
    }
  }
  if (!SingleIE) return SILValue();
  return cast<InitExistentialAddrInst>(SingleIE);
}

/// Get the Stack Address.
static SILValue getStackAddress(AllocStackInst *ASI, SILInstruction *ASIUser, bool &Copied) {
  SILInstruction *OneWrite = nullptr;
  for (auto Use : ASI->getUses()) {
    auto *User = Use->getUser();
    if (isa<DeallocStackInst>(User) || isa<DebugValueAddrInst>(User) ||
        isa<DestroyAddrInst>(User) || isa<WitnessMethodInst>(User) ||
        isa<DeinitExistentialAddrInst>(User) ||
        isa<OpenExistentialAddrInst>(User) ||
        User == ASIUser) {
      continue;
    }
    if (auto *CAI = dyn_cast<CopyAddrInst>(User)) {
      if (CAI->getDest() == ASI) {
        if (OneWrite)
          return SILValue();
        OneWrite = CAI;
        Copied = true;
      }
      continue;
    }
    if (isa<InitExistentialAddrInst>(User)) {
      if (OneWrite)
        return SILValue();
      OneWrite = User;
      continue;
    }
    if (isa<ApplyInst>(User) || isa<TryApplyInst>(User)) {
      auto Index = Use->getOperandNumber() - ApplyInst::getArgumentOperandNumber();
      auto Convention = FullApplySite(User).getArgumentConvention(Index);
      if (Convention != SILArgumentConvention::Indirect_In &&
          Convention != SILArgumentConvention::Indirect_In_Guaranteed)
        return SILValue();
      continue;
    }
    return SILValue();
  }
  if (!OneWrite) 
    return SILValue();
  SILBasicBlock *BB = OneWrite->getParent();
  if (BB != ASI->getParent() && BB != ASIUser->getParent())
    return SILValue();
  if (auto *CAI = dyn_cast<CopyAddrInst>(OneWrite)) {
    SILValue CAISource = CAI->getSrc();
    if (auto *ASI = dyn_cast<AllocStackInst>(CAISource))
      return getStackAddress(ASI, CAI, Copied);
    if (auto *GAI = dyn_cast<GlobalAddrInst>(CAISource)) {
      return findInitExistentialFromGlobalAddr(GAI);
    }
    return CAISource;
  }
  return cast<InitExistentialAddrInst>(OneWrite);
}


/// Find the concrete type of the existential argument.
static bool findConcreteType(ApplySite AI, SILValue Arg, CanType &ConcreteType) {
  bool Copied = false;

  /// Ignore any unconditional cast instructions. Is it Safe? Do we need to
  /// also add UnconditionalCheckedCastAddrInst? TODO.
  if (auto *Instance = dyn_cast<UnconditionalCheckedCastInst>(Arg)) {
      Arg = Instance->getOperand(); 
  }
  /// Handle AllocStack Instruction.
  if (auto *Instance = dyn_cast<AllocStackInst>(Arg)) {
    if (SILValue Src = getStackAddress(Instance, AI.getInstruction(), Copied)) {
      Arg = Src;
    }
  }

  /// init_existential_addr instructions
  if (auto *Open = dyn_cast<OpenExistentialAddrInst>(Arg)) {
    auto Op = Open->getOperand();
    auto *ASI = dyn_cast<AllocStackInst>(Op);
    if (!ASI)
      return false;

    SILValue StackWrite = getStackAddress(ASI, Open, Copied);
    if (!StackWrite)
      return false;

    if(auto *InitExistential = dyn_cast<InitExistentialAddrInst>(StackWrite)) {
      ConcreteType = InitExistential->getFormalConcreteType();
      return true;
    }
  } else if(auto *InitExistential = dyn_cast<InitExistentialAddrInst>(Arg)) {
      ConcreteType = InitExistential->getFormalConcreteType();
      return true;
  } else if (auto *Open = dyn_cast<OpenExistentialRefInst>(Arg)) {
    if (auto *InitExistential = dyn_cast<InitExistentialRefInst>(Open->getOperand())) {
      ConcreteType =  InitExistential->getFormalConcreteType();
      return true;
    }
  } else if (auto *InitExistential = dyn_cast<InitExistentialRefInst>(Arg)) {
    ConcreteType =  InitExistential->getFormalConcreteType();
    return true;
  } else if(auto *InitExistential = dyn_cast<InitExistentialAddrInst>(Arg)) {
    ConcreteType = InitExistential->getFormalConcreteType();
    return true;
  }
  return false;
}

/// Check if the callee uses the arg to dereference a witness method that
/// would then be converted into a direct method call and perhaps inlined.
static bool findIfCalleeUsesArgInWitnessMethod(SILValue Arg,
        ExistentialTransformArgumentDescriptor &ETAD) {
  bool PatternMatched = false;
  for (Operand *ArgUse : Arg->getUses()) {
    auto *ArgUser = ArgUse->getUser();
    if (auto *Open = dyn_cast<OpenExistentialAddrInst>(ArgUser)) {
      for (Operand *OpenUse : Open->getUses()) {
        auto *OpenUser = OpenUse->getUser();
        if (auto *WMI = dyn_cast<WitnessMethodInst>(OpenUser)) {
          PatternMatched = true;
          break;
        }
      }
    } else if (isa<OpenExistentialRefInst>(ArgUser)) {
      PatternMatched = true;
    } else if (isa<DestroyAddrInst>(ArgUser)) {
      ETAD.DestroyAddrUse = true;
    }
  }
  return PatternMatched;
}

/// Check if any argument to a function meet the criteria for specialization.
bool ExistentialSpecializer::canSpecializeExistentialArgsInFunction(ApplySite &Apply, llvm::SmallDenseMap<int, ExistentialTransformArgumentDescriptor> &ExistentialArgDescriptor) {
  auto *F = Apply.getReferencedFunction();
  auto Args = F->begin()->getFunctionArguments();
  bool returnFlag = false;
  const CallerAnalysis::FunctionInfo &FuncInfo = CA->getCallerInfo(F);
  auto *PAI = dyn_cast<PartialApplyInst>(Apply.getInstruction());
  int minPartialAppliedArgs = FuncInfo.getMinPartialAppliedArgs();

  /// Analyze the argument for protocol conformance.
  for (unsigned Idx = 0, Num = Args.size(); Idx < Num; ++Idx) {
    if (PAI && (Idx < Num - minPartialAppliedArgs)) continue;
    auto Arg = Args[Idx];
    auto ArgType = Arg->getType();
    auto SwiftArgType = ArgType.getSwiftRValueType();
    if (!ArgType || !SwiftArgType 
        || !(ArgType.isExistentialType()) 
        || ArgType.isAnyObject()  
        || SwiftArgType->isAny()
        ) continue;
    auto ExistentialRepr = Arg->getType().getPreferredExistentialRepresentation(F->getModule());
    if (!(ExistentialRepr == ExistentialRepresentation::Opaque || ExistentialRepr == ExistentialRepresentation::Class)) continue; 
    if (!(SwiftArgType->is<ProtocolType>() || 
          SwiftArgType->is<ProtocolCompositionType>())) continue;

    /// Find concrete type.
    CanType ConcreteType;
    ExistentialTransformArgumentDescriptor ETAD;
    ETAD.AccessType = OpenedExistentialAccess::Immutable;
    ETAD.DestroyAddrUse = false;
    auto ApplyArg = Apply.getArgument(PAI ? Idx-Num+minPartialAppliedArgs : Idx);
    if (!findConcreteType(Apply, ApplyArg, ConcreteType)) {
      DEBUG(llvm::dbgs() << ".. did not find concrete type.. bail..\n";);
      continue;
    }

    /// The caller should use it for a witness method.
    if (!(findIfCalleeUsesArgInWitnessMethod(Arg, ETAD) && (ETAD.DestroyAddrUse || ((Args[Idx]->getType().getPreferredExistentialRepresentation(F->getModule())) == ExistentialRepresentation::Class)))) {
      DEBUG(llvm::dbgs() << ".. no witness method and destroy use.. bail..\n";);
      continue;
    }
    /// Save the protocol declaration.
    ExistentialArgDescriptor[Idx]=ETAD;

    DEBUG(llvm::dbgs() << "Function: " << F->getName() << " Arg:" << Idx << "has a concrete type.\n");
    returnFlag |= true;
  }
  return returnFlag;
}

/// Can we specialize this function?
bool ExistentialSpecializer::canSpecializeCalleeFunction(ApplySite &Apply) {

  /// Disallow generic callees.
  if (Apply.hasSubstitutions())
    return false;

  /// Determine the caller of the apply.
  auto *Callee = Apply.getReferencedFunction();
  if (!Callee)
    return false;

  /// Callee should be optimizable.
  if (!Callee->shouldOptimize())
    return false;

  /// External function definitions.
  if ((!Callee->isDefinition()) || Callee->isExternalDeclaration())
    return false;

  /// For now ignore functions with indirect results.
  if (Callee->getConventions().hasIndirectSILResults())
    return false;

  /// Do not optimize always_inlinable functions.
  if (Callee->getInlineStrategy() == Inline_t::AlwaysInline) 
    return false;

  /// Only choose a select few function representations for specilization.
  if (Callee->getRepresentation() == SILFunctionTypeRepresentation::ObjCMethod || 
      Callee->getRepresentation() == SILFunctionTypeRepresentation::Block) {
    return false;
  }
  return true;
}

/// Specialize existential args passed to a function.
void ExistentialSpecializer::specializeExistentialArgsInAppliesWithinFunction(SILFunction &F) {
  bool Changed = false;
  for (auto &BB : F) {
    for (auto It = BB.begin(), End = BB.end(); It != End; ++It) {
      auto *I = &*It;

      /// Is it an apply site?
      ApplySite Apply = ApplySite::isa(I);
      if (!Apply)
        continue;
      
      /// Can the callee be specialized?
      if (!canSpecializeCalleeFunction(Apply))
        continue;

      auto *Callee = Apply.getReferencedFunction();

      /// Determine the arguments that can be specialized.
      llvm::SmallDenseMap<int, ExistentialTransformArgumentDescriptor> ExistentialArgDescriptor;
      if (!canSpecializeExistentialArgsInFunction(Apply, ExistentialArgDescriptor)) {
        DEBUG(llvm::dbgs() << "  cannot specialize existential args in function: " << Callee->getName() << " -> abort\n");
        continue;
      }

      DEBUG(llvm::dbgs() << "Function::" << Callee->getName() << " has an existential argument and can be optimized via ExistentialSpecializer\n");

      /// Name Mangler for naming the protocol constrained generic method.
      auto P = Demangle::SpecializationPass::GenericSpecializer;
      Mangle::FunctionSignatureSpecializationMangler Mangler(P, Callee->isSerialized(), Callee);

      /// Save the arguments in a descriptor.
      llvm::SmallVector<ArgumentDescriptor, 4> ArgumentDescList;
      auto Args = Callee->begin()->getFunctionArguments();
      for (unsigned i = 0, e = Args.size(); i != e; ++i) {
        ArgumentDescList.emplace_back(Args[i]);
      }

      /// This is the function to optimize for existential specilizer.
      DEBUG(llvm::dbgs() << "*** ExistentialSpecializer Pass on function: " << Callee->getName() << " ***\n");


      /// Instantiate the ExistentialSpecializerTransform pass.
      ExistentialSpecializerTransform EST(Callee, Mangler, ArgumentDescList, ExistentialArgDescriptor);

      /// Run the protocol devirtualizer.
      Changed = EST.run();

      if (Changed) {
        /// Update statistics on the number of functions devirtualized.
        ++ NumFunctionsWithExistentialArgsSpecialized;

        /// Make sure the PM knows about the new specialized inner function.
        notifyAddFunction(EST.getExistentialSpecializedFunction(), Callee);

        /// Invalidate analysis results of Callee.
        PM->invalidateAnalysis(Callee, SILAnalysis::InvalidationKind::Everything);
      }
    }
  }
  return;
}

SILTransform *swift::createGenericSpecializer() {
  return new GenericSpecializer();
}

SILTransform *swift::createExistentialSpecializer() {
  return new ExistentialSpecializer();
}
