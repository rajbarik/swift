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

STATISTIC(NumFunctionsWithProtocolArgsDevirtualized, "Number of functions with protocol args devirtualized");
using ArgIndexList = llvm::SmallVector<unsigned, 8>;

namespace {

class GenericSpecializer : public SILFunctionTransform {

  bool specializeAppliesInFunction(SILFunction &F);

  /// The entry point to the transformation.
  void run() override {
    SILFunction &F = *getFunction();
    DEBUG(llvm::dbgs() << "***** GenericSpecializer on function:" << F.getName()
                       << " *****\n");

    if (specializeAppliesInFunction(F))
      invalidateAnalysis(SILAnalysis::InvalidationKind::Everything);
  }

};

/// ProtocolDevirtualizer class.
class ProtocolDevirtualizer : public SILFunctionTransform {

  /// determine if the current function is a target for protocol devirtualizer.
  bool canDevirtualizeProtocolInFunction(ProtocolDevirtualizerAnalysis *PDA,
          llvm::SmallDenseMap<int, std::pair<ProtocolDecl*, ClassDecl *>> &Arg2DeclMap);

public:

  void run() override {
    auto *F = getFunction();

    /// Don't run protocol devirtualizer at -Os.
    if (F->optimizeForSize())
      return;

    /// Don't optimize functions that should not be optimized.
    if (F->empty() || (!F->shouldOptimize())) {
      return;
    }

    /// This is the function to optimize for protocol devirtualize.
    DEBUG(llvm::dbgs() << "*** ProtocolDevirtualization Pass on function: " << F->getName() << " ***\n");

    /// Use FunctionSignature Specialization to determine if this function
    /// can be specialized, without call graph information.
    if ( !canSpecializeFunction(F, nullptr, false)) {
      DEBUG(llvm::dbgs() << "  cannot specialize function -> abort\n");
      return;
    }

    CallerAnalysis *CA = PM->getAnalysis<CallerAnalysis>();
    const CallerAnalysis::FunctionInfo &FuncInfo = CA->getCallerInfo(F);

    /// Use FunctionSignature Specialization to determine if this function
    /// can be specialized, based on call graph.
    /// canSpecializeFunction does not consider generic methods -- TODO in future.
    if (!canSpecializeFunction(F, &FuncInfo, true)) {
      DEBUG(llvm::dbgs() << "  cannot specialize function -> abort\n");
      return;
    }

    /// Get the protocol devirtualizer pass that contains which protocols can be devirtualized.
    ProtocolDevirtualizerAnalysis *PDA = getAnalysis<ProtocolDevirtualizerAnalysis>();

    /// Determine the arguments that can be devirtualized.
    llvm::SmallDenseMap<int, std::pair<ProtocolDecl *, ClassDecl *>> Arg2DeclMap;
    if(!canDevirtualizeProtocolInFunction(PDA, Arg2DeclMap)) {
      DEBUG(llvm::dbgs() << "  cannot devirtualize function -> abort\n");
      return;
    }

    DEBUG(llvm::dbgs() << "Function::" << F->getName() << " has a Protocol Argument and can be optimized via PDA\n");

    /// Name Mangler for naming the protocol constrained generic method.
    auto P = Demangle::SpecializationPass::GenericSpecializer;
    Mangle::FunctionSignatureSpecializationMangler Mangler(P, F->isSerialized(), F);

    /// Save the arguments in a descriptor.
    llvm::SmallVector<ArgumentDescriptor, 4> ArgumentDescList;
    auto Args = F->begin()->getFunctionArguments();
    for (unsigned i = 0, e = Args.size(); i != e; ++i) {
      ArgumentDescList.emplace_back(Args[i]);
    }

    /// Instantiate the ProtocolDevirtualizerTransform pass.
    ProtocolDevirtualizerTransform PDT(F, Mangler, ArgumentDescList, Arg2DeclMap);

    /// Run the protocol devirtualizer.
    bool Changed = PDT.run();

    if (Changed) {
      /// Update statistics on the number of functions devirtualized.
      ++ NumFunctionsWithProtocolArgsDevirtualized;

      /// Invalidate Analysis as we introduce a new function.
      invalidateAnalysis(SILAnalysis::InvalidationKind::Everything);

      /// Make sure the PM knows about the new devirtualized inner function.
      notifyAddFunction(PDT.getDevirtualizedProtocolFunction(), F);

      /// should we restart pipeline? be conservative.
      restartPassPipeline();
    }
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

/// Check if any argument to a function meet the criteria for devirtualization.
bool ProtocolDevirtualizer::canDevirtualizeProtocolInFunction(ProtocolDevirtualizerAnalysis *PDA,
        llvm::SmallDenseMap<int, std::pair<ProtocolDecl*, ClassDecl *>> &Arg2DeclMap) {
  auto *F = getFunction();
  auto Args = F->begin()->getFunctionArguments();
  bool returnFlag = false;

  /// Analyze the argument for protocol conformance.
  for (unsigned i = 0, e = Args.size(); i != e; ++i) {
    auto ArgType = Args[i]->getType();
    /// Keep it simple for now. Do not handle Protocol constrained methods or Optionals.
    auto SwiftArgType = ArgType.getSwiftRValueType();
    if (ArgType && ArgType.isAnyExistentialType()) {
      auto SwiftProtoDecl = SwiftArgType.getAnyNominal();
      if (SwiftProtoDecl) {
        auto ProtoDecl = dyn_cast<ProtocolDecl>(SwiftProtoDecl);
        auto CD = PDA->getSoleClassImplementingProtocol(ProtoDecl);
        if (CD) {
          /// Save the mapping for transformation pass.
          Arg2DeclMap[i] = std::make_pair(ProtoDecl, CD);
          DEBUG(llvm::dbgs() << "Function: " << F->getName() << " has a singel class decl\n");
          returnFlag |= true;
        }
      }
    }
  }
  return returnFlag;
}

SILTransform *swift::createGenericSpecializer() {
  return new GenericSpecializer();
}

SILTransform *swift::createProtocolDevirtualizer() {
  return new ProtocolDevirtualizer();
}
