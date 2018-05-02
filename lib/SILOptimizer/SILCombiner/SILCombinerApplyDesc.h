//===--- SILCombiner.h ------------------------------------------*- C++ -*-===//
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
// A port of LLVM's InstCombiner to SIL. Its main purpose is for performing
// small combining operations/peepholes at the SIL level. It additionally
// performs dead code elimination when it initially adds instructions to the
// work queue in order to reduce compile time by not visiting trivially dead
// instructions.
//
//===----------------------------------------------------------------------===//

#ifndef SWIFT_SILOPTIMIZER_PASSMANAGER_SILCOMBINERAPPLYDESC_H
#define SWIFT_SILOPTIMIZER_PASSMANAGER_SILCOMBINERAPPLYDESC_H

#include "swift/SIL/SILInstruction.h"
#include "swift/SIL/SILValue.h"
#include "swift/SILOptimizer/Utils/Local.h"

namespace swift {

/// This struct carries information about arguments of apply instructions
/// for concrete type propagation.
struct ApplyArgumentDescriptor {
  SILValue NewArg;
  CanType ConcreteType;
  ArchetypeType *OpenedArchetype;
  ApplyArgumentDescriptor() {}
  ApplyArgumentDescriptor(SILValue NewArg, CanType ConcreteType, 
         ArchetypeType *OpenedArchetype) : 
         NewArg(NewArg), ConcreteType(ConcreteType),
         OpenedArchetype(OpenedArchetype) {}
};

} // end namespace swift

#endif
