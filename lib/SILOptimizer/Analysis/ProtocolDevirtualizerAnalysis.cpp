//===--- ProtocolDevirtualizerAnalysis.cpp - Protocol to Class inheritance ------------===//
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

#include "swift/SILOptimizer/Analysis/ProtocolDevirtualizerAnalysis.h"
#include "swift/SILOptimizer/Analysis/ClassHierarchyAnalysis.h"
#include "swift/AST/ASTContext.h"
#include "swift/AST/ASTWalker.h"
#include "swift/AST/Module.h"
#include "swift/SIL/SILInstruction.h"
#include "swift/SIL/SILValue.h"
#include "swift/SIL/SILModule.h"

using namespace swift;

void ProtocolDevirtualizerAnalysis::init() {

  /// Get the class hierarchy.
  ClassHierarchyAnalysis *CHA = llvm::dyn_cast<ClassHierarchyAnalysis>(createClassHierarchyAnalysis(M));

  SmallVector<Decl *, 32> Decls;

  /// Get all top level Decls.
  M->getSwiftModule()->getTopLevelDecls(Decls);

  for (auto *D: Decls) {
    auto ProtoDecl = dyn_cast<ProtocolDecl>(D);
    /// Check for protocols that are either internal or lowe  with whole module compilation enabled
    /// or file private or lower.
    if (ProtoDecl && ProtoDecl->hasAccess() && 
        CHA->hasKnownImplementations(ProtoDecl) &&
        ((M->isWholeModule() && ProtoDecl->getEffectiveAccess() <= AccessLevel::Internal) ||
          (ProtoDecl->getEffectiveAccess() <= AccessLevel::FilePrivate))
        ) {
  
      /// Make sure one class implements this protocol.
      SmallVector<NominalTypeDecl *, 8> ImplementedClassOrProtocolList = CHA->getProtocolImplementations(ProtoDecl);
      if (ImplementedClassOrProtocolList.size() == 1) {
        /// Make sure it is a class declaration that implements this protocol.
        /// Check if the class has no subclasses: direct or indirect.
        auto CD = dyn_cast<ClassDecl>(*(ImplementedClassOrProtocolList.begin()));
        if (CD && (CD->getEffectiveAccess() <= AccessLevel::Internal) && 
            (!CHA->hasKnownDirectSubclasses(CD)) && (!CHA->hasKnownIndirectSubclasses(CD))) {
            ProtocolImplementationsCache[ProtoDecl] = CD;
        }
      }
    }
  }
}

ProtocolDevirtualizerAnalysis::~ProtocolDevirtualizerAnalysis() {}
