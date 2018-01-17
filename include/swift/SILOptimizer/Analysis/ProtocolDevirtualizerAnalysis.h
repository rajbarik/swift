#ifndef SWIFT_SILOPTIMIZER_ANALYSIS_PROTOCOLDEVIRTUALIZER_H
#define SWIFT_SILOPTIMIZER_ANALYSIS_PROTOCOLDEVIRTUALIZER_H

#include "swift/SILOptimizer/Analysis/Analysis.h"
#include "swift/SIL/SILArgument.h"
#include "swift/SIL/SILValue.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/Debug.h"

namespace swift {

class SILModule;
class ClassDecl;
class ProtocolDecl;

class ProtocolDevirtualizerAnalysis : public SILAnalysis {
public:
  typedef llvm::DenseMap<ProtocolDecl *, ClassDecl *> ProtocolImplementations;

  ProtocolDevirtualizerAnalysis(SILModule *Mod)
      : SILAnalysis(AnalysisKind::ProtocolDevirtualizer), M(Mod) {
      init(); 
    }

  ~ProtocolDevirtualizerAnalysis();

  static bool classof(const SILAnalysis *S) {
    return S->getKind() == AnalysisKind::ProtocolDevirtualizer;
  }

  /// Invalidate all information in this analysis.
  virtual void invalidate() override { }

  /// Invalidate all of the information for a specific function.
  virtual void invalidate(SILFunction *F, InvalidationKind K) override { }

  /// Notify the analysis about a newly created function.
  virtual void notifyAddFunction(SILFunction *F) override { }

  /// Notify the analysis about a function which will be deleted from the
  /// module.
  virtual void notifyDeleteFunction(SILFunction *F) override { }

  /// Notify the analysis about changed witness or vtables.
  virtual void invalidateFunctionTables() override { }

  /// Get the sole class that implements a protocol.
  ClassDecl *getSoleClassImplementingProtocol(ProtocolDecl *P) {
    return ProtocolImplementationsCache[P];
  }

private:
  /// Compute inheritance properties.
  void init();

  /// The module.
  SILModule *M;

  /// A cache that maps a protocol to its sole class conforming to it.
  ProtocolImplementations ProtocolImplementationsCache;
};

}
#endif
