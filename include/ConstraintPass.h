/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_CONSTRAINTPASS_H_
#define INCLUDE_CONSTRAINTPASS_H_

#include "include/Assumptions.h"
#include "include/ConstraintGraph.h"
#include "include/ControlFlowGraph.h"
#include "include/DUG.h"
#include "include/ExtInfo.h"
#include "include/ObjectMap.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"

#include "llvm/Function.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

extern llvm::cl::opt<bool> do_spec;

class ConstraintPass : public llvm::ModulePass {
 public:
  static char ID;
  ConstraintPass();

  virtual bool runOnModule(llvm::Module &M);

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  const char *getPassName() const override {
    return "ConstraintPass";
  }

  const ObjectMap &getObjectMap() const {
    return omap_;
  }

  const ExtLibInfo *getLibInfo() const {
    return &extInfo_;
  }

  const ConstraintGraph &getConstraintGraph() const {
    return cg_;
  }

  const CFG &getControlFlowGraph() const {
    return cfg_;
  }

  const AssumptionSet &getSpecAssumptions() const {
    return specAssumptions_;
  }

 private:
  ObjectMap omap_;
  ConstraintGraph cg_;
  CFG cfg_;
  AssumptionSet specAssumptions_;

  ExtLibInfo extInfo_;

  // Identifies all objects in the module, adds them to graph
  bool identifyObjects(ObjectMap &omap, const llvm::Module &M);

  // Creates constraints for each top-lvel operatioon in the module
  // Also populates Def/Use info for later address-taken constraints
  bool createConstraints(ConstraintGraph &cg, CFG &cfg, ObjectMap &omap,
      const llvm::Module &M, const UnusedFunctions &unused,
      AssumptionSet &as);
};

#endif  // INCLUDE_CONSTRAINTPASS_H_
