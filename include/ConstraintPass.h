/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_CONSTRAINTPASS_H_
#define INCLUDE_CONSTRAINTPASS_H_

#include "include/Assumptions.h"
#include "include/Cg.h"
#include "include/ExtInfo.h"
#include "include/ModInfo.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

class ConstraintPass : public llvm::ModulePass {
 public:
  static char ID;
  ConstraintPass();

  virtual bool runOnModule(llvm::Module &M);

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  llvm::StringRef getPassName() const override {
    return "ConstraintPass";
  }

  const Cg &getCG() const {
    return *mainCg_;
  }

  const CgCache &cgCache() const {
    return *cgCache_;
  }

  const CgCache &callCgCache() const {
    return *callCgCache_;
  }

  const AssumptionSet &getSpecAssumptions() const {
    return specAssumptions_;
  }

 private:
  Cg *mainCg_;
  std::unique_ptr<CgCache> cgCache_;
  std::unique_ptr<CgCache> callCgCache_;
  AssumptionSet specAssumptions_;

  std::unique_ptr<ExtLibInfo> extInfo_;
  std::unique_ptr<ModInfo> modInfo_;
};

#endif  // INCLUDE_CONSTRAINTPASS_H_
