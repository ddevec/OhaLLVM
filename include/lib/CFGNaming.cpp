/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_CFGNAMING_H_
#define INCLUDE_CFGNAMING_H_

#include "include/Assumptions.h"
#include "include/ConstraintGraph.h"
#include "include/ControlFlowGraph.h"
#include "include/DUG.h"
#include "include/ExtInfo.h"
#include "include/ObjectMap.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"

#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

// Template class, used to define how FcnCFGInfo operates
class FcnCFGInfo {
 public:
  virtual llvm::Function *fcn() { return fcn_; }

  virtual std::vector<std::unique_ptr<FcnCFGInfo>> preds() = 0;
 
 protected:
  FcnCFGInfo(const llvm::Function *fcn) : fcn_(fcn) { }

  const llvm::Function *fcn_;
};

// Another which returns info for only realized callpaths
class FcnCFG : public llvm::ModulePass {
 public:
  static char ID;
  FcnCFG();

  virtual bool runOnModule(llvm::Module &M);

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  const char *getPassName() const override {
    return "FcnCFG";
  }

  // This gets tricky...
  std::vector<std::unique_ptr<FcnCFGInfo>>
  getInfo(const llvm::Function *fcn);

 private:
  SEG callGraph_;
  DynCallPaths *dynCalls_;
};

#endif  // INCLUDE_CFGNAMING_H_
