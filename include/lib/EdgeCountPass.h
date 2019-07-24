/*
 * Copyright (C) 2016 David Devecsery
 */

#ifndef INCLUDE_LIB_EDGECOUNTPASS_H_
#define INCLUDE_LIB_EDGECOUNTPASS_H_

#include <algorithm>
#include <iterator>
#include <unordered_map>
#include <vector>

#include "include/util.h"

#include "llvm/Pass.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

class DynEdgeLoader : public llvm::ModulePass {
 public:
  static char ID;
  DynEdgeLoader();

  virtual bool runOnModule(llvm::Module &m);

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  llvm::StringRef getPassName() const override {
    return "DynEdgeLoader";
  }

  bool hasDynData() const {
    return loaded_;
  }

  bool getExecutionCount(const llvm::Function *fcn) const {
    return getExecutionCount(&fcn->getEntryBlock());
  }

  bool getExecutionCount(const llvm::BasicBlock *bb) const {
    return executionCounts_.at(bb);
  }

 private:
  bool loaded_ = false;

  std::unordered_map<const llvm::BasicBlock *, size_t> executionCounts_;
};

#endif  // INCLUDE_LIB_EDGECOUNTPASS_H_
