/*
 * Copyright (C) 2016 David Devecsery
 */

#ifndef INCLUDE_LIB_PTSNUMBERPASS_H_
#define INCLUDE_LIB_PTSNUMBERPASS_H_

#include "include/ExtInfo.h"
#include "include/ModInfo.h"
#include "include/ValueMap.h"

#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

// Number all:
//  Loads
//  Stores
//  Globals (and functions)
class PtsNumberPass : public llvm::ModulePass {
 public:
  typedef ValueMap::Id Id;
  static char ID;
  PtsNumberPass();

  virtual bool runOnModule(llvm::Module &M);

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  llvm::StringRef getPassName() const override {
    return "PtsNumberPass";
  }

  Id getId(const llvm::Value *val) const {
    auto ids = vals_.getIds(val);
    assert(ids.size() == 1);
    return *std::begin(ids);
  }

  const llvm::Value *getValue(Id id) const {
    return vals_.getValue(id);
  }

  const ExtLibInfo &extInfo() const {
    return *extInfo_;
  }

  const ValueMap &vals() const {
    return vals_;
  }

 private:
  ValueMap vals_;
  std::unique_ptr<ExtLibInfo> extInfo_;
};

#endif  // INCLUDE_LIB_PTSNUMBERPASS_H_
