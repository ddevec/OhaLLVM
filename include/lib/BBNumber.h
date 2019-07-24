/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LIB_BBNUMBER_H_
#define INCLUDE_LIB_BBNUMBER_H_

#include <unordered_map>
#include <vector>

#include "include/util.h"
#include "include/lib/UnusedFunctions.h"

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

// Numbers all basic blocks in the module
class BBNumber : public llvm::ModulePass {
 private:
  class id_tag { };

 public:
  typedef util::ID<id_tag, int32_t, -1> Id;

  static char ID;
  BBNumber();

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  virtual bool runOnModule(llvm::Module &m);

  llvm::StringRef getPassName() const override {
    return "BBNumber";
  }

  Id getId(const llvm::BasicBlock *bb) const {
    auto ret_id = revMapping_.at(bb);
    assert(static_cast<size_t>(ret_id) < mapping_.size());
    return ret_id;
  }

  const llvm::BasicBlock *getBB(Id id) const {
    assert(static_cast<size_t>(id) < mapping_.size());
    return mapping_[static_cast<size_t>(id)];
  }

  size_t numBBs() const {
    return mapping_.size();
  }

 private:
  std::vector<const llvm::BasicBlock *> mapping_;
  std::unordered_map<const llvm::BasicBlock *, Id> revMapping_;
};

#endif  // INCLUDE_LIB_BBNUMBER_H_
