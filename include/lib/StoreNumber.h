/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LIB_STORENUMBER_H_
#define INCLUDE_LIB_STORENUMBER_H_

#include <unordered_map>
#include <vector>

#include "include/util.h"
#include "include/lib/UnusedFunctions.h"

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

// Numbers all basic blocks in the module
class StoreNumber : public llvm::ModulePass {
 private:
  class id_tag { };

 public:
  typedef util::ID<id_tag, int32_t, -1> Id;

  static char ID;
  StoreNumber();

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  virtual bool runOnModule(llvm::Module &m);

  llvm::StringRef getPassName() const override {
    return "InstNumber";
  }

  Id getId(const llvm::StoreInst *inst) const {
    return revMapping_.at(inst);
  }

  const llvm::StoreInst *getInst(Id id) const {
    return mapping_[static_cast<size_t>(id)];
  }

  size_t numStores() const {
    return mapping_.size();
  }

 private:
  std::vector<const llvm::StoreInst *> mapping_;
  std::unordered_map<const llvm::StoreInst *, Id> revMapping_;
};

#endif  // INCLUDE_LIB_STORENUMBER_H_
