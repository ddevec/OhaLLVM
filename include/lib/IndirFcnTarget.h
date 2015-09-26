/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LIB_INDIRFCNTARGET_H__
#define INCLUDE_LIB_INDIRFCNTARGET_H__

#include <vector>

#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/PathProfileInfo.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

class IndirFunctionInfo : public llvm::ModulePass {
 public:
    static char ID;

    IndirFunctionInfo() : llvm::ModulePass(ID) { }

    bool runOnModule(llvm::Module &m) override;

    void getAnalysisUsage(llvm::AnalysisUsage &) const override;

    bool hasInfo() const {
      return hasInfo_;
    }

    const std::vector<const llvm::Value *> &
    getTargets(const llvm::Value *val) const {
      return callToTarget_.at(val);
    }

 private:
    std::map<const llvm::Value *, std::vector<const llvm::Value *>>
      callToTarget_;

    bool hasInfo_;
};

#endif  // INCLUDE_LIB_INDIRFCNTARGET_H__
