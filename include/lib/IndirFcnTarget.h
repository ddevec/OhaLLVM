/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LIB_INDIRFCNTARGET_H__
#define INCLUDE_LIB_INDIRFCNTARGET_H__

#include <vector>

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

class IndirFunctionInfo : public llvm::ModulePass {
 public:
    static char ID;

    IndirFunctionInfo() : llvm::ModulePass(ID) { }

    bool runOnModule(llvm::Module &m) override;

    void getAnalysisUsage(llvm::AnalysisUsage &) const override;

    bool hasInfo() const {
      return hasInfo_ && enabled_;
    }

    const std::vector<const llvm::Value *> &
    getTargets(const llvm::Value *val) const {
      auto it = callToTarget_.find(val);
      if (it == std::end(callToTarget_)) {
        static std::vector<const llvm::Value *> empty_vec;
        return empty_vec;
      }
      return it->second;
    }

    size_t numInvariants() const {
      size_t ret = 0;

      for (auto &pr : callToTarget_) {
        ret += pr.second.size();
      }

      return ret;
    }

    void disable() {
      enabled_ = false;
    }

    void enable() {
      enabled_ = true;
    }

 private:
    std::map<const llvm::Value *, std::vector<const llvm::Value *>>
      callToTarget_;

    bool hasInfo_;
    bool enabled_ = true;
};

#endif  // INCLUDE_LIB_INDIRFCNTARGET_H__
