/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LIB_UNUSEDFUNCTIONS_H__
#define INCLUDE_LIB_UNUSEDFUNCTIONS_H__

#include <set>

#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/PathProfileInfo.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"


class UnusedFunctions : public llvm::ModulePass {
 public:
    static char ID;

    UnusedFunctions() : llvm::ModulePass(ID) { }

    bool runOnModule(llvm::Module &m) override;

    void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

    bool isUsed(const llvm::Function &fcn) const {
      return isUsed(&fcn);
    }

    bool isUsed(const llvm::Function *fcn) const {
      if (allUsed_) {
        return true;
      }

      llvm::dbgs() << "Checkign for use: " << fcn->getName() << ": ";
      if (fcn->getName() == "main") {
        llvm::dbgs() << "true\n";
        return true;
      }
      // We're conservative for external functions, which we don't profile
      if (fcn->hasExternalLinkage()) {
        llvm::dbgs() << "true\n";
        return true;
      }
      bool ret =  visited_.find(fcn) != std::end(visited_);
      if (ret) {
        llvm::dbgs() << "true\n";
      } else {
        llvm::dbgs() << "false\n";
      }

      return ret;
    }

 private:
    std::set<const llvm::Function *> visited_;

    bool allUsed_ = false;
};

#endif  // INCLUDE_LIB_UNUSEDFUNCTIONS_H__
