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
      if (fcn->getName() == "main") {
        return true;
      }
      // We're conservative for external functions, which we don't profile
      if (fcn->hasExternalLinkage()) {
        return true;
      }
      return visited.find(fcn) != std::end(visited);
    }

 private:
    std::set<const llvm::Function *> visited;
};

#endif  // INCLUDE_LIB_UNUSEDFUNCTIONS_H__
