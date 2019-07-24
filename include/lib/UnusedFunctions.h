/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LIB_UNUSEDFUNCTIONS_H__
#define INCLUDE_LIB_UNUSEDFUNCTIONS_H__

#include <set>
#include <unordered_set>

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"


class UnusedFunctions : public llvm::ModulePass {
 public:
    static char ID;

    UnusedFunctions();

    bool runOnModule(llvm::Module &m) override;

    void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

    bool hasInfo() const {
      return !allUsed_;
    }

    bool isUsed(const llvm::Function &fcn) const {
      return isUsed(&fcn);
    }

    bool isUsed(const llvm::Function *fcn) const {
      if (ignoreUnused_ || !enabled_) {
        return true;
      }

      return isReallyUsed(fcn);
    }

    bool isReallyUsed(const llvm::Function &fcn) const {
      return isReallyUsed(&fcn);
    }

    bool isReallyUsed(const llvm::Function *fcn) const {
      if (allUsed_) {
        return true;
      }

      // llvm::dbgs() << "Checking for use: " << fcn->getName() << ": ";
      if (fcn->getName() == "main") {
        // llvm::dbgs() << "true\n";
        return true;
      }
      // We're conservative for external functions, which we don't profile
      if (fcn->isDeclaration()) {
        // llvm::dbgs() << "true\n";
        return true;
      }
      bool ret =  visited_.find(fcn) != std::end(visited_);
      if (ret) {
        // llvm::dbgs() << "true\n";
      } else {
        // llvm::dbgs() << "false\n";
      }

      return ret;
    }

    bool isUsed(const llvm::BasicBlock &bb) const {
      return isUsed(&bb);
    }

    bool isUsed(const llvm::BasicBlock *bb) const {
      if (ignoreUnused_ || !enabled_) {
        return true;
      }

      return isReallyUsed(bb);
    }

    bool isReallyUsed(const llvm::BasicBlock &bb) const {
      return isReallyUsed(&bb);
    }

    bool isReallyUsed(const llvm::BasicBlock *bb) const {
      if (allUsed_) {
        return true;
      }

      // llvm::dbgs() << "Checking for BB use: " << bb->getName() << ": ";

      bool ret =  visitedBB_.find(bb) != std::end(visitedBB_);

      if (ret) {
        // llvm::dbgs() << "true\n";
      } else {
        // llvm::dbgs() << "false\n";
      }

      return ret;
    }

    size_t numInvariants() const {
      return visitedBB_.size();
    }

    void disable() {
      enabled_ = false;
    }

    void enable() {
      enabled_ = true;
    }

 private:
    std::unordered_set<const llvm::Function *> visited_;
    std::unordered_set<const llvm::BasicBlock *>visitedBB_;

    bool enabled_ = true;
    bool allUsed_ = false;
    const bool ignoreUnused_;
};

template <typename visit>
void foreach_used_fcn(llvm::Module &m, const UnusedFunctions &dyn_info,
    visit visit_fcn) {
  for (auto &fcn : m) {
    if (!dyn_info.isUsed(fcn)) {
      continue;
    }

    visit_fcn(&fcn);
  }
}

template <typename visit>
void foreach_used_bb(llvm::Module &m, const UnusedFunctions &dyn_info,
    visit visit_fcn) {
  foreach_used_fcn(m, dyn_info,
    [&visit_fcn, &dyn_info](auto pfcn) {
      for (auto &bb : *pfcn) {
        if (!dyn_info.isUsed(bb)) {
          continue;
        }

        visit_fcn(&bb);
      }
    });
}

template <typename visit>
void foreach_used_inst(llvm::Module &m, const UnusedFunctions &dyn_info,
    visit visit_fcn) {
  foreach_used_bb(m, dyn_info,
      [&visit_fcn](auto pbb) {
        for (auto &inst : *pbb) {
          visit_fcn(&inst);
        }
      });
}

#endif  // INCLUDE_LIB_UNUSEDFUNCTIONS_H__
