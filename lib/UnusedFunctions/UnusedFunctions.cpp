/*
 * Copyright (C) 2015 David Devecsery
 */

#include "lib/UnusedFunctions.h"

#include "llvm/Support/Debug.h"
#include "llvm/Analysis/ProfileInfo.h"
#include "llvm/Function.h"

void UnusedFunctions::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<llvm::ProfileInfo>();
}

bool UnusedFunctions::runOnModule(llvm::Module &m) {
  // llvm::dbgs() << "In runOnModule!\n";

  auto &PI = getAnalysis<llvm::ProfileInfo>();

  int used_fcns = 0;
  int unused_fcns = 0;

  int used_bbs = 0;
  int unused_bbs = 0;

  // Check for unused functions
  for (auto &fcn : m) {
    // llvm::dbgs() << "Iterating fcn: " << fcn.getName() << "\n";
    if (fcn.isDeclaration()) {
      continue;
    }

    auto execution_count = PI.getExecutionCount(&fcn);
    // llvm::dbgs() << "  ExecutionCount is: " << execution_count << "\n";

    if (execution_count < 1) {
      unused_fcns++;
      // llvm::dbgs() << "Found unused fcn: " << fcn.getName() << "!\n";
    } else {
      used_fcns++;
      visited_.insert(&fcn);
    }
  }

  // Check for unused Basic Blocks
  for (auto &fcn : m) {
    for (auto &bb : fcn) {
      // llvm::dbgs() << "Scanning bb: " << bb.getName() << "\n";
      if (PI.getExecutionCount(&bb) < 1) {
        // llvm::dbgs() << "  Unused\n";
        unused_bbs++;
      } else {
        visitedBB_.insert(&bb);
        // llvm::dbgs() << "  Used\n";
        used_bbs++;
      }
    }
  }

  // llvm::dbgs() << "num used_fcns: " << used_fcns << "\n";
  // llvm::dbgs() << "num unused_fcns: " << unused_fcns << "\n";

  // llvm::dbgs() << "num used_bbs: " << used_bbs << "\n";
  // llvm::dbgs() << "num unused_bbs: " << unused_bbs << "\n";


  if (used_fcns == 0) {
    llvm::dbgs() << "UnusedFunctions: No logfile found\n";
    allUsed_ = true;
  } else {
    llvm::dbgs() << "UnusedFunctions: Successfully Loaded\n";
    allUsed_ = false;
  }

  return false;
}

char UnusedFunctions::ID = 0;
static llvm::RegisterPass<UnusedFunctions> X("unused-functions",
    "Simple pass, analyses pathprofileinfo to determine which functions are"
    " unused",
    false, false);


