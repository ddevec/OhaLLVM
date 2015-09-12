/*
 * Copyright (C) 2015 David Devecsery
 */

#include "lib/UnusedFunctions.h"

#include "llvm/Support/Debug.h"

void UnusedFunctions::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<llvm::PathProfileInfo>();
}

bool UnusedFunctions::runOnModule(llvm::Module &m) {
  llvm::dbgs() << "In runOnModule!\n";

  auto &PI = getAnalysis<llvm::PathProfileInfo>();

  int used_fcns = 0;
  int unused_fcns = 0;

  for (auto &fcn : m) {
    if (fcn.hasExternalLinkage()) {
      continue;
    }
    PI.setCurrentFunction(&fcn);

    if (PI.pathsRun() == 0) {
      unused_fcns++;
      // llvm::dbgs() << "Found unused fcn: " << fcn.getName() << "!\n";
    } else {
      used_fcns++;
      visited.insert(&fcn);
    }
  }

  llvm::dbgs() << "num used_fcns: " << used_fcns << "\n";
  llvm::dbgs() << "num unused_fcns: " << unused_fcns << "\n";

  return false;
}

char UnusedFunctions::ID = 0;
static llvm::RegisterPass<UnusedFunctions> X("unused-functions",
    "Simple pass, analyses pathprofileinfo to determine which functions are"
    " unused",
    false, false);


