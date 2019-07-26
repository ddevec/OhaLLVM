/*
 * Copyright (C) 2019 David Devecsery
 */

#include "include/ModuleAAResults.h"

#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"

#include "include/SpecAnders.h"
#include "include/SpecAndersCS.h"

using AliasResult = llvm::AliasResult;

char ModuleAAResults::ID = 0;
ModuleAAResults::ModuleAAResults() : llvm::ModulePass(ID) { }

void ModuleAAResults::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  usage.setPreservesAll();
  usage.addUsedIfAvailable<SpecAndersWrapperPass>();
  usage.addUsedIfAvailable<SpecAndersCS>();
}

bool ModuleAAResults::runOnModule(llvm::Module &) {
  anders_ = getAnalysisIfAvailable<SpecAndersWrapperPass>();
  andersCS_ = getAnalysisIfAvailable<SpecAndersCS>();
  return false;
}

AliasResult ModuleAAResults::alias(const llvm::MemoryLocation &l1,
    const llvm::MemoryLocation &l2) {
  AliasResult ret = AliasResult::MayAlias;
  if (andersCS_) {
    ret = andersCS_->alias(l1, l2);
  } else if (anders_) {
    ret = anders_->getResult().alias(l1, l2);
  }
  return ret;
}

namespace llvm {
  static RegisterPass<ModuleAAResults>
      ModAARP("ModuleAAResults", "Wrapper for andersens AAs", false, true);
}


