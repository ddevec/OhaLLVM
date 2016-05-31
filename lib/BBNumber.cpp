/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/lib/BBNumber.h"

#include "include/util.h"
#include "include/lib/UnusedFunctions.h"

#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

char BBNumber::ID = 0;
BBNumber::BBNumber() : llvm::ModulePass(ID) { }

void BBNumber::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  usage.addRequired<UnusedFunctions>();
  usage.setPreservesAll();
}

bool BBNumber::runOnModule(llvm::Module &m) {
  auto &dyn_info = getAnalysis<UnusedFunctions>();
  // Populate mapping/revMapping from module
  foreach_used_bb(m, dyn_info,
      [this if_debug_enabled(, &dyn_info)] (const llvm::BasicBlock *bb) {
        assert(dyn_info.isUsed(bb));
        Id id(mapping_.size());
        mapping_.push_back(bb);
        revMapping_.emplace(bb, id);
        assert(mapping_.size()-1 == static_cast<size_t>(id));
      });

  // never ever modifies code
  return false;
}

namespace llvm {
static RegisterPass<BBNumber> dX("BBNumber",
    "Numbers the (used) BBs within the program",
    false, false);
}  // namespace llvm

