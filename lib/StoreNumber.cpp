/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/lib/StoreNumber.h"

#include <unordered_map>
#include <vector>

#include "include/util.h"
#include "include/lib/UnusedFunctions.h"

#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"


char StoreNumber::ID = 0;
StoreNumber::StoreNumber() : llvm::ModulePass(ID) { }


void StoreNumber::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  usage.addRequired<UnusedFunctions>();
  usage.setPreservesAll();
}

bool StoreNumber::runOnModule(llvm::Module &m) {
  auto &dyn_info = getAnalysis<UnusedFunctions>();
  // Populate mapping/revMapping from module
  foreach_used_inst(m, dyn_info,
      [this] (const llvm::Instruction *inst) {
        if (auto si = dyn_cast<llvm::StoreInst>(inst)) {
          Id id(mapping_.size());
          mapping_.push_back(si);
          revMapping_.emplace(si, id);
        }
      });

  // never ever modifies code
  return false;
}

namespace llvm {
static RegisterPass<StoreNumber> eX("StoreNumber",
    "Numbers the (used) Stores within the program",
    false, false);
}  // namespace llvm


