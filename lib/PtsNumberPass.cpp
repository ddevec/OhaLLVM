/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/lib/PtsNumberPass.h"

#include <string>
#include <vector>

using std::swap;

char PtsNumberPass::ID = 0;
PtsNumberPass::PtsNumberPass() : llvm::ModulePass(ID) { }

namespace llvm {
  static RegisterPass<PtsNumberPass>
      X("PtsNumberPass", "Generate identifiers for all pointers values, loads"
          " and stores in program", false, false);
}  // namespace llvm

void PtsNumberPass::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  // Because we're an AliasAnalysis
  // AliasAnalysis::getAnalysisUsage(usage);
  usage.setPreservesAll();
}

bool PtsNumberPass::runOnModule(llvm::Module &m) {
  ModInfo mod_info(m);
  extInfo_ = std14::make_unique<ExtLibInfo>(mod_info);
  extInfo_->init(m, vals_);

  // Now we populate the value map...
  // First, we create a value for each global
  for (auto it = m.global_begin(), en = m.global_end();
      it != en; ++it) {
    auto &glbl = *it;
    // Add a def for this global
    vals_.getDef(&glbl);
  }

  // Then we create a value for each function
  for (auto &fcn : m) {
    vals_.getDef(&fcn);

    for (auto &bb : fcn) {
      // Then, for each bb
      vals_.getDef(&fcn);
      // Finally, for appropriate instructions
      for (auto &inst : bb) {
        // Any pointer def by an inst
        // Store insts
        if (auto si = dyn_cast<llvm::StoreInst>(&inst)) {
          vals_.getDef(si);
        // Load inst
        } else if (auto li = dyn_cast<llvm::LoadInst>(&inst)) {
          vals_.getDef(li);
        // Call Insts
        } else if (auto ci = dyn_cast<llvm::CallInst>(&inst)) {
          vals_.getDef(ci);
        // Anything else returning a pointer
        } else {
          if (llvm::isa<llvm::PointerType>(inst.getType())) {
            vals_.getDef(&inst);
          }
        }

        // ?Any constant arg w/ a pointer type?
        // Check each operand of the inst for a pointer
        for (auto it = inst.op_begin(), en = inst.op_end();
            it != en; ++it) {
          auto &op = *it;
          if (llvm::isa<llvm::PointerType>(op->getType())) {
            vals_.getDef(op);
          }
        }
      }
    }
  }


  // We don't change code.  Ever.
  return false;
}
