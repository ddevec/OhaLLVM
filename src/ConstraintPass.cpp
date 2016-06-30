/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/ConstraintPass.h"

#include <string>
#include <vector>

using std::swap;

llvm::cl::opt<bool>
  do_spec("specsfs-do-spec", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc("Determines if specsfs should include speculative dynamic "
        "runtime information"));

// Error handling functions {{{
// Don't warn about this (if it is an) unused function... I'm being sloppy
[[ gnu::unused ]]
static void print_stack_trace(void) {
  void *array[10];
  size_t size;
  char **strings;
  size_t i;

  size = backtrace(array, 10);
  strings = backtrace_symbols(array, size);

  llvm::errs() << "BACKTRACE:\n";
  for (i = 0; i < size; i++) {
    llvm::errs() << "\t" << strings[i] << "\n";
  }

  free(strings);
}

//}}}

char ConstraintPass::ID = 0;
ConstraintPass::ConstraintPass() : llvm::ModulePass(ID) { }

namespace llvm {
  static RegisterPass<ConstraintPass>
      X("ConstraintPass", "Generate Constraints for use by inclusion based "
          "points-to analysis", false, false);
}  // namespace llvm

void ConstraintPass::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  // Because we're an AliasAnalysis
  // AliasAnalysis::getAnalysisUsage(usage);
  usage.setPreservesAll();

  // For DCE
  usage.addRequired<UnusedFunctions>();

  // For indirect function following
  // usage.addRequired<IndirFunctionInfo>();
}

bool ConstraintPass::runOnModule(llvm::Module &m) {
  ModInfo mod_info(m);
  extInfo_ = std14::make_unique<ExtLibInfo>(mod_info);

  const UnusedFunctions &unused_fcns =
      getAnalysis<UnusedFunctions>();
  DynamicInfo dyn_info(unused_fcns);

  BasicFcnCFG fcn_cfg(m, dyn_info);

  // Create a cg for each function in module
  // Then get the main cg
  // "merge sccs" with all the other functions cgs
  //   -- This will create one "unfiied" cg

  // Make constraint info for each function in the graph...
  // Then merge them all into one cg (combinging and linking together, like in
  //    sccs)
  // This is the Cg for the whole program...
  cgCache_ = std14::make_unique<CgCache>(m, dyn_info, fcn_cfg, mod_info,
      *extInfo_, specAssumptions_);

  auto main = m.getFunction("main");
  mainCg_ = &cgCache_->getCg(main);

  mainCg_->addGlobalConstraints(m);
  // Now merge the constraints for each function together...
  for (auto &fcn : m) {
    // Only consider functions with bodies..
    if (fcn.isDeclaration()) {
      continue;
    }
    if (fcn.getName() == "main") {
      continue;
    }
    auto &cur_cg = cgCache_->getCg(&fcn);
    mainCg_->mergeCg(cur_cg);
  }

  // We don't change code.  Ever.
  return false;
}
