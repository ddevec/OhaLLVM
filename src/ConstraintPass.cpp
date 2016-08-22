/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/ConstraintPass.h"

#include <set>
#include <string>
#include <vector>

using std::swap;

extern llvm::cl::opt<bool> no_spec;

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
  usage.addRequired<IndirFunctionInfo>();

  // Required for call info passes
  usage.addRequired<CsCFG>();
  usage.addRequired<CallContextLoader>();
}

bool ConstraintPass::runOnModule(llvm::Module &m) {
  modInfo_ = std14::make_unique<ModInfo>(m);
  extInfo_ = std14::make_unique<ExtLibInfo>(*modInfo_);

  auto &unused_fcns =
      getAnalysis<UnusedFunctions>();

  auto &indir_info =
      getAnalysis<IndirFunctionInfo>();

  auto &call_info =
      getAnalysis<CallContextLoader>();
  DynamicInfo dyn_info(unused_fcns, indir_info, call_info);

  auto &cs_cfg =
      getAnalysis<CsCFG>();

  BasicFcnCFG fcn_cfg(m, dyn_info);

  // Create a cg for each function in module
  // Then get the main cg
  // "merge sccs" with all the other functions cgs
  //   -- This will create one "unfiied" cg

  // Make constraint info for each function in the graph...
  // Then merge them all into one cg (combinging and linking together, like in
  //    sccs)
  // This is the Cg for the whole program...
  cgCache_ = std14::make_unique<CgCache>(m, dyn_info, fcn_cfg, *modInfo_,
      *extInfo_, specAssumptions_, cs_cfg);
  callCgCache_ = std14::make_unique<CgCache>(fcn_cfg);

  auto main = m.getFunction("main");
  mainCg_ = &cgCache_->getCg(main);

  llvm::dbgs() << "Pre global constraints\n";
  mainCg_->constraintStats();

  mainCg_->addGlobalConstraints(m);

  llvm::dbgs() << "Post global constraints\n";
  mainCg_->constraintStats();
  // Now merge the constraints for each function together...
  std::set<Cg *> visited;
  for (auto &fcn : m) {
    // Only evaluate used functions
    if (!dyn_info.used_info.isUsed(fcn) && !no_spec) {
      continue;
    }
    // Only consider functions with bodies..
    if (fcn.isDeclaration()) {
      continue;
    }
    if (fcn.getName() == "main") {
      continue;
    }
    auto &cur_cg = cgCache_->getCg(&fcn);
    llvm::dbgs() << "Visiting: " << fcn.getName() << "\n";
    auto rc = visited.emplace(&cur_cg);
    if (rc.second) {
      llvm::dbgs() << "merging: " << fcn.getName() << "\n";
      mainCg_->mergeCg(cur_cg);
    }
  }

  llvm::dbgs() << "Pre resolveCalls constraints\n";
  mainCg_->constraintStats();

  // Resolve any additional calls -- note that since our mainCg_ now defines all
  // functions, they will all be resolved w/ internal edges (without context
  //   sensitivity)
  mainCg_->resolveCalls(*cgCache_, *callCgCache_);

  llvm::dbgs() << "Post resolveCalls constraints\n";
  mainCg_->constraintStats();

  // We don't change code.  Ever.
  return false;
}
