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

static void error(const std::string &msg) {
  llvm::errs() << "ERROR: " << msg << "\n";
  print_stack_trace();
  assert(0);
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
  if (do_spec) {
    llvm::dbgs() << "ConstraintPass: do-spec is true!\n";
  } else {
    llvm::dbgs() << "ConstraintPass: no do-spec!\n";
  }

  const UnusedFunctions &unused_fcns =
      getAnalysis<UnusedFunctions>();

  ObjectMap::replaceDbgOmap(omap_);
  {
    util::PerfTimerPrinter id_timer(llvm::dbgs(), "Identify Objects");
    // Identify all of the objects in the source
    if (identifyObjects(omap_, m)) {
      error("Identify objects failure!");
    }
  }

  // Get the initial (top-level) constraints set
  // This should also track the def/use info
  // NOTE: This function will create a graph of all top-level variables,
  //   and a def/use mapping, but it will not fill in address-taken edges.
  //   Those will be populated later, by the actual points-to analysis using the
  //   constraints, as different analyses use the def use info differently
  {
    util::PerfTimerPrinter create_timer(llvm::dbgs(), "CreateConstraints");
    if (createConstraints(cg_, cfg_, omap_, m, unused_fcns, specAssumptions_)) {
      error("CreateConstraints failure!");
    }
  }

  // Need to now re-order constraints, with objects at bottom and values at
  //   top...
  {
    auto remap = omap_.lowerObjects();

    // Use the remapping to adjust the CG and CFG
    cg_.updateObjIDs(remap);
    cfg_.updateObjIDs(remap);
    specAssumptions_.updateObjIDs(remap);
  }

  // We don't change code.  Ever.
  return false;
}
