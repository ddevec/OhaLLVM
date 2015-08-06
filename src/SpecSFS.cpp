/*
 * Copyright (C) 2015 David Devecsery
 */


// Enable debugging prints for this file
#define SPECSFS_DEBUG

#include "include/SpecSFS.h"

#include <execinfo.h>

#include <algorithm>
#include <string>

#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

#include "include/Debug.h"
#include "include/Andersens.h"
#include "include/ObjectMap.h"

using std::swap;

// Error handling functions
/*{{{*/
// Don't warn about this (if it is an) unused function... I'm being sloppy
__attribute__((unused))
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
/*}}}*/

// Constructor
char SpecSFS::ID = 0;
SpecSFS::SpecSFS() : ModulePass(ID) { }
static llvm::RegisterPass<SpecSFS>
X("SpecSFS", "Speculative Sparse Flow-sensitive Analysis", false, false);
// static RegisterAnalysisGroup<AliasAnalysis> Y(X);

// runOnModule, the primary pass
bool SpecSFS::runOnModule(llvm::Module &M) {
  // Set up our alias analysis
  // -- This is required for the llvm AliasAnalysis interface
  // InitializeAliasAnalysis(this);

  // Clear the def-use graph
  // It should already be cleared, but I'm paranoid
  ConstraintGraph cg;
  CFG cfg;
  ObjectMap &omap = omap_;

  // Identify all of the objects in the source
  if (identifyObjects(omap, M)) {
    error("Identify objects failure!");
  }

  // Get the initial (top-level) constraints set
  // This should also track the def/use info
  // NOTE: This function will create a graph of all top-level variables,
  //   and a def/use mapping, but it will not fill in address-taken edges.
  //   Those will be populated later, once we have AUX info available.
  if (createConstraints(cg, cfg, omap, M)) {
    error("CreateConstraints failure!");
  }

  cg.getSEG().printDotFile("top.dot", omap);

  // Initial optimization pass
  // Runs HU on the graph as it stands, w/ only top level info filled in
  // Removes any nodes deemed to be non-ptr (definitely null), and merges nodes
  //   with statically equivalent ptsto sets
  if (optimizeConstraints(cg, omap)) {
    error("OptimizeConstraints failure!");
  }

  cg.getSEG().printDotFile("top_HU.dot", omap);

  cfg.getSEG().printDotFile("CFG.dot", omap);

  // Get AUX info, in this instance we choose Andersens
  dout << "Running Andersens\n";
  Andersens aux;
  bool ret = aux.runOnModule(M);
  // Andersens had better not change M!
  dout << "Andersens done\n";
  assert(ret == false);

  // Now, fill in the indirect function calls
  if (addIndirectCalls(cg, cfg, aux, omap)) {
    error("AddIndirectCalls failure!");
  }

  // The PE graph was updated by addIndirectCalls
  cg.getSEG().printDotFile("top_indir.dot", omap);

  cfg.getSEG().printDotFile("CFG_indir.dot", omap);

  // Now, compute the SSA form for the top-level variables
  // We translate any PHI nodes into copy nodes... b/c the paper says so
  CFG::ControlFlowGraph ssa = computeSSA(cfg.getSEG());

  ssa.printDotFile("CFG_ssa.dot", omap);

  cfg.setSEG(std::move(ssa));

  // Compute partitions, based on address equivalence
  DUG graph;

  graph.fillTopLevel(cg);

  if (computePartitions(graph, cfg, aux, omap)) {
    error("ComputePartitions failure!");
  }

  // Compute SSA for each partition
  if (addPartitionsToDUG(graph, cfg)) {
    error("ComputePartSSA failure!");
  }

  // Finally, solve the graph
  if (solve(graph)) {
    error("Solve failure!");
  }

  // We do not modify code, ever!
  return false;
}

