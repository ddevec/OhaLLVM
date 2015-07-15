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

using namespace llvm; // NOLINT

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

  errs() << "BACKTRACE:\n";
  for (i = 0; i < size; i++) {
    errs() << "\t" << strings[i] << "\n";
  }

  free(strings);
}

static void error(const std::string &msg) {
  errs() << "ERROR: " << msg << "\n";
  print_stack_trace();
  assert(0);
}
/*}}}*/

// Constructor
char SpecSFS::ID = 0;
SpecSFS::SpecSFS() : ModulePass(ID) { }
static RegisterPass<SpecSFS>
X("SpecSFS", "Speculative Sparse Flow-sensitive Analysis", false, false);
// static RegisterAnalysisGroup<AliasAnalysis> Y(X);

// runOnModule, the primary pass
bool SpecSFS::runOnModule(Module &M) {
  // Set up our alias analysis
  // -- This is required for the llvm AliasAnalysis interface
  // InitializeAliasAnalysis(this);

  // Clear the def-use graph
  // It should already be cleared, but I'm paranoid
  DUG graph;
  ObjectMap omap;

  // Identify all of the objects in the source
  if (identifyObjects(omap, M)) {
    error("Identify objects failure!");
  }

  // Now that I've filled the omap, prep the graph w/ it
  graph.prepare(omap);

  // Get the initial (top-level) constraints set
  // This should also track the def/use info
  // NOTE: This function will create a graph of all top-level variables,
  //   and a def/use mapping, but it will not fill in address-taken edges.
  //   Those will be populated later, once we have AUX info available.
  if (createConstraints(graph, omap, M)) {
    error("CreateConstraints failure!");
  }

  graph.getConstraintGraph().printDotFile("graph.dot", omap);

  // Initial optimization pass
  // Runs HU on the graph as it stands, w/ only top level info filled in
  // Removes any nodes deemed to be non-ptr (definitely null), and merges nodes
  //   with statically equivalent ptsto sets
  if (optimizeConstraints(graph, omap)) {
    error("OptimizeConstraints failure!");
  }

  graph.getConstraintPEGraph().printDotFile("graphPE.dot", omap);


  // Get AUX info, in this instance we choose Andersens
  dout << "Running Andersens\n";
  Andersens aux;
  bool ret = aux.runOnModule(M);
  // Andersens had better not change M!
  dout << "Andersens done\n";
  assert(ret == false);

  // Now, fill in the indirect function calls
  if (addIndirectCalls(graph, aux, omap)) {
    error("AddIndirectCalls failure!");
  }

  // The PE graph was updated by addIndirectCalls
  graph.getConstraintPEGraph().printDotFile("graphPE_indr.dot", omap);
  // We can also get a non-PE version:
  // graph.getConstraintGraph().printDotFile("graph_indr.dot", omap);

  // Now, compute the SSA form for the top-level variables
  // We translate any PHI nodes into copy nodes... b/c the paper says so
  DUG::ControlFlowGraph ssa = computeSSA(graph.getCFG());

  // ssa.printDotFile("ssa.dot", omap);
#if 0
  // Now that we have the top level info, we fill in the address-taken
  // information
  if (fillAddressTaken(graph, aux)) {
    error("FillAddressTaken failure!");
  }

  // Compute partitions, based on address equivalence
  if (computePartitions(graph)) {
    error("ComputePartitions failure!");
  }

  // Compute SSA for each partition
  if (computePartSSA(graph)) {
    error("ComputePartSSA failure!");
  }

  // Finally, solve the graph
  if (solve(graph)) {
    error("Solve failure!");
  }

  // We do not modify code, ever!
#endif
  return false;
}

