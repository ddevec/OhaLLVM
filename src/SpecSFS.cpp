/*
 * Copyright (C) 2015 David Devecsery
 */


// Enable debugging prints for this file
#define SPECSFS_DEBUG

#include "include/SpecSFS.h"

#include <execinfo.h>

#include <algorithm>
#include <string>
#include <utility>
#include <vector>

#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/Analysis/AliasAnalysis.h"


#include "include/Andersens.h"
#include "include/Debug.h"
#include "include/ObjectMap.h"
#include "include/lib/UnusedFunctions.h"

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

void SpecSFS::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  usage.setPreservesAll();
  usage.addRequired<UnusedFunctions>();
  usage.addRequired<AliasAnalysis>();
}

// runOnModule, the primary pass
bool SpecSFS::runOnModule(llvm::Module &M) {
  // Set up our alias analysis
  // -- This is required for the llvm AliasAnalysis interface
  InitializeAliasAnalysis(this);

  // Clear the def-use graph
  // It should already be cleared, but I'm paranoid
  ConstraintGraph cg;
  CFG cfg;
  ObjectMap &omap = omap_;

  const UnusedFunctions &unused_fcns =
      getAnalysis<UnusedFunctions>();

  // Identify all of the objects in the source
  if (identifyObjects(omap, M)) {
    error("Identify objects failure!");
  }

  // Get the initial (top-level) constraints set
  // This should also track the def/use info
  // NOTE: This function will create a graph of all top-level variables,
  //   and a def/use mapping, but it will not fill in address-taken edges.
  //   Those will be populated later, once we have AUX info available.
  if (createConstraints(cg, cfg, omap, M, unused_fcns)) {
    error("CreateConstraints failure!");
  }

  // Initial optimization pass
  // Runs HU on the graph as it stands, w/ only top level info filled in
  // Removes any nodes deemed to be non-ptr (definitely null), and merges nodes
  //   with statically equivalent ptsto sets
  /* FIXME: -- ddevec -- Skipping for now to help debug
  if (optimizeConstraints(cg, cfg, omap)) {
    error("OptimizeConstraints failure!");
  }
  */

  if_debug(cfg.getSEG().printDotFile("CFG.dot", omap));

  // Get AUX info, in this instance we choose Andersens
  dout("Running Andersens\n");
  Andersens aux;
  if (aux.runOnModule(M)) {
    // Andersens had better not change M!
    error("Andersens changes M???");
  }
  dout("Andersens done\n");

  // Now, fill in the indirect function calls
  if (addIndirectCalls(cg, cfg, aux, omap)) {
    error("AddIndirectCalls failure!");
  }

  // Now that we've resolve our indir edges, we can remove duplicate constraints
  // (possibly created by optimizeConstraints())
  cg.unique();

  // The PE graph was updated by addIndirectCalls

  if_debug(cfg.getSEG().printDotFile("CFG_indir.dot", omap));

  // Now, compute the SSA form for the top-level variables
  // We translate any PHI nodes into copy nodes... b/c the paper says so
  CFG::ControlFlowGraph ssa = computeSSA(cfg.getSEG());

  if_debug(ssa.printDotFile("CFG_ssa.dot", omap));

  cfg.setSEG(std::move(ssa));

  // Compute partitions, based on address equivalence
  DUG graph;

  graph.fillTopLevel(cg, omap);

  if (computePartitions(graph, cfg, aux, omap)) {
    error("ComputePartitions failure!");
  }

  // Compute SSA for each partition
  if (addPartitionsToDUG(graph, cfg, omap)) {
    error("ComputePartSSA failure!");
  }

  // Finally, solve the graph
  if (solve(graph, omap)) {
    error("Solve failure!");
  }

#ifndef SPECSFS_NODEBUG
  // STATS!
  int64_t total_variables = 0;
  int64_t total_ptstos = 0;

  int32_t num_objects[10] = {};

  size_t max_objects = 0;
  int32_t num_max = 0;

  llvm::dbgs() << "Printing final ptsto set for top level variables:\n";
  std::for_each(pts_top_.cbegin(), pts_top_.cend(),
      [&omap, &total_variables, &total_ptstos, &max_objects, &num_objects,
        &num_max]
      (const std::pair<const ObjectMap::ObjID, std::vector<PtstoSet>> &pr) {
    auto top_val = omap.valueAtID(pr.first);

    if (top_val == nullptr) {
      llvm::dbgs() << "Value is (id): " << pr.first << "\n";
    } else if (auto gv = llvm::dyn_cast<llvm::GlobalValue>(top_val)) {
      llvm::dbgs() << "Value (" << pr.first << ") is: " <<
          gv->getName() << "\n";
    } else if (auto fcn = llvm::dyn_cast<llvm::Function>(top_val)) {
      llvm::dbgs() << "Value (" << pr.first <<") is: " <<
          fcn->getName() << "\n";
    } else {
      llvm::dbgs() << "Value (" << pr.first << ") is: " << *top_val << "\n";
    }

    for (uint32_t i = 0; i < pr.second.size(); i++) {
      llvm::dbgs() << "  Offset: " << i << "\n";

      // Statistics
      auto &ptsto = pr.second[i];
      size_t ptsto_size = ptsto.size();

      total_variables++;
      total_ptstos += ptsto_size;

      if (ptsto_size < 10) {
        num_objects[ptsto_size]++;
      }

      if (ptsto_size > max_objects) {
        max_objects = ptsto_size;
        num_max = 0;
      }

      if (ptsto_size == max_objects) {
        num_max++;
      }

      // Printing
      std::for_each(ptsto.cbegin(), ptsto.cend(),
          [&omap] (const ObjectMap::ObjID obj_id) {
        auto loc_val = omap.valueAtID(obj_id);

        if (loc_val == nullptr) {
          llvm::dbgs() << "    Value is (id): " << obj_id << "\n";
        } else if (auto gv = llvm::dyn_cast<llvm::GlobalValue>(loc_val)) {
          llvm::dbgs() << "    " << obj_id << ": " << gv->getName() << "\n";
        } else if (auto fcn = llvm::dyn_cast<llvm::Function>(loc_val)) {
          llvm::dbgs() << "    " << obj_id << ": " << fcn->getName() << "\n";
        } else {
          llvm::dbgs() << "    " << obj_id << ": " << *loc_val << "\n";
        }
      });
    }
  });

  llvm::dbgs() << "Number tracked values: " << total_variables << "\n";
  llvm::dbgs() << "Number tracked ptstos: " << total_ptstos << "\n";

  llvm::dbgs() << "Max ptsto is: " << max_objects << ", with num_max: " <<
    num_max << "\n";

  llvm::dbgs() << "lowest ptsto counts:\n";
  for (int i = 0; i < 10; i++) {
    llvm::dbgs() << "  [" << i << "]:  " << num_objects[i] << "\n";
  }
#endif

  // We do not modify code, ever!
  return false;
}

llvm::AliasAnalysis::AliasResult SpecSFS::alias(const Location &L1,
                                            const Location &L2) {
  auto &pts1 = pts_top_.at(omap_.getValue(L1.Ptr));
  auto &pts2 = pts_top_.at(omap_.getValue(L2.Ptr));

  // Check to see if the two pointers are known to not alias.  They don't alias
  // if their points-to sets do not intersect.
  if (!pts1.insersectsIgnoring(pts2, ObjectMap::NullObjectValue)) {
    return NoAlias;
  }

  // ddevec - FIXME: Changed this because we can't call "alisas" from a non
  //   "alias analysis"
  return AliasAnalysis::alias(L1, L2);
}


