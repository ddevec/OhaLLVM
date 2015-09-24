/*
 * Copyright (C) 2015 David Devecsery
 */


// Enable debugging prints for this file
// #define SPECSFS_DEBUG
#define SPECSFS_LOGDEBUG

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

  {
    PerfTimerPrinter id_timer(llvm::dbgs(), "Identify Objects");
    // Identify all of the objects in the source
    if (identifyObjects(omap, M)) {
      error("Identify objects failure!");
    }
  }

  // Get the initial (top-level) constraints set
  // This should also track the def/use info
  // NOTE: This function will create a graph of all top-level variables,
  //   and a def/use mapping, but it will not fill in address-taken edges.
  //   Those will be populated later, once we have AUX info available.
  {
    PerfTimerPrinter create_timer(llvm::dbgs(), "CreateConstraints");
    if (createConstraints(cg, cfg, omap, M, unused_fcns)) {
      error("CreateConstraints failure!");
    }
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

  cfg.cleanup();

  Andersens aux;
  // Get AUX info, in this instance we choose Andersens
  {
    PerfTimerPrinter andersens_timer(llvm::dbgs(), "Andersens");
    if (aux.runOnModule(M)) {
      // Andersens had better not change M!
      error("Andersens changes M???");
    }
  }

  {
    // Converting from aux_id to obj_ids
    // For each pointer value we care about:
    dout("Filling aux_to_obj:\n");
    auto &aux_val_nodes = aux.getObjectMap();

    special_aux_.emplace(ObjectMap::NullValue, Andersens::NullPtr);
    special_aux_.emplace(ObjectMap::NullObjectValue, Andersens::NullObject);
    special_aux_.emplace(ObjectMap::ArgvValue, Andersens::ArgvValue);
    special_aux_.emplace(ObjectMap::ArgvObjectValue, Andersens::ArgvObject);
    special_aux_.emplace(ObjectMap::IntValue, aux.IntNode);
    special_aux_.emplace(ObjectMap::UniversalValue, Andersens::UniversalSet);
    special_aux_.emplace(ObjectMap::LocaleObject, Andersens::LocaleObject);
    special_aux_.emplace(ObjectMap::CTypeObject, Andersens::CTypeObject);
    special_aux_.emplace(ObjectMap::ErrnoObject, Andersens::ErrnoObject);
    special_aux_.emplace(ObjectMap::PthreadSpecificValue,
        aux.PthreadSpecificNode);

    aux_to_obj_.emplace(Andersens::NullPtr, ObjectMap::NullValue);
    aux_to_obj_.emplace(Andersens::NullObject, ObjectMap::NullObjectValue);
    aux_to_obj_.emplace(Andersens::ArgvValue, ObjectMap::ArgvValue);
    aux_to_obj_.emplace(Andersens::ArgvObject, ObjectMap::ArgvObjectValue);
    aux_to_obj_.emplace(aux.IntNode, ObjectMap::IntValue);
    aux_to_obj_.emplace(Andersens::UniversalSet, ObjectMap::UniversalValue);
    aux_to_obj_.emplace(Andersens::LocaleObject, ObjectMap::LocaleObject);
    aux_to_obj_.emplace(Andersens::CTypeObject, ObjectMap::CTypeObject);
    aux_to_obj_.emplace(Andersens::ErrnoObject, ObjectMap::ErrnoObject);
    aux_to_obj_.emplace(aux.PthreadSpecificNode,
        ObjectMap::PthreadSpecificValue);

    std::for_each(std::begin(aux_val_nodes), std::end(aux_val_nodes),
        [this, &aux, &omap]
        (const std::pair<const llvm::Value *, uint32_t> &pr) {
      auto obj_id = omap.getObject(pr.first);
      // auto obj_id = omap.getValue(pr.first);
      auto aux_val_id = pr.second;

      dout("  " << aux_val_id << "->" << obj_id <<
        "\n");
      assert(aux_to_obj_.find(aux_val_id) == std::end(aux_to_obj_));
      aux_to_obj_.emplace(aux_val_id, obj_id);
    });
  }

  // Now, fill in the indirect function calls
  {
    PerfTimerPrinter indir_timer(llvm::dbgs(), "addIndirectCalls");
    if (addIndirectCalls(cg, cfg, aux, omap)) {
      error("AddIndirectCalls failure!");
    }
  }

  // Now that we've resolve our indir edges, we can remove duplicate constraints
  // (possibly created by optimizeConstraints())
  {
    PerfTimerPrinter unique_timer(llvm::dbgs(), "cg.unique()");
    cg.unique();
  }

  // The PE graph was updated by addIndirectCalls

  if_debug(cfg.getSEG().printDotFile("CFG_indir.dot", omap));

  // Now, compute the SSA form for the top-level variables
  // We translate any PHI nodes into copy nodes... b/c the paper says so
  CFG::ControlFlowGraph ssa;
  {
    PerfTimerPrinter ssa_timer(llvm::dbgs(), "computeSSA");
    ssa = std::move(computeSSA(cfg.getSEG()));
  }

  if_debug(ssa.printDotFile("CFG_ssa.dot", omap));

  {
    PerfTimerPrinter seg_timer(llvm::dbgs(), "setSEG");
    cfg.setSEG(std::move(ssa));
  }

  // Compute partitions, based on address equivalence
  DUG graph;

  {
    PerfTimerPrinter fill_timer(llvm::dbgs(), "fillTopLevel");
    graph.fillTopLevel(cg, omap);
  }

  {
    PerfTimerPrinter partition_timer(llvm::dbgs(), "computePartitions");
    if (computePartitions(graph, cfg, aux, omap)) {
      error("ComputePartitions failure!");
    }
  }

  // Compute SSA for each partition
  {
    PerfTimerPrinter part_dug_timer(llvm::dbgs(), "addPartitionsToDUG");
    if (addPartitionsToDUG(graph, cfg, omap)) {
      error("ComputePartSSA failure!");
    }
  }

  graph.setStructInfo(omap.getIsStructSet());

  // Finally, solve the graph
  {
    PerfTimerPrinter solve_timer(llvm::dbgs(), "solve");
    if (solve(graph, omap)) {
      error("Solve failure!");
    }
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


