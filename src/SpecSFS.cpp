/*
 * Copyright (C) 2015 David Devecsery
 */

// Enable debugging prints for this file
// #define SPECSFS_DEBUG
// #define SPECSFS_LOGDEBUG
// #define SEPCSFS_PRINT_RESULTS

#include "include/SpecSFS.h"

#include <google/profiler.h>

#include <execinfo.h>

#include <algorithm>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "llvm/Pass.h"
#include "llvm/PassSupport.h"
#include "llvm/Function.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ProfileInfo.h"

#include "include/Debug.h"
#include "include/ObjectMap.h"
#include "include/SpecAnders.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"
#include "include/lib/DynPtsto.h"

using std::swap;

static llvm::cl::opt<std::string>
  fcn_name("specsfs-debug-fcn", llvm::cl::init(""),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("if set specsfs will print the ptsto set for this function"
        " at the end of execution"));

static llvm::cl::opt<bool>
  do_spec_diff("specsfs-do-spec-diff", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc("if set specsfs will print the ptstos counts which would "
        "have been identified by a speculative sfs run (for reporting "
        "improvment numbers)"));

static llvm::cl::opt<bool>
  do_spec_print_result("specsfs-do-print-result", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc(
        "if set specsfs will print the ptsto sets for each value"));

static llvm::cl::opt<bool>
  do_spec_dyn_debug("specsfs-do-check-dyn", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc(
        "Verifies the calculated points-to set is a superset of the dynamic "
        "points-to to"));

static llvm::cl::opt<std::string>
  glbl_name("specsfs-debug-glbl", llvm::cl::init(""),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("if set specsfs will print the ptsto set for this global"
        " at the end of execution"));

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

// Constructor
SpecSFS::SpecSFS() : llvm::ModulePass(ID) { }
// SpecSFS::SpecSFS(char &id) : llvm::ModulePass(id) { }
char SpecSFS::ID = 0;
namespace llvm {
  static RegisterPass<SpecSFS>
      X("SpecSFS", "Speculative Sparse Flow-sensitive Analysis", false, true);
  RegisterAnalysisGroup<AliasAnalysis> Y(X);
}  // namespace llvm

using llvm::PassRegistry;
using llvm::PassInfo;
using llvm::callDefaultCtor;
using llvm::AliasAnalysis;

void SpecSFS::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  // Because we're an AliasAnalysis
  // AliasAnalysis::getAnalysisUsage(usage);
  usage.addRequired<llvm::AliasAnalysis>();
  usage.setPreservesAll();

  // Calculates the constraints for this module for both sfs and andersens
  usage.addRequired<ConstraintPass>();

  // Staging analysis for sfs
  usage.addRequired<SpecAnders>();

  // For DCE
  usage.addRequired<UnusedFunctions>();
  // For indirect function following
  usage.addRequired<IndirFunctionInfo>();
  // For dynamic ptsto removal
  usage.addRequired<DynPtstoLoader>();
  usage.addRequired<llvm::ProfileInfo>();
}

// runOnModule, the primary pass
bool SpecSFS::runOnModule(llvm::Module &m) {
  // Set up our alias analysis
  // -- This is required for the llvm AliasAnalysis interface
  InitializeAliasAnalysis(this);

  if (do_spec) {
    llvm::dbgs() << "do-spec is true!\n";
  } else {
    llvm::dbgs() << "no do-spec!\n";
  }

  if (fcn_name != "") {
    llvm::dbgs() << "Got debug function: " << fcn_name << "\n";
  }
  if (glbl_name != "") {
    llvm::dbgs() << "Got debug gv: " << glbl_name << "\n";
  }


  // Clear the def-use graph
  // It should already be cleared, but I'm paranoid
  const auto &cons_pass = getAnalysis<ConstraintPass>();
  ConstraintGraph cg(cons_pass.getConstraintGraph());
  CFG cfg(cons_pass.getControlFlowGraph());
  omap_ = cons_pass.getObjectMap();
  ObjectMap &omap = omap_;

  // Initial optimization pass
  // Runs HU on the graph as it stands, w/ only top level info filled in
  // Removes any nodes deemed to be non-ptr (definitely null), and merges nodes
  //   with statically equivalent ptsto sets
  // Does not consider doing anything with indirect edges, as we haven't taken
  //   control-flow information for those nodes into account yet
  {
    util::PerfTimerPrinter opt_timer(llvm::dbgs(), "optimizeConstarints");
    if (SFSHU(cg, cfg, omap)) {
      error("OptimizeConstraints failure!");
    }
  }

  if_debug(cfg.getSEG().printDotFile("CFG.dot", omap));

  cfg.cleanup();

  SpecAnders &aux = getAnalysis<SpecAnders>();

  const UnusedFunctions &unused_fcns =
      getAnalysis<UnusedFunctions>();

  // Now, fill in the indirect function calls
  {
    util::PerfTimerPrinter indir_timer(llvm::dbgs(), "addIndirectCalls");
    auto dyn_indir_info = &getAnalysis<IndirFunctionInfo>();
    if (!do_spec || !unused_fcns.hasInfo()) {
      dyn_indir_info = nullptr;
    }
    if (addIndirectCalls(cg, cfg, aux, dyn_indir_info, omap)) {
      error("AddIndirectCalls failure!");
    }
  }

  // if_debug(cfg.getSEG().printDotFile("CFG_indir.dot", omap));
  // cfg.getSEG().printDotFile("CFG_indir.dot", omap);

  // Now, compute the SSA form for the top-level variables
  // We translate any PHI nodes into copy nodes... b/c the paper says so
  {
    util::PerfTimerPrinter ssa_timer(llvm::dbgs(), "computeSSA");
    computeSSA(cfg.getSEG());
  }

  // cfg.getSEG().printDotFile("CFG_ssa.dot", omap);

  // Compute partitions, based on address equivalence
  DUG graph;
  {
    util::PerfTimerPrinter fill_timer(llvm::dbgs(), "fillTopLevel");
    graph.fillTopLevel(cg, omap);
  }


  /*
  llvm::dbgs() << "ID 100827 is: " << FullValPrint(ObjectMap::ObjID(100827)) <<
    "\n";
  llvm::dbgs() << "ID 101052 is: " << FullValPrint(ObjectMap::ObjID(101052)) <<
    "\n";
  llvm::dbgs() << "ID 112793 is: " << FullValPrint(ObjectMap::ObjID(112793)) <<
    "\n";
  */

  // Now that we've filled in the top level constraint graph, we add in dynamic
  //   info (If we're using speculative optimizations)
  std::map<ObjectMap::ObjID, Bitmap> dyn_pts;
  if (do_spec) {
    util::PerfTimerPrinter dyn_timer(llvm::dbgs(), "Dynamic Ptsto Info");
    dyn_pts = addDynPtstoInfo(m, graph, cfg, omap);
  }

  {
    util::PerfTimerPrinter partition_timer(llvm::dbgs(), "computePartitions");
    if (computePartitions(graph, cfg, aux, omap)) {
      error("ComputePartitions failure!");
    }
  }

  // Compute SSA for each partition
  {
    util::PerfTimerPrinter part_dug_timer(llvm::dbgs(), "addPartitionsToDUG");
    if (addPartitionsToDUG(graph, cfg, omap)) {
      error("ComputePartSSA failure!");
    }
  }

  graph.setStructInfo(omap.getIsStructSet());

  // Finally, solve the graph
  {
    util::PerfTimerPrinter solve_timer(llvm::dbgs(), "solve");
    ProfilerStart("solve.prof");
    if (solve(graph, std::move(dyn_pts))) {
      error("Solve failure!");
    }
    ProfilerStop();
  }


  // Go through a function, and print the ptsto graph for that function, this
  // should be faster then printing the whole graph
  if (glbl_name != "") {
    // DEBUG {{{
    llvm::dbgs() << "Printing ptsto for global variable: " << glbl_name << "\n";
    auto glbl = m.getNamedValue(glbl_name);
    auto val_id = omap.getValue(glbl);
    auto &pts_set_vec = pts_top_.atVec(val_id);


    llvm::dbgs() << "pts_top[" << val_id << "]: " << ValPrint(val_id) <<
      "\n";

    for (uint32_t i = 0; i < pts_set_vec.size(); i++) {
      llvm::dbgs() << "  Offset: " << i << "\n";

      auto &ptsto = pts_set_vec[i];

      std::for_each(ptsto.cbegin(), ptsto.cend(),
          [&omap] (const ObjectMap::ObjID obj_id) {
        llvm::dbgs() << "    " << obj_id << ": " << ValPrint(obj_id)
            << "\n";
      });
    }
    //}}}
  }

  if (fcn_name != "") {
    // DEBUG {{{
    auto fcn = m.getFunction(fcn_name);

    llvm::dbgs() << "Printing ptsto for function: " << fcn_name << "\n";
    llvm::dbgs() << "Printing args: " << fcn_name << "\n";
    std::for_each(fcn->arg_begin(), fcn->arg_end(),
        [this, &omap] (const llvm::Argument &arg) {
      if (llvm::isa<llvm::PointerType>(arg.getType())) {
        auto val_id = omap.getValue(&arg);
        auto &pts_set_vec = pts_top_.atVec(val_id);

        llvm::dbgs() << "pts_top[" << val_id << "]: " << ValPrint(val_id) <<
          "\n";

        for (uint32_t i = 0; i < pts_set_vec.size(); i++) {
          llvm::dbgs() << "  Offset: " << i << "\n";

          auto &ptsto = pts_set_vec[i];

          std::for_each(ptsto.cbegin(), ptsto.cend(),
              [&omap] (const ObjectMap::ObjID obj_id) {
            llvm::dbgs() << "    " << obj_id << ": " << ValPrint(obj_id)
                << "\n";
          });
        }
      }
    });

    llvm::dbgs() << "Printing instructions: " << fcn_name << "\n";
    std::for_each(inst_begin(fcn), inst_end(fcn),
        [this, &omap] (llvm::Instruction &inst) {
      if (llvm::isa<llvm::PointerType>(inst.getType())) {
        auto val_id = omap.getValue(&inst);
        auto &pts_set_vec = pts_top_.atVec(val_id);

        llvm::dbgs() << "pts_top[" << val_id << "]: " << inst <<
          "\n";

        if (omap.valueAtID(val_id) != &inst) {
          llvm::dbgs() << "--have value remap: " << inst << " -> " <<
              *omap.valueAtID(val_id) << "\n";
        }

        for (uint32_t i = 0; i < pts_set_vec.size(); i++) {
          llvm::dbgs() << "  Offset: " << i << "\n";

          auto &ptsto = pts_set_vec[i];

          std::for_each(ptsto.cbegin(), ptsto.cend(),
              [&omap] (const ObjectMap::ObjID obj_id) {
            llvm::dbgs() << "    " << obj_id << ": " << ValPrint(obj_id)
                << "\n";
          });
        }
      }
    });
    //}}}
  }

  if (do_spec_diff) {
    // STATS! {{{
    int64_t total_variables = 0;
    int64_t total_ptstos = 0;

    int32_t num_objects[10] = {};

    size_t max_objects = 0;
    int32_t num_max = 0;

    auto &uf = getAnalysis<UnusedFunctions>();

    auto obj_update_fcn = [this, &total_variables, &total_ptstos, &num_objects,
         &max_objects, &num_max, &omap]
           (const llvm::Value *val) {
      auto val_id = omap.getValue(val);

      // Statistics
      auto &ptsto = pts_top_.at(val_id);
      size_t ptsto_size = ptsto.count();
      // size_t ptsto_size = ptsto.getSizeNoStruct(omap);

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
    };

    // Woot, time to walk the CFG!
    for (auto &fcn : m) {
      if (uf.isUsed(fcn)) {
        std::for_each(fcn.arg_begin(), fcn.arg_end(),
            [&obj_update_fcn, &omap]
            (const llvm::Argument &arg) {
          if (llvm::isa<llvm::PointerType>(arg.getType())) {
            obj_update_fcn(&arg);
          }
        });
      }
      for (auto &bb : fcn) {
        if (!uf.isUsed(bb)) {
          continue;
        }

        for (auto &inst : bb) {
          if (llvm::isa<llvm::PointerType>(inst.getType())) {
            obj_update_fcn(&inst);
          }
        }
      }
    }

    llvm::dbgs() << "Number tracked values: " << total_variables << "\n";
    llvm::dbgs() << "Number tracked ptstos: " << total_ptstos << "\n";

    llvm::dbgs() << "Max ptsto is: " << max_objects << ", with num_max: " <<
      num_max << "\n";

    llvm::dbgs() << "lowest ptsto counts:\n";
    for (int i = 0; i < 10; i++) {
      llvm::dbgs() << "  [" << i << "]:  " << num_objects[i] << "\n";
    }
    //}}}
  }

  if (do_spec_print_result) {
    // DEBUG {{{
    llvm::dbgs() << "Printing the rep mappings for top level variales:\n";
    for (auto &pr : obj_to_rep_) {
      auto obj_id = pr.first;
      auto rep_id = omap.getRep(obj_id);

      llvm::dbgs() << obj_id << "->" << rep_id << "\n";
    }


    llvm::dbgs() << "Printing final ptsto set for top level variables:\n";
    std::for_each(pts_top_.cbegin(), pts_top_.cend(),
        [&omap]
        (const TopLevelPtsto::PtsPair &pr) {
      auto top_val = omap.valueAtID(pr.id());

      if (omap.isObject(pr.id())) {
        llvm::dbgs() << "Object ";
      } else {
        llvm::dbgs() << "Value ";
      }

      if (top_val == nullptr) {
        llvm::dbgs() << "is (id): " << pr.id() << "\n";
      } else if (auto gv = dyn_cast<llvm::GlobalValue>(top_val)) {
        llvm::dbgs() << "(" << pr.id() << ") is: " <<
            gv->getName() << "\n";
      } else if (auto fcn = dyn_cast<llvm::Function>(top_val)) {
        llvm::dbgs() << "(" << pr.id() <<") is: " <<
            fcn->getName() << "\n";
      } else {
        llvm::dbgs() << "(" << pr.id() << ") is: " << *top_val << "\n";
      }

      for (uint32_t i = 0; i < pr.pts().size(); i++) {
        llvm::dbgs() << "  Offset: " << i << "\n";

        // Statistics
        auto &ptsto = pr.pts()[i];

        // Printing
        std::for_each(ptsto.cbegin(), ptsto.cend(),
            [&omap] (const ObjectMap::ObjID obj_id) {
          auto loc_val = omap.valueAtID(obj_id);

          if (loc_val == nullptr) {
            llvm::dbgs() << "    Value is (id): " << obj_id << "\n";
          } else if (auto gv = dyn_cast<llvm::GlobalValue>(loc_val)) {
            llvm::dbgs() << "    " << obj_id << ": " << gv->getName() << "\n";
          } else if (auto fcn = dyn_cast<llvm::Function>(loc_val)) {
            llvm::dbgs() << "    " << obj_id << ": " << fcn->getName() << "\n";
          } else {
            llvm::dbgs() << "    " << obj_id << ": " << *loc_val << "\n";
          }
        });
      }
    });
    //}}}
  }

  if (do_spec_dyn_debug) {
    // DEBUG {{{
    llvm::dbgs() << "Checking for dynamic points-to not in the static set\n";
    // Here we check that our calculated "static" pointsto
    // To do so, we iterate over each value in the dynamic points-to
    // We then get that value form our top-level set
    // We ensure that the dynamic version is a subset of the static one
    //   ERROR otherwise
    const auto &dyn_ptsto = getAnalysis<DynPtstoLoader>();
    assert(dyn_ptsto.hasInfo());

    // First, deal with nodes which have been optimized away from the
    //   dyn_ptsto set
    std::map<ObjectMap::ObjID, std::set<ObjectMap::ObjID>> new_dyn_ptsto;

    for (auto &pr : dyn_ptsto) {
      auto old_id = pr.first;
      auto &old_set = pr.second;
      auto new_id = omap.getRep(old_id);

      // Also, strip out structures to their base field
      if (!ObjectMap::isSpecial(new_id)) {
        auto val = omap.valueAtID(new_id);
        if (val != nullptr) {
          new_id = omap.getValue(val);
        }
        // assert(omap.isObject(new_id));
      }

      auto &new_set = new_dyn_ptsto[new_id];

      new_set.insert(std::begin(old_set), std::end(old_set));
    }

    // Okay, now we iterate the ptsto list:
    for (auto &pr : new_dyn_ptsto) {
      auto obj_id = pr.first;
      auto set_obj_id = pr.first;
      bool set_id_found = false;
      auto &dyn_pts_set = pr.second;

      // And we get the appropriate top-level ptsto variable:
      // NOTE: We intentionally copy that set here
      auto st_pts_set = pts_top_.at(obj_id);

      // We then add the base node of any struct fields in the static set
      std::vector<ObjectMap::ObjID> to_add;
      for (auto obj_id : st_pts_set) {
        auto base_pr = omap.findObjBase(obj_id);
        if (base_pr.first) {
          to_add.emplace_back(base_pr.second);
        }
      }

      for (auto id : to_add) {
        st_pts_set.set(id);
      }

      // Now, iterate each element in st_pts_set and ensure that it isn't
      //   present in dyn_pts_set
      if (set_obj_id != ObjectMap::NullValue) {
        for (auto obj_id : dyn_pts_set) {
          // Ensure that this element is in the static set
          if (st_pts_set.test(obj_id) == false) {
            // If this is the first time we've found a missing value for this
            //    set...
            if (!set_id_found) {
              const llvm::Function *fcn = nullptr;
              const llvm::BasicBlock *bb = nullptr;
              llvm::dbgs() << "Element: " << set_obj_id << ": ";
              auto val = omap.valueAtID(set_obj_id);
              if (val == nullptr) {
                llvm::dbgs() << "Value NULL";
              } else if (auto ins = dyn_cast<llvm::Instruction>(val)) {
                llvm::dbgs() << ins->getParent()->getParent()->getName() << ", "
                    << ins->getParent()->getName();
                if (!unused_fcns.isUsed(ins->getParent())) {
                  bb = ins->getParent();
                }
                if (!unused_fcns.isUsed(ins->getParent()->getParent())) {
                  fcn = ins->getParent()->getParent();
                }
              } else if (auto ins = dyn_cast<llvm::Argument>(val)) {
                llvm::dbgs() << ins->getParent()->getName() << ", (arg)";

                if (!unused_fcns.isUsed(ins->getParent())) {
                  fcn = ins->getParent();
                }
              } else if (auto fcn = dyn_cast<llvm::Function>(val)) {
                llvm::dbgs() << fcn->getName() << ", (fcn)";
              } else if (llvm::isa<llvm::GlobalVariable>(val)) {
                llvm::dbgs() << "(global)";
              }
              llvm::dbgs() << ": " << ValPrint(set_obj_id) << "\n";

              if (fcn) {
                llvm::dbgs() << "  !! In Unused Function: " << fcn->getName() <<
                  " !!\n";
              }
              if (bb) {
                llvm::dbgs() << "  !! In Unused BasicBlock: " <<
                  bb->getName() << " !!\n";
              }

              // Check if the ID given by the omap is equivalent to the ID given
              //   by our anaysis
              auto rep_id = omap.getRep(set_obj_id);
              if (rep_id != set_obj_id) {
                llvm::dbgs() << "  !! Merged AWAY by cons_opt !!\n";
              }

              set_id_found = true;
            }
            auto val = omap.valueAtID(obj_id);
            llvm::dbgs() << "  Found element in dyn set not in static set:\n";
            llvm::dbgs() << "    ";
            if (val == nullptr) {
              llvm::dbgs() << "NULL";
            } else if (auto ins = dyn_cast<llvm::Instruction>(val)) {
              llvm::dbgs() << ins->getParent()->getParent()->getName() << ", "
                  << ins->getParent()->getName();
            } else if (auto ins = dyn_cast<llvm::Argument>(val)) {
              llvm::dbgs() << ins->getParent()->getName() << ", (arg)";
            } else if (auto fcn = dyn_cast<llvm::Function>(val)) {
              llvm::dbgs() << fcn->getName() << ", (fcn)";
            } else if (llvm::isa<llvm::GlobalVariable>(val)) {
              llvm::dbgs() << "(global)";
            }
            llvm::dbgs() << ": " << ValPrint(obj_id) << "\n";
            llvm::dbgs() << "    (obj_id): " << obj_id << "\n";
          }
        }
      }
    }
    //}}}
  }

  /*
  if (alias(Location(nullptr), Location(nullptr)) != MayAlias) {
    llvm::dbgs() << "?\n";
  }
  */

  // We do not modify code, ever!
  return false;
}

llvm::AliasAnalysis::AliasResult SpecSFS::alias(const Location &L1,
                                            const Location &L2) {
  auto obj_id1 = omap_.getValue(L1.Ptr);
  auto obj_id2 = omap_.getValue(L2.Ptr);
  auto rep_id1 = omap_.getRep(obj_id1);
  auto rep_id2 = omap_.getRep(obj_id2);
  auto pts1_it = pts_top_.find(rep_id1);
  auto pts2_it = pts_top_.find(rep_id2);

  if (pts1_it == std::end(pts_top_)) {
    return AliasAnalysis::alias(L1, L2);
  }

  if (pts2_it == std::end(pts_top_)) {
    return AliasAnalysis::alias(L1, L2);
  }

  auto &pts1 = pts1_it->pts();
  auto &pts2 = pts2_it->pts();

  // If either of the sets point to nothing, no alias
  if (pts1.empty() || pts2.empty()) {
    return NoAlias;
  }

  // Check to see if the two pointers are known to not alias.  They don't alias
  // if their points-to sets do not intersect.
  if (!pts1.front().intersectsIgnoring(pts2.front(),
        ObjectMap::NullObjectValue)) {
    return NoAlias;
  }

  return AliasAnalysis::alias(L1, L2);
}

AliasAnalysis::ModRefResult SpecSFS::getModRefInfo(llvm::ImmutableCallSite CS,
                                   const llvm::AliasAnalysis::Location &Loc) {
  return AliasAnalysis::getModRefInfo(CS, Loc);
}

AliasAnalysis::ModRefResult SpecSFS::getModRefInfo(llvm::ImmutableCallSite CS1,
                                   llvm::ImmutableCallSite CS2) {
  return AliasAnalysis::getModRefInfo(CS1, CS2);
}

/*
void SpecSFS::getMustAliases(llvm::Value *P, std::vector<llvm::Value*> &RetVals) {
  return AliasAnalysis::getMustAliases(P, RetVals);
}
*/

// Do not use it.
bool SpecSFS::pointsToConstantMemory(const AliasAnalysis::Location &loc,
    bool or_local) {
  return AliasAnalysis::pointsToConstantMemory(loc, or_local);
}

void SpecSFS::deleteValue(llvm::Value *V) {
  // FIXME: Should do this
  // Really, I'm just going to ignore it...
  auto v_id = omap_.getValue(V);
  llvm::dbgs() << "Deleting value: " << v_id << "\n";
  pts_top_.remove(v_id);
  getAnalysis<AliasAnalysis>().deleteValue(V);
}

void SpecSFS::copyValue(llvm::Value *From, llvm::Value *To) {
  assert(0 && "Unimplemented -- need to fix after omap reps were added");
  auto from_id = omap_.getValue(From);
  auto to_id = omap_.getValue(To);

  // If to doesn't exist, make it
  if (to_id == ObjectMap::ObjID::invalid()) {
    omap_.addValue(To);
    to_id = omap_.getValue(To);
  }

  // From really should exist...
  assert(from_id != ObjectMap::ObjID::invalid());

  // Make to point to from
  omap_.mergeObjRep(to_id, from_id);

  getAnalysis<AliasAnalysis>().copyValue(From, To);
}


