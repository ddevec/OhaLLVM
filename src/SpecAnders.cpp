/*
 * Copyright (C) 2015 David Devecsery
 */

// Enable debugging prints for this file
// #define SPECSFS_DEBUG
// #define SPECSFS_LOGDEBUG
// #define SEPCSFS_PRINT_RESULTS

#include "include/SpecAnders.h"

#include <execinfo.h>

#include <algorithm>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "include/util.h"

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
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"
#include "include/lib/DynPtsto.h"

using std::swap;

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

static llvm::cl::opt<bool>
  do_spec_diff("anders-do-spec-diff", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc("if set specanders will print the ptstos counts which "
        "would have been identified by a speculative sfs run (for reporting "
        "improvment numbers)"));

static llvm::cl::opt<std::string>
  fcn_name("anders-debug-fcn", llvm::cl::init(""),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("if set anders will print the ptsto set for this function"
        " at the end of execution"));

static llvm::cl::opt<std::string>
  glbl_name("anders-debug-glbl", llvm::cl::init(""),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("if set anders will print the ptsto set for this global"
        " at the end of execution"));

static llvm::cl::list<int32_t> //  NOLINT
  id_debug("anders-debug-id",
      llvm::cl::desc("Specifies IDs to print the nodes of after andersens "
        "runs"));

static llvm::cl::list<int32_t> //  NOLINT
  id_print("anders-print-id",
      llvm::cl::desc("Specifies IDs to print the nodes of before andersens "
        "runs"));

static llvm::cl::opt<bool>
  do_anders_print_result("anders-do-print-result", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc(
        "if set specanders will print the ptsto sets for each value"));

static llvm::cl::opt<bool>
  do_spec_dyn_debug("anders-do-check-dyn", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc(
        "Verifies the calculated points-to set is a superset of the dynamic "
        "points-to to"));

// Constructor
SpecAnders::SpecAnders() : llvm::ModulePass(ID) { }
SpecAnders::SpecAnders(char &id) : llvm::ModulePass(id) { }
char SpecAnders::ID = 0;
namespace llvm {
  static RegisterPass<SpecAnders>
      SpecAndersRP("SpecAnders", "Speculative Andersens Analysis", false, true);
  RegisterAnalysisGroup<SpecAnders> SpecAndersRAG(SpecAndersRP);
}  // namespace llvm

void SpecAnders::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  // Because we're an AliasAnalysis
  // AliasAnalysis::getAnalysisUsage(usage);
  usage.addRequired<llvm::AliasAnalysis>();
  usage.setPreservesAll();

  // Calculates the constraints for this module for both sfs and andersens
  usage.addRequired<ConstraintPass>();

  // Staging analysis for sfs
  // usage.addRequired<SpecAnders>();

  // For DCE
  usage.addRequired<UnusedFunctions>();
  // For indirect function following
  usage.addRequired<IndirFunctionInfo>();
  // For dynamic ptsto removal
  usage.addRequired<DynPtstoLoader>();
  usage.addRequired<llvm::ProfileInfo>();
}

bool SpecAnders::runOnModule(llvm::Module &m) {
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

  const UnusedFunctions &unused_fcns =
      getAnalysis<UnusedFunctions>();

  // Clear the def-use graph
  // It should already be cleared, but I'm paranoid
  const auto &cons_pass = getAnalysis<ConstraintPass>();
  ConstraintGraph cg(cons_pass.getConstraintGraph());
  omap_ = cons_pass.getObjectMap();

  ObjectMap &omap = omap_;

  // Now that we have the constraints, lets optimize a bit
  // First, do HVN

  llvm::dbgs() << "Original number of constraints: " << cg.getNumConstraints()
    << "\n";
  {
    size_t num_alloc = 0;
    size_t num_gep = 0;
    size_t num_copy = 0;
    size_t num_load = 0;
    size_t num_store = 0;
    for (auto &pcons : cg) {
      if (pcons == nullptr) {
        continue;
      }

      switch (pcons->type()) {
        case ConstraintType::AddressOf:
          num_alloc++;
          break;
        case ConstraintType::Copy:
          if (pcons->offs() != 0) {
            num_gep++;
          } else {
            num_copy++;
          }
          break;
        case ConstraintType::Store:
          num_store++;
          break;
        case ConstraintType::Load:
          num_load++;
          break;
      }
    }

    llvm::dbgs() << "  num_objs: " << omap.getNumObjs() << "\n";
    llvm::dbgs() << "  num_alloc: " << num_alloc << "\n";
    llvm::dbgs() << "  num_gep: " << num_gep << "\n";
    llvm::dbgs() << "  num_copy: " << num_copy << "\n";
    llvm::dbgs() << "  num_load: " << num_load << "\n";
    llvm::dbgs() << "  num_store: " << num_store << "\n";
  }

  {
    util::PerfTimerPrinter hvn_timer(llvm::dbgs(), "HVN");
    int32_t removed = HVN(cg, omap);
    llvm::dbgs() << "hvn removed: " << removed << " constraints\n";
  }

  /*
  // Now manage remap:
  {
    auto remap = omap.lowerObjects();

    // Use the remapping to adjust the CG and CFG
    cg.updateObjIDs(remap);
    // specAssumptions_.updateObjIDs(remap);
  }
  */

  // Then, do HRU
  {
    util::PerfTimerPrinter hru_timer(llvm::dbgs(), "HRU");
    HRU(cg, omap, 100);
  }

  for (auto &id_val : id_print) {
    llvm::dbgs() << "Printing node for id: " << id_val << "\n";
    ObjectMap::ObjID val_id(id_val);

    llvm::dbgs() << "  " << val_id << ": " << FullValPrint(val_id) <<
      "\n";
  }

  llvm::dbgs() << "Constraints after HRU: " << cg.getNumConstraints()
    << "\n";
  {
    size_t num_alloc = 0;
    size_t num_gep = 0;
    size_t num_copy = 0;
    size_t num_load = 0;
    size_t num_store = 0;
    for (auto &pcons : cg) {
      if (pcons == nullptr) {
        continue;
      }

      switch (pcons->type()) {
        case ConstraintType::AddressOf:
          num_alloc++;
          break;
        case ConstraintType::Copy:
          if (pcons->offs() != 0) {
            num_gep++;
          } else {
            num_copy++;
          }
          break;
        case ConstraintType::Store:
          num_store++;
          break;
        case ConstraintType::Load:
          num_load++;
          break;
      }
    }

    llvm::dbgs() << "  num_objs: " << omap.getNumObjs() << "\n";
    llvm::dbgs() << "  num_alloc: " << num_alloc << "\n";
    llvm::dbgs() << "  num_gep: " << num_gep << "\n";
    llvm::dbgs() << "  num_copy: " << num_copy << "\n";
    llvm::dbgs() << "  num_load: " << num_load << "\n";
    llvm::dbgs() << "  num_store: " << num_store << "\n";

    Bitmap nodes;
    for (auto &pcons : cg) {
      if (pcons == nullptr) {
        continue;
      }

      // Ignore address of destinations?
      if (pcons->type() == ConstraintType::AddressOf) {
        // Add dest only for addressof
        nodes.set(pcons->dest().val());
        continue;
      }

      nodes.set(pcons->dest().val());
      nodes.set(pcons->src().val());
    }

    llvm::dbgs() << "  num_nodes: " << nodes.count() << "\n";
  }

  // Now manage remap: -- before HCD, as HCD fills some stuff in the
  //   class...
  /*
  {
    auto remap = omap.lowerObjects();

    // Use the remapping to adjust the CG and CFG
    cg.updateObjIDs(remap);
    // specAssumptions_.updateObjIDs(remap);
  }
  */

  // Then, HCD
  {
    util::PerfTimerPrinter hcd_timer(llvm::dbgs(), "HCD");
    // Gather hybrid cycle info from our graph
    HCD(cg, omap);
  }

  llvm::dbgs() << "Constraints after HCD: " << cg.getNumConstraints()
    << "\n";

  {
    util::PerfTimerPrinter graph_timer(llvm::dbgs(), "Graph Creation");
    // Fill our online graph with the initial constraint set
    graph_.fill(cg, omap, m);
  }

  graph_.setStructInfo(omap.getIsStructSet());

  {
    util::PerfTimerPrinter solve_timer(llvm::dbgs(), "AndersSolve");
    if (solve()) {
      error("Solve failure!");
    }
  }

  for (auto &id_val : id_debug) {
    // DEBUG {{{
    llvm::dbgs() << "Printing node for id: " << id_val << "\n";
    ObjectMap::ObjID val_id(id_val);

    llvm::dbgs() << "ptsto[" << val_id << "]: " << FullValPrint(val_id) <<
      "\n";
    auto rep_id = getRep(val_id);
    if (rep_id != val_id) {
      llvm::dbgs() << " REP: " << rep_id << ": " <<
        FullValPrint(rep_id) << "\n";
    }

    if (graph_.getNode(rep_id).id() != rep_id) {
      llvm::dbgs() << " Graph-REP: " << graph_.getNode(rep_id).id() << ": "
        << FullValPrint(graph_.getNode(rep_id).id()) << "\n";
    }

    auto &ptsto = getPointsTo(rep_id);

    std::for_each(std14::cbegin(ptsto), std14::cend(ptsto),
        [&omap] (const ObjectMap::ObjID obj_id) {
      llvm::dbgs() << "    " << obj_id << ": " << ValPrint(obj_id)
          << "\n";
    });

    llvm::dbgs() << "copySuccs: {";
    auto &succs = graph_.getNode(rep_id).copySuccs();
    for (auto succ_id : succs) {
      llvm::dbgs() << " " << succ_id;
    }
    llvm::dbgs() << " }\n";

    llvm::dbgs() << "gepSuccs: {";
    auto &gep_succs = graph_.getNode(rep_id).gepSuccs();
    for (auto &succ_pr : gep_succs) {
      llvm::dbgs() << " (" << succ_pr.first << " + " << succ_pr.second << ")";
    }
    llvm::dbgs() << " }\n";
    //}}}
  }

  if (glbl_name != "") {
    // DEBUG {{{
    llvm::dbgs() << "Printing ptsto for global variable: " << glbl_name << "\n";
    auto glbl = m.getNamedValue(glbl_name);
    auto val_id = omap.getValue(glbl);

    llvm::dbgs() << "ptsto[" << val_id << "]: " << ValPrint(val_id) <<
      "\n";
    auto rep_id = getRep(val_id);
    if (rep_id != val_id) {
      llvm::dbgs() << " REP: " << rep_id << ": " <<
        FullValPrint(rep_id) << "\n";
    }

    if (graph_.getNode(rep_id).id() != rep_id) {
      llvm::dbgs() << " Graph-REP: " << graph_.getNode(rep_id).id() << ": "
        << FullValPrint(graph_.getNode(rep_id).id()) << "\n";
    }

    auto &ptsto = getPointsTo(rep_id);

    std::for_each(std14::cbegin(ptsto), std14::cend(ptsto),
        [&omap] (const ObjectMap::ObjID obj_id) {
      llvm::dbgs() << "    " << obj_id << ": " << ValPrint(obj_id)
          << "\n";
    });
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
        auto arg_id = omap.getValue(&arg);
        llvm::dbgs() << "ptsto[" << arg_id << "]: " << ValPrint(arg_id) <<
          "\n";

        auto rep_id = getRep(arg_id);
        if (rep_id != arg_id) {
          llvm::dbgs() << " REP: " << rep_id << ": " <<
              FullValPrint(rep_id) << "\n";
        }

        if (graph_.getNode(rep_id).id() != rep_id) {
          llvm::dbgs() << " Graph-REP: " << graph_.getNode(rep_id).id() << ": "
            << FullValPrint(graph_.getNode(rep_id).id()) << "\n";
        }

        auto &ptsto = getPointsTo(rep_id);

        std::for_each(std14::cbegin(ptsto), std14::cend(ptsto),
            [&omap] (const ObjectMap::ObjID obj_id) {
          llvm::dbgs() << "    " << obj_id << ": " << ValPrint(obj_id)
              << "\n";
        });
      }
    });

    llvm::dbgs() << "Printing instructions: " << fcn_name << "\n";
    std::for_each(inst_begin(fcn), inst_end(fcn),
        [this, &omap] (llvm::Instruction &inst) {
      if (llvm::isa<llvm::PointerType>(inst.getType())) {
        auto val_id = omap.getValue(&inst);

        llvm::dbgs() << "ptsto[" << val_id << "]: " << ValPrint(val_id) <<
          "\n";

        auto rep_id = getRep(val_id);
        if (rep_id != val_id) {
          llvm::dbgs() << " REP: " << rep_id << ": " << FullValPrint(rep_id)
              << "\n";
        }

        if (graph_.getNode(rep_id).id() != rep_id) {
          llvm::dbgs() << " Graph-REP: " << graph_.getNode(rep_id).id() << ": "
            << FullValPrint(graph_.getNode(rep_id).id()) << "\n";
        }

        auto &ptsto = getPointsTo(rep_id);

        std::for_each(std14::cbegin(ptsto), std14::cend(ptsto),
            [&omap] (const ObjectMap::ObjID obj_id) {
          llvm::dbgs() << "    " << obj_id << ": " << ValPrint(obj_id)
              << "\n";
        });
      }
    });
    //}}}
  }

  /*
  if (do_anders_print_result) {
    // DEBUG {{{
    llvm::dbgs() << "Printing final ptsto set for variables in anders:\n";
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
  */

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

      /*
      if (old_id != new_id) {
        llvm::dbgs() << "old_id(" << old_id << ") -> new_id("
          << new_id << ")\n";


        llvm::dbgs() << "old_set:";
        for (auto elm : old_set) {
          llvm::dbgs() << " " << elm;
        }
        llvm::dbgs() << "\n";
      }
      */

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
      // Convert old node to new node:
      auto corrected_obj_id = omap.getRep(obj_id);

      /*
      llvm::dbgs() << "corrected_id: " << corrected_obj_id << ", obj_id: " <<
        obj_id << "\n";
      */
      auto st_pts_set = graph_.getNode(corrected_obj_id).ptsto();

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
              if (val != nullptr) {
                auto new_set_id = omap.getValue(val);
                if (new_set_id != set_obj_id) {
                  llvm::dbgs() << "  !! Merged AWAY by cons_opt !!\n";
                  llvm::dbgs() << "  !! new id: " << new_set_id << " !!\n";
                  llvm::dbgs() << "  !! old id: " << set_obj_id << " !!\n";
                }
              }

              set_id_found = true;
            }
            auto val = omap.valueAtID(obj_id);
            llvm::dbgs() << "  Found element in dyn set not in static set:\n";
            llvm::dbgs() << "    ";
            if (val == nullptr) {
              llvm::dbgs() << "(nullptr)";
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
      auto val_id = omap.getValueRep(val);

      // Statistics
      auto &ptsto = graph_.getNode(val_id).ptsto();
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

#ifndef NDEBUG
  // Verify I don't have any crazy stuff in the graph
  uint32_t num_nodes = 0;
  uint32_t num_node_pts = 0;
  uint32_t num_reps = 0;
  uint64_t num_copy_edges = 0;
  uint64_t num_gep_edges = 0;
  uint64_t total_pts_size = 0;
  for (auto &node : graph_) {
    // Gather num nodes
    num_nodes++;
    if (!node.isRep()) {
      // Assert non-reps don't have succs or ptstos
      assert(node.ptsto().empty());
      assert(node.copySuccs().empty());
      assert(node.gepSuccs().empty());
    } else {
      // Gather num reps
      num_reps++;


      if (!node.ptsto().empty()) {
        num_node_pts++;
      }

      total_pts_size += node.ptsto().count();
      num_copy_edges += node.copySuccs().count();
      num_gep_edges += node.gepSuccs().size();
      /*
      for (auto id : node.ptsto()) {
        total_pts_size++;
        // Should point to a rep
        // Not guaranteed, ever
        // assert(graph_.getNode(id).id() == id);
      }

      // Count avg number of outgoing edges
      for (auto id_val : node.copySuccs()) {
        // Should point to a rep
        // Not guaranteed, if a succ is merged after the last visit to this node
        // assert(graph_.getNode(id).id() == id);
        num_copy_edges++;
      }

      for (auto &pr : node.gepSuccs()) {
        auto id = pr.first;
        // Should point to a rep
        // Not guaranteed, if a succ is merged after the last visit to this node
        // assert(graph_.getNode(id).id() == id);
        num_gep_edges++;
      }
      */
    }
  }

  llvm::dbgs() << "num_nodes: " << num_nodes << "\n";
  llvm::dbgs() << "num_nonempty_nodes: " << num_node_pts << "\n";
  llvm::dbgs() << "num_reps: " << num_reps << "\n";
  llvm::dbgs() << "num_copy_edges: " << num_copy_edges << "\n";
  llvm::dbgs() << "num_gep_edges: " << num_gep_edges << "\n";
  llvm::dbgs() << "total_pts_size: " << total_pts_size << "\n";

#endif

  // Free any memory no longer needed by the graph (now that solve is done)
  graph_.cleanup();

  // We do not modify code, ever!
  return false;
}

llvm::AliasAnalysis::AliasResult SpecAnders::alias(const Location &L1,
                                            const Location &L2) {
  auto obj_id1 = omap_.getValue(L1.Ptr);
  auto obj_id2 = omap_.getValue(L2.Ptr);

  auto &node1 = graph_.getNode(obj_id1);
  auto &node2 = graph_.getNode(obj_id2);

  auto &pts1 = node1.ptsto();
  auto &pts2 = node2.ptsto();

  // If either of the sets point to nothing, no alias
  if (pts1.empty() || pts2.empty()) {
    return NoAlias;
  }

  // Check to see if the two pointers are known to not alias.  They don't alias
  // if their points-to sets do not intersect.
  if (!pts1.insersectsIgnoring(pts2,
        ObjectMap::NullObjectValue)) {
    return NoAlias;
  }

  return AliasAnalysis::alias(L1, L2);
}

llvm::AliasAnalysis::ModRefResult SpecAnders::getModRefInfo(
    llvm::ImmutableCallSite CS, const llvm::AliasAnalysis::Location &Loc) {
  return AliasAnalysis::getModRefInfo(CS, Loc);
}

llvm::AliasAnalysis::ModRefResult SpecAnders::getModRefInfo(
    llvm::ImmutableCallSite CS1, llvm::ImmutableCallSite CS2) {
  return AliasAnalysis::getModRefInfo(CS1, CS2);
}

bool SpecAnders::pointsToConstantMemory(const AliasAnalysis::Location &loc,
    bool or_local) {
  return AliasAnalysis::pointsToConstantMemory(loc, or_local);
}

