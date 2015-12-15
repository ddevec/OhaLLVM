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
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
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

static llvm::cl::opt<bool>
  do_anders_print_result("specanders-do-print-result", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc(
        "if set specanders will print the ptsto sets for each value"));


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

  // Clear the def-use graph
  // It should already be cleared, but I'm paranoid
  const auto &cons_pass = getAnalysis<ConstraintPass>();
  ConstraintGraph cg(cons_pass.getConstraintGraph());
  ObjectMap omap(cons_pass.getObjectMap());

  // Now that we have the constraints, lets optimize a bit
  // First, do HVN
  // HVN(cg, omap);

  // Then, do HRU
  // HRU(cg, omap, 100);

  // Then, HCD
  // auto hcd_map = HCD(cg, omap);

  // Fill our online graph with the initial constraint set
  graph_.fill(cg, omap, m);

  // Solve the graph
  solve();

  {
    util::PerfTimerPrinter solve_timer(llvm::dbgs(), "AndersSolve");
    if (solve()) {
      error("Solve failure!");
    }
  }

  if (glbl_name != "") {
    // DEBUG {{{
    llvm::dbgs() << "Printing ptsto for global variable: " << glbl_name << "\n";
    auto glbl = m.getNamedValue(glbl_name);
    auto val_id = omap.getValue(glbl);

    // FIXME: This is a huge hack
    llvm::dbgs() << "ptsto[" << val_id << "]: " << ValPrint(val_id) <<
      "\n";
    int32_t i = 0;
    while (omap.valueAtID(val_id) == glbl) {
      llvm::dbgs() << "  Offset: " << i << "\n";

      auto &ptsto = graph_.getNode(val_id).ptsto();

      std::for_each(std14::cbegin(ptsto), std14::cend(ptsto),
          [&omap] (const ObjectMap::ObjID obj_id) {
        llvm::dbgs() << "    " << obj_id << ": " << ValPrint(obj_id)
            << "\n";
      });

      val_id++;
      i++;
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
        auto arg_id = omap.getValue(&arg);
        auto arg_val = &arg;
        // FIXME: This is a huge hack
        llvm::dbgs() << "ptsto[" << arg_id << "]: " << ValPrint(arg_id) <<
          "\n";

        int32_t i = 0;

        while (omap.valueAtID(arg_id) == arg_val) {
          llvm::dbgs() << "  Offset: " << i << "\n";

          auto &ptsto = graph_.getNode(arg_id).ptsto();

          std::for_each(std14::cbegin(ptsto), std14::cend(ptsto),
              [&omap] (const ObjectMap::ObjID obj_id) {
            llvm::dbgs() << "    " << obj_id << ": " << ValPrint(obj_id)
                << "\n";
          });

          arg_id++;
          i++;
        }
      }
    });

    llvm::dbgs() << "Printing instructions: " << fcn_name << "\n";
    std::for_each(inst_begin(fcn), inst_end(fcn),
        [this, &omap] (llvm::Instruction &inst) {
      if (llvm::isa<llvm::PointerType>(inst.getType())) {
        auto val_id = omap.getValue(&inst);

        // FIXME: This is a huge hack
        llvm::dbgs() << "ptsto[" << val_id << "]: " << ValPrint(val_id) <<
          "\n";

        int32_t i = 0;

        while (omap.valueAtID(val_id) == &inst) {
          llvm::dbgs() << "  Offset: " << i << "\n";

          auto &ptsto = graph_.getNode(val_id).ptsto();

          std::for_each(std14::cbegin(ptsto), std14::cend(ptsto),
              [&omap] (const ObjectMap::ObjID obj_id) {
            llvm::dbgs() << "    " << obj_id << ": " << ValPrint(obj_id)
                << "\n";
          });

          val_id++;
          i++;
        }
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
  if (pts1.size() == 0 || pts2.size() == 0) {
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



