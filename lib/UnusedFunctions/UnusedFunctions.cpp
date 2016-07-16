/*
 * Copyright (C) 2015 David Devecsery
 */

#include "lib/UnusedFunctions.h"

#include "lib/EdgeCountPass.h"

#include "llvm/Function.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

static llvm::cl::opt<bool>
  IgnoreDynInfo("ignore-unused", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc("If set, analyses will ignore unused function info"));

UnusedFunctions::UnusedFunctions() : llvm::ModulePass(ID),
  ignoreUnused_(IgnoreDynInfo) { }

void UnusedFunctions::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.addRequired<DynEdgeLoader>();
  // AU.addRequired<llvm::ProfileInfoLoader>();
  AU.setPreservesAll();
}

bool UnusedFunctions::runOnModule(llvm::Module &m) {
  // llvm::dbgs() << "In runOnModule!\n";

  int used_fcns = 0;
  int unused_fcns = 0;

  int used_bbs = 0;
  int unused_bbs = 0;

  auto &dyn_edges = getAnalysis<DynEdgeLoader>();

  // Check for unused functions
  if (dyn_edges.hasDynData()) {
    llvm::dbgs() << "UnusedFunctions: Successfully Loaded\n";
    for (auto &fcn : m) {
      // llvm::dbgs() << "Iterating fcn: " << fcn.getName() << "\n";
      if (fcn.isDeclaration()) {
        continue;
      }

      auto execution_count = dyn_edges.getExecutionCount(&fcn);
      // llvm::dbgs() << "  ExecutionCount is: " << execution_count << "\n";

      if (execution_count < 1) {
        unused_fcns++;
        // llvm::dbgs() << "Found unused fcn: " << fcn.getName() << "!\n";
      } else {
        used_fcns++;
        visited_.insert(&fcn);
      }
    }

    // Check for unused Basic Blocks
    for (auto &fcn : m) {
      for (auto &bb : fcn) {
        // llvm::dbgs() << "Scanning bb: " << bb.getName() << "\n";
        if (dyn_edges.getExecutionCount(&bb) < 1) {
          // llvm::dbgs() << "  Unused\n";
          unused_bbs++;
        } else {
          visitedBB_.insert(&bb);
          // llvm::dbgs() << "  Used\n";
          used_bbs++;
        }
      }
    }
    allUsed_ = false;
  } else {
    llvm::dbgs() << "UnusedFunctions: No logfile loaded\n";
    allUsed_ = true;
  }

  // llvm::dbgs() << "num used_fcns: " << used_fcns << "\n";
  // llvm::dbgs() << "num unused_fcns: " << unused_fcns << "\n";

  // llvm::dbgs() << "num used_bbs: " << used_bbs << "\n";
  // llvm::dbgs() << "num unused_bbs: " << unused_bbs << "\n";

  return false;
}

char UnusedFunctions::ID = 0;
static llvm::RegisterPass<UnusedFunctions> X("unused-functions",
    "Simple pass, analyses pathprofileinfo to determine which functions are"
    " unused",
    false, false);


