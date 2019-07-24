/*
 * Copyright (C) 2015 David Devecsery
 */

#include <map>
#include <vector>

#include "include/lib/DynAlias.h"
#include "include/lib/IndirFcnTarget.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/CallContextPass.h"

#include "llvm/Pass.h"
#include "llvm/PassSupport.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InstIterator.h"

static llvm::cl::opt<bool>
  no_calls("invariant-no-call", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc("Ignores callstack invariants"));

class CountObservations : public llvm::ModulePass {
 public:
  static char ID;
  CountObservations() : llvm::ModulePass(ID) { }

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const {
    usage.setPreservesAll();
    usage.addRequired<CallContextLoader>();
    usage.addRequired<IndirFunctionInfo>();
    usage.addRequired<UnusedFunctions>();
  }

  bool runOnModule(llvm::Module &m) override;
};

char CountObservations::ID = 0;
static llvm::RegisterPass<CountObservations>
  X("count-invariants", "CountObservations", false, false);

bool CountObservations::runOnModule(llvm::Module &) {
  auto &call_info = getAnalysis<CallContextLoader>();
  auto &indir_info = getAnalysis<IndirFunctionInfo>();
  auto &used_info = getAnalysis<UnusedFunctions>();

  llvm::dbgs() << "Unused Info Size: " << used_info.numInvariants() << "\n";
  llvm::dbgs() << "Indir Info Size: " << indir_info.numInvariants() << "\n";
  if (!no_calls) {
    llvm::dbgs() << "Call Info Size: " << call_info.numInvariants() << "\n";
  }

  // We never modify code
  return false;
}
