/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/lib/CallDests.h"

#include <string>
#include <vector>

#include "include/lib/UnusedFunctions.h"

#include "include/LLVMHelper.h"

char CallDests::ID = 0;
CallDests::CallDests() : llvm::ModulePass(ID) { }

using llvm::AliasAnalysis;
typedef AliasAnalysis::Location Location;

namespace llvm {
  static RegisterPass<CallDests>
      X("call-dests", "Helper to show which callsites call which functions",
          false, false);
}  // namespace llvm

void CallDests::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  // Because we're an AliasAnalysis
  // AliasAnalysis::getAnalysisUsage(usage);
  usage.setPreservesAll();

  // For DCE
  usage.addRequired<IndirFunctionInfo>();

  // For function numbering?
  usage.addRequired<AliasAnalysis>();

  usage.addRequired<UnusedFunctions>();
}

bool CallDests::runOnModule(llvm::Module &m) {
  // Load all of our used analysis
  alias_ = &getAnalysis<AliasAnalysis>();
  indirInfo_ = &getAnalysis<IndirFunctionInfo>();

  m_ = &m;

  for (auto &fcn : m) {
    fcns_.push_back(&fcn);
  }

  return false;
}

const std::vector<const llvm::ReturnInst *> &
CallDests::populateRets(const llvm::Function *fcn) const {
  std::vector<const llvm::ReturnInst *> ret;

  for (auto &bb : *fcn) {
    for (auto &inst : bb) {
      if (auto ri = dyn_cast<llvm::ReturnInst>(&inst)) {
        ret.push_back(ri);
      }
    }
  }

  // Populate the memoization
  auto rc = rets_.emplace(fcn, std::move(ret));
  assert(rc.second);

  return rc.first->second;
}

const std::vector<const llvm::Function *> &
CallDests::populateCs(llvm::ImmutableCallSite &cs) const {
  std::vector<const llvm::Function *> ret;
  static std::vector<const llvm::Function *> empty_vector;

  // llvm::dbgs() << "  populateCs: " << *cs.getInstruction() << "\n";
  // Then, determine callsite/CFG information for
  //   each function in M
  //
  auto callee = cs.getCalledValue();
  if (callee != nullptr &&
      llvm::isa<llvm::InlineAsm>(callee)) {
    return empty_vector;
  }

  auto pfcn1 = cs.getCalledFunction();
  if (pfcn1 != nullptr && pfcn1->isIntrinsic()) {
    return empty_vector;
  }

  auto pfcn = LLVMHelper::getFcnFromCall(cs);


  // If I could statically infer the callsite:
  if (pfcn != nullptr) {
    ret.push_back(pfcn);
  // If it has a non-constant expr, use the AA (or indir fcns if that exists)
  } else {
    // Use indir info
    if (indirInfo_->hasInfo()) {
      /*
      llvm::dbgs() << "indir fcn info for: " <<
        ValPrinter(cs.getInstruction()) << "\n";
      */
      auto &dests = indirInfo_->getTargets(cs.getInstruction());

      for (auto &dest : dests) {
        auto dest_fcn = cast<llvm::Function>(dest);
        // llvm::dbgs() << "  Have dest: " << dest_fcn->getName() << "\n";
        ret.push_back(dest_fcn);
      }
    // Use alias analysis
    } else {
      auto called_value = cs.getCalledValue();

      for (auto &fcn : fcns_) {
        if (alias_->alias(Location(called_value),
              Location(fcn)) != AliasAnalysis::NoAlias) {
          ret.push_back(fcn);
        }
      }
    }
  }

  // Populate the memoization
  auto rc = csToDests_.emplace(cs.getInstruction(), std::move(ret));
  assert(rc.second);

  return rc.first->second;
}

void CallDests::fillCallers() const {
  auto &m = *m_;
  auto &dyn_info = getAnalysis<UnusedFunctions>();

  // For all call insts...
  for (auto &fcn : m) {
    if (!dyn_info.isUsed(fcn)) {
      continue;
    }

    for (auto &bb : fcn) {
      if (!dyn_info.isUsed(bb)) {
        continue;
      }

      for (auto &inst : bb) {
        if (auto ci = dyn_cast<llvm::CallInst>(&inst)) {
          // get dests of call:
          llvm::ImmutableCallSite cs(ci);

          auto &dests = getDests(cs);

          for (auto &dest : dests) {
            callers_[dest].push_back(ci);
          }
        }
      }
    }
  }
}

