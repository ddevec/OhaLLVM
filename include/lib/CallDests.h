/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LIB_CALLDESTS_H_
#define INCLUDE_LIB_CALLDESTS_H_

#include <functional>
#include <map>
#include <unordered_map>
#include <vector>

#include "include/util.h"
#include "include/ValueMap.h"
#include "include/ModuleAAResults.h"
#include "include/LLVMHelper.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

extern llvm::cl::opt<bool> do_spec;

class CallDests : public llvm::ModulePass {
 public:
  static char ID;
  CallDests();

  virtual bool runOnModule(llvm::Module &M);

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  llvm::StringRef getPassName() const override {
    return "CallDests";
  }

  const std::vector<const llvm::Instruction *> &
  getCallers(const llvm::Function *fcn) const {
    if (callers_.empty()) {
      fillCallers();
    }

    return callers_[fcn];
  }

  const std::vector<const llvm::Function *> &
  getDests(llvm::ImmutableCallSite &cs) const {
    auto ins = cs.getInstruction();
    auto it = csToDests_.find(ins);

    if (it != std::end(csToDests_)) {
      return it->second;
    }

    return populateCs(cs);
  }

  const std::vector<const llvm::ReturnInst *> &
  getRets(const llvm::Function *fcn) const {
    auto it = rets_.find(fcn);

    if (it != std::end(rets_)) {
      return it->second;
    }

    return populateRets(fcn);
  }

 private:
  const std::vector<const llvm::Function *> &
  populateCs(llvm::ImmutableCallSite &cs) const;

  const std::vector<const llvm::ReturnInst *> &
  populateRets(const llvm::Function *fcn) const;

  void fillCallers() const;

  ModuleAAResults *alias_;
  IndirFunctionInfo *indirInfo_;

  llvm::Module *m_;

  std::vector<const llvm::Function *> fcns_;

  /*
  std::unordered_map<llvm::ImmutableCallSite,
    std::vector<const llvm::Instruction *>, icsHasher>
      csToDests_;
  */
  mutable std::map<const llvm::Instruction *,
    std::vector<const llvm::Function *>> csToDests_;

  mutable std::map<const llvm::Function *,
    std::vector<const llvm::ReturnInst *>> rets_;

  mutable std::map<const llvm::Function *,
    std::vector<const llvm::Instruction *>> callers_;
};

#endif  // INCLUDE_LIB_CALLDESTS_H_
