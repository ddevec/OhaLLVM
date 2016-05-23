/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_CALLDESTS_H_
#define INCLUDE_CALLDESTS_H_

#include "include/util.h"
#include "include/DUG.h"
#include "include/ObjectMap.h"
#include "include/LLVMHelper.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"

#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"


#include <functional>
#include <unordered_map>
#include <vector>

extern llvm::cl::opt<bool> do_spec;

/*
struct icsHasher {
  size_t operator()(const llvm::ImmutableCallSite &cs) const {
    return std::hash<llvm::Instruction *>()(cs.getInstruction());
  }
};
*/

class CallDests : public llvm::ModulePass {
 public:
  static char ID;
  CallDests();

  virtual bool runOnModule(llvm::Module &M);

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  const char *getPassName() const override {
    return "CallDests";
  }

  const std::vector<const llvm::Instruction *> &
  getCallers(const llvm::Function *fcn) const {
    if (callers_.empty()) {
      fillCallers();
    }

    return callers_.at(fcn);
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

  llvm::AliasAnalysis *alias_;
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

#endif  // INCLUDE_CALLDESTS_H_
