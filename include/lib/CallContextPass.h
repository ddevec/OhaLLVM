/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LIB_CALLCONTEXTPASS_H_
#define INCLUDE_LIB_CALLCONTEXTPASS_H_

#include <algorithm>
#include <iterator>
#include <unordered_map>
#include <vector>

#include "include/util.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"
#include "include/lib/CsCFG.h"

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

class CallContextLoader : public llvm::ModulePass {
 public:
  static char ID;
  CallContextLoader();

  virtual bool runOnModule(llvm::Module &m);

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  llvm::StringRef getPassName() const override {
    return "CallContextLoader";
  }

  bool hasDynData() const {
    return loaded_ && enabled_;
  }

  bool isValid(const std::vector<CsCFG::Id> &check) const {
    assert(hasDynData());
    auto it = std::lower_bound(std::begin(callsites_), std::end(callsites_),
        check);

    if (it == std::end(callsites_)) {
      return false;
    }

    auto &dyn_check = *it;
    if (dyn_check.size() < check.size()) {
      return false;
    }

    auto dyn_it = std::begin(dyn_check);
    for (auto elm : check) {
      auto dyn_elm = *dyn_it;

      if (elm != dyn_elm) {
        return false;
      }

      ++dyn_it;
    }

    return true;
  }

  CsCFG::Id getMainContext() const {
    return CsCFG::Id(0);
  }

  const std::vector<const std::vector<CsCFG::Id> *> &
  getAllContexts(CsCFG::Id id) const {
    return index_.at(id);
  }

  std::vector<const std::vector<CsCFG::Id> *>
  getAllContexts(const std::vector<CsCFG::Id> &prefix) const {
    // Get lower & upper bounds
    auto lower_it = std::lower_bound(
        std::begin(callsites_), std::end(callsites_),
        prefix);
    auto upper_it = std::upper_bound(
        std::begin(callsites_), std::end(callsites_),
        prefix);

    // Return new vector containing data
    std::vector<const std::vector<CsCFG::Id> *>
        ret(std::distance(lower_it, upper_it));

    std::transform(lower_it, upper_it, std::begin(ret),
        [] (const std::vector<CsCFG::Id> &v) {
          return &v;
        });

    return ret;
  }

  size_t numInvariants() const {
    return callsites_.size();
  }

  void disable() {
    enabled_ = false;
  }

  void enable() {
    enabled_ = true;
  }

 private:
  bool loaded_ = false;
  bool enabled_ = true;
  // Get all callsites containing a (non-strict) partial stack
  // Keep sorted, to do prefix lookup
  std::vector<std::vector<CsCFG::Id>> callsites_;

  // Also keep map, to do by-id lookup:
  std::unordered_map<CsCFG::Id, std::vector<const std::vector<CsCFG::Id> *>>
    index_;
};

#endif  // INCLUDE_LIB_CALLCONTEXTPASS_H_
