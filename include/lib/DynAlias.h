/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LIB_DYNALIAS_H_
#define INCLUDE_LIB_DYNALIAS_H_

#include <map>
#include <set>

#include "llvm/Pass.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/Debug.h"

#include "include/SolveHelpers.h"
#include "include/ValueMap.h"

#include "include/InstPrinter.h"

class DynAliasLoader : public llvm::ModulePass {
 public:
  static char ID;

  DynAliasLoader() : llvm::ModulePass(ID) { }

  bool runOnModule(llvm::Module &m) override;

  void getAnalysisUsage(llvm::AnalysisUsage &au) const override;

  llvm::StringRef getPassName() const override {
    return "DynAliasLoader";
  }

  bool hasInfo() const {
    return hasInfo_;
  }

  /*
  bool hasPtsto(ValueMap::Id &val_id) const {
    assert(hasInfo_);
    auto it = valToObjs_.find(val_id);

    if (it == std::end(valToObjs_)) {
      return false;
    } else {
      return true;
    }
  }
  */

  bool hasPtsto(const llvm::Value *val) {
    assert(hasInfo_);
    auto val_id = map_.getDef(val);
    auto it = valToObjs_.find(val_id);

    if (it == std::end(valToObjs_)) {
      return false;
    } else {
      return true;
    }
  }

  std::set<ValueMap::Id> &getPtsto(const llvm::Value *val) {
    ValueMap::Id val_id = map_.getDef(val);

    assert(hasInfo_);
    static std::set<ValueMap::Id> empty_set;
    auto it = valToObjs_.find(val_id);
    if (it == std::end(valToObjs_)) {
      return empty_set;
    } else {
      return it->second;
    }
  }

  typedef std::map<ValueMap::Id, std::set<ValueMap::Id>>::const_iterator
    const_iterator;

  const_iterator begin() const {
    return std::begin(valToObjs_);
  }

  const_iterator end() const {
    return std::end(valToObjs_);
  }

  bool loadStoreAlias(const llvm::LoadInst *li, const llvm::StoreInst *si) {
    // Check for the store inst in our load alias set...
    auto sid = map_.getDef(si);
    auto lid = map_.getDef(li);

    // Get the loadinst for our value:
    auto load_it = valToObjs_.find(lid);
    // If we couldn't find the value in our set, assume an alias
    if (load_it == std::end(valToObjs_)) {
      return false;
    }

    auto &load_ptsto = load_it->second;

    // If we have some unknown dynamic info, Fallback to a static alias analysis
    if (load_ptsto.find(ValueMap::Id::invalid()) !=
        std::end(load_ptsto)) {
      auto &aa = getAnalysis<llvm::AAResultsWrapperPass>().getAAResults();
      return aa.alias(llvm::MemoryLocation(li->getOperand(0)),
          llvm::MemoryLocation(si->getOperand(1))) !=
        llvm::AliasResult::NoAlias;
    }

    return load_ptsto.find(sid) != std::end(load_ptsto);
  }

  std::vector<const llvm::Value *> getAliases(const llvm::LoadInst *li) {
    auto lid = map_.getDef(li);
    auto load_it = valToObjs_.find(lid);

    if (load_it == std::end(valToObjs_)) {
      return std::vector<const llvm::Value *>();
    }

    auto &load_ptsto = load_it->second;

    std::vector<const llvm::Value *> ret;
    for (auto sid : load_ptsto) {
      if (sid == ValueMap::Id::invalid()) {
        return std::vector<const llvm::Value *>(1, nullptr);
      }

      ret.push_back(map_.getValue(sid));
    }

    return ret;
  }

  const llvm::Value *valueAtID(ValueMap::Id id) {
    return map_.getValue(id);
  }

  const ValueMap &map() const {
    return map_;
  }

 private:
  void setupSpecSFSids(llvm::Module &);

  ValueMap map_;
  std::map<ValueMap::Id, std::set<ValueMap::Id>> valToObjs_;
  bool hasInfo_ = false;
};

class DynAliasTester : public llvm::ModulePass {
 public:
  static char ID;

  DynAliasTester() : llvm::ModulePass(ID) { }

  bool runOnModule(llvm::Module &m) override;

  void getAnalysisUsage(llvm::AnalysisUsage &au) const override;

 private:
  DynAliasLoader *dynAA_;
};

#endif  // INCLUDE_LIB_DYNALIAS_H_
