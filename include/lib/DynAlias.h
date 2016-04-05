/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LIB_DYNALIAS_H_
#define INCLUDE_LIB_DYNALIAS_H_

#include <map>
#include <set>

#include "llvm/BasicBlock.h"
#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Function.h"
#include "llvm/GlobalVariable.h"
#include "llvm/Instructions.h"
#include "llvm/Module.h"
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/Debug.h"

#include "include/SolveHelpers.h"
#include "include/ObjectMap.h"

class DynAliasLoader : public llvm::ModulePass {
 public:
  static char ID;

  DynAliasLoader() : llvm::ModulePass(ID) { }

  bool runOnModule(llvm::Module &m) override;

  void getAnalysisUsage(llvm::AnalysisUsage &au) const override;

  const char *getPassName() const override {
    return "DynAliasLoader";
  }

  bool hasInfo() const {
    return hasInfo_;
  }

  /*
  bool hasPtsto(ObjectMap::ObjID &val_id) const {
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
    auto val_id = omap_.getValueRep(val);
    auto it = valToObjs_.find(val_id);

    if (it == std::end(valToObjs_)) {
      return false;
    } else {
      return true;
    }
  }

  std::set<ObjectMap::ObjID> &getPtsto(const llvm::Value *val) {
    ObjectMap::ObjID val_id = omap_.getValOrConstRep(val);

    assert(hasInfo_);
    static std::set<ObjectMap::ObjID> empty_set;
    auto it = valToObjs_.find(val_id);
    if (it == std::end(valToObjs_)) {
      return empty_set;
    } else {
      return it->second;
    }
  }

  typedef std::map<ObjectMap::ObjID, std::set<ObjectMap::ObjID>>::const_iterator
    const_iterator;

  const_iterator begin() const {
    return std::begin(valToObjs_);
  }

  const_iterator end() const {
    return std::end(valToObjs_);
  }

  bool loadStoreAlias(const llvm::LoadInst *li, const llvm::StoreInst *si) {
    // Check for the store inst in our load alias set...
    auto sid = omap_.getValueC(si);
    auto lid = omap_.getValueC(li);

    // Get the loadinst for our value:
    auto load_it = valToObjs_.find(lid);
    if (load_it == std::end(valToObjs_)) {
      return false;
    }

    auto &load_ptsto = load_it->second;

    return load_ptsto.find(sid) != std::end(load_ptsto);
  }

  const llvm::Value *valueAtID(ObjectMap::ObjID id) {
    return omap_.valueAtID(id);
  }

  ObjectMap &omap() {
    return omap_;
  }

 private:
  void setupSpecSFSids(llvm::Module &);

  ObjectMap omap_;
  std::map<ObjectMap::ObjID, std::set<ObjectMap::ObjID>> valToObjs_;
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
