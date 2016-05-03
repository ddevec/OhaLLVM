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

#include "include/InstPrinter.h"

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
    // If we couldn't find the value in our set, assume an alias
    if (load_it == std::end(valToObjs_)) {
      return false;
    }

    auto &load_ptsto = load_it->second;

    // If we have some unknown dynamic info, Fallback to a static alias analysis
    if (load_ptsto.find(ObjectMap::ObjID::invalid()) !=
        std::end(load_ptsto)) {
      auto &aa = getAnalysis<llvm::AliasAnalysis>();
      return aa.alias(llvm::AliasAnalysis::Location(li->getOperand(0)),
          llvm::AliasAnalysis::Location(si->getOperand(1))) !=
        llvm::AliasAnalysis::NoAlias;
    }

    return load_ptsto.find(sid) != std::end(load_ptsto);
  }

  std::vector<const llvm::Value *> getAliases(const llvm::LoadInst *li) {
    auto lid = omap_.getValueC(li);
    auto load_it = valToObjs_.find(lid);

    if (load_it == std::end(valToObjs_)) {
      return std::vector<const llvm::Value *>();
    }

    auto &load_ptsto = load_it->second;

    std::vector<const llvm::Value *> ret;
    for (auto sid : load_ptsto) {
      if (sid == ObjectMap::ObjID::invalid()) {
        return std::vector<const llvm::Value *>(1, nullptr);
      }

      ret.push_back(omap_.valueAtID(sid));
    }

    return ret;
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
