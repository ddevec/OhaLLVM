/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LIB_DYNPTSTO_H_
#define INCLUDE_LIB_DYNPTSTO_H_

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

class DynPtstoLoader : public llvm::ModulePass {
 public:
  static char ID;

  DynPtstoLoader() : llvm::ModulePass(ID) { }

  bool runOnModule(llvm::Module &m) override;

  void getAnalysisUsage(llvm::AnalysisUsage &au) const override;

  const char *getPassName() const override {
    return "DynPtstoLoader";
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

  PtstoSet &getPtsto(const llvm::Value *val) {
    ObjectMap::ObjID val_id = omap_.getValOrConstRep(val);

    assert(hasInfo_);
    static PtstoSet empty_set;
    auto it = valToObjs_.find(val_id);
    if (it == std::end(valToObjs_)) {
      return empty_set;
    } else {
      return it->second;
    }
  }

  typedef std::map<ObjectMap::ObjID, PtstoSet>::const_iterator
    const_iterator;

  const_iterator begin() const {
    return std::begin(valToObjs_);
  }

  const_iterator end() const {
    return std::end(valToObjs_);
  }

  bool noAlias(const llvm::Value *v1, const llvm::Value *v2) {
    auto &pts1 = getPtsto(v1);
    auto &pts2 = getPtsto(v2);

    if (pts1.empty() || pts2.empty()) {
      return true;
    }

    if (!pts1.intersectsIgnoring(pts2, ObjectMap::NullValue)) {
      return true;
    }

    return false;
  }

 private:
  void setupSpecSFSids(llvm::Module &);

  ObjectMap omap_;
  std::map<ObjectMap::ObjID, PtstoSet> valToObjs_;
  bool hasInfo_ = false;
};

class DynPtstoAA : public llvm::ModulePass,
                   public llvm::AliasAnalysis {
 public:
  static char ID;

  DynPtstoAA() : llvm::ModulePass(ID) { }

  bool runOnModule(llvm::Module &m) override;

  void getAnalysisUsage(llvm::AnalysisUsage &au) const override;

  virtual void *getAdjustedAnalysisPointer(llvm::AnalysisID PI) {
    if (PI == &AliasAnalysis::ID) {
      // return (llvm::AliasAnalysis *)this;
      return static_cast<llvm::AliasAnalysis *>(this);
    }
    return this;
  }

  virtual AliasAnalysis::AliasResult alias(const AliasAnalysis::Location &L1,
      const AliasAnalysis::Location &L2);
 private:
  DynPtstoLoader *dynPts_;
};

#endif  // INCLUDE_LIB_DYNPTSTO_H_
