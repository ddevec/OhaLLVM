/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LIB_DYNPTSTO_H_
#define INCLUDE_LIB_DYNPTSTO_H_

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

#include "include/ExtInfo.h"
#include "include/SolveHelpers.h"

class DynPtstoLoader : public llvm::ModulePass {
 public:
  static char ID;

  DynPtstoLoader() : llvm::ModulePass(ID) { }

  bool runOnModule(llvm::Module &m) override;

  void getAnalysisUsage(llvm::AnalysisUsage &au) const override;

  llvm::StringRef getPassName() const override {
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
    auto val_id = map_.getDef(val);
    auto it = valToObjs_.find(val_id);

    if (it == std::end(valToObjs_)) {
      return false;
    } else {
      return true;
    }
  }

  PtstoSet &getPtsto(const llvm::Value *val) {
    auto val_id = map_.getDef(val);

    assert(hasInfo_);
    static PtstoSet empty_set;
    auto it = valToObjs_.find(val_id);
    if (it == std::end(valToObjs_)) {
      return empty_set;
    } else {
      return it->second;
    }
  }

  typedef std::map<ValueMap::Id, PtstoSet>::const_iterator
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

    if (!pts1.intersectsIgnoring(pts2, ValueMap::NullValue)) {
      return true;
    }

    return false;
  }

 private:
  void setupSpecSFSids(llvm::Module &);

  ValueMap map_;
  std::map<ValueMap::Id, PtstoSet> valToObjs_;
  bool hasInfo_ = false;
};

class DynPtstoAA : public llvm::ModulePass,
                   public llvm::AAResultBase<DynPtstoAA> {
 public:
  static char ID;

  DynPtstoAA() : llvm::ModulePass(ID) { }

  bool runOnModule(llvm::Module &m) override;

  void getAnalysisUsage(llvm::AnalysisUsage &au) const override;

  /*
  virtual void *getAdjustedAnalysisPointer(llvm::AnalysisID PI) {
    if (PI == &AliasAnalysis::ID) {
      // return (llvm::AliasAnalysis *)this;
      return static_cast<llvm::AliasAnalysis *>(this);
    }
    return this;
  }
  */

  virtual llvm::AliasResult alias(const llvm::MemoryLocation &L1,
      const llvm::MemoryLocation &L2);
 private:
  DynPtstoLoader *dynPts_;
};

#endif  // INCLUDE_LIB_DYNPTSTO_H_
