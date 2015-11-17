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
#include "llvm/Support/CallSite.h"
#include "llvm/Support/Debug.h"

#include "include/SpecSFS.h"
#include "include/ObjectMap.h"

class DynPtstoLoader : public SpecSFS {
 public:
    static char ID;

    DynPtstoLoader() : SpecSFS(ID) { }

    bool runOnModule(llvm::Module &m) override;

    void getAnalysisUsage(llvm::AnalysisUsage &au) const override;

    bool hasInfo() const {
      return hasInfo_;
    }

    bool hasPtsto(ObjectMap::ObjID &val_id) const {
      assert(hasInfo_);
      auto it = valToObjs_.find(val_id);

      if (it == std::end(valToObjs_)) {
        return false;
      } else {
        return true;
      }
    }

    const std::set<ObjectMap::ObjID> &getPtstoSet(const llvm::Value *val) {
      auto val_id = omap_.getValue(val);
      assert(hasInfo_);
      static std::set<ObjectMap::ObjID> empty_set;
      auto it = valToObjs_.find(val_id);
      if (it == std::end(valToObjs_)) {
        return empty_set;
      } else {
        return it->second;
      }
    }

    const std::set<ObjectMap::ObjID> &getPtsto(ObjectMap::ObjID &val_id) const {
      assert(hasInfo_);
      static std::set<ObjectMap::ObjID> empty_set;
      auto it = valToObjs_.find(val_id);
      if (it == std::end(valToObjs_)) {
        return empty_set;
      } else {
        return it->second;
      }
    }

 private:
    void setupSpecSFSids(llvm::Module &);

    std::map<ObjectMap::ObjID, std::set<ObjectMap::ObjID>> valToObjs_;
    bool hasInfo_ = false;
};

#endif  // INCLUDE_LIB_DYNPTSTO_H_
