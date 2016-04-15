/*
 * Copyright (C) 2016 David Devecsery
 *
 */

#ifndef INCLUDE_EXTINFO_H_
#define INCLUDE_EXTINFO_H_

#include <unordered_map>
#include <utility>
#include <vector>

#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Instructions.h"
#include "llvm/Module.h"

#include "include/ObjectMap.h"
#include "include/ConstraintGraph.h"
#include "include/ControlFlowGraph.h"

class ExtInfo {
 public:
  ExtInfo() = default;

  // A tuple representing the data allocated/returned by a functon
  //  -- get<0> -- value -- the value allocated by the function
  //  -- get<1> -- size  -- an llvm::Value representing the size of the
  //                            allocated object
  //  -- get<2> -- id    -- An ObjID representing what static object this data
  //                            is associated with -- ObjID::invalid() if the
  //                            data is a non-static (stack/heap based)
  //                            allocation (ex. from malloc)
  typedef std::tuple<llvm::Value *, llvm::Value *, ObjectMap::ObjID> AllocInfo;

  virtual bool insertCallCons(llvm::ImmutableCallSite *ci, ObjectMap &omap,
      ConstraintGraph &cg, CFG &cfg) const = 0;

  virtual std::vector<AllocInfo> getAllocData(llvm::Module &m, llvm::CallSite &ci,
      ObjectMap &omap,
      llvm::Value **insert_after) const = 0;

  virtual std::vector<llvm::Value *> getFreeData(llvm::Module &m, llvm::CallSite &ci,
      ObjectMap &omap,
      llvm::Value **insert_after) const = 0;
};

class UnknownExtInfo : public ExtInfo {
 public:
  UnknownExtInfo() = default;

  bool insertCallCons(llvm::ImmutableCallSite *ci, ObjectMap &omap,
      ConstraintGraph &cg, CFG &cfg) const override;

  std::vector<AllocInfo> getAllocData(llvm::Module &m, llvm::CallSite &ci,
      ObjectMap &omap, llvm::Value **insert_after) const override;

  std::vector<llvm::Value *> getFreeData(llvm::Module &m, llvm::CallSite &ci,
      ObjectMap &omap,
      llvm::Value **insert_after) const override;
};

class ExtLibInfo {
 public:
  ExtLibInfo();

  const UnknownExtInfo UnknownFunction;

  bool isUnknownFunction(const ExtInfo &inf) const {
    return &inf == &UnknownFunction;
  }

  const ExtInfo &getInfo(const std::string &fcn) const {
    auto it = info_.find(fcn);

    // If we don't know 
    if (it != std::end(info_)) {
      return *it->second;
    }

    // We don't have it in info_, still check partial matches
    for (auto &pr : matchInfo_) {
      if (fcn.find(pr.first)) {
        return *pr.second;
      }
    }

    llvm::dbgs() << "!!! Unknown external call: " << fcn << "\n";
    return UnknownFunction;
  }

 private:
  std::unordered_map<std::string, std::unique_ptr<ExtInfo>> info_;
  // Partial matches
  std::vector<std::pair<std::string, std::unique_ptr<ExtInfo>>> matchInfo_;
};

#endif  // INCLUDE_ALLOCINFO_H_

