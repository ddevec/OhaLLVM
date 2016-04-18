/*
 * Copyright (C) 2016 David Devecsery
 *
 */

#ifndef INCLUDE_EXTINFO_H_
#define INCLUDE_EXTINFO_H_

#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Instructions.h"
#include "llvm/Module.h"
#include "llvm/Support/CallSite.h"

#include "include/ObjectMap.h"
#include "include/ConstraintGraph.h"
#include "include/ControlFlowGraph.h"
#include "include/LLVMHelper.h"


enum class AllocStatus {
  // Assume weak maybe-struct
  Strong,
  Weak,
  None
};

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

  // A pair representing what is allocated by a given instruction.
  //  - first -- AllocStatus -- If the allocation is weak, strong, none, or
  //                            unknown
  //  - second -- type       -- The conservative type (nullptr if non-struct) of
  //                            the allocation -- used to determine allocation
  //                            size
  typedef std::pair<AllocStatus, const llvm::Type *> StaticAllocInfo;

  virtual bool insertCallCons(llvm::ImmutableCallSite &ci, ObjectMap &omap,
      ConstraintGraph &cg, CFG &cfg, CFG::CFGid *next_id) const = 0;

  virtual std::vector<AllocInfo> getAllocData(llvm::Module &m,
      llvm::CallSite &ci, ObjectMap &omap,
      llvm::Instruction **insert_after) const = 0;

  virtual std::vector<llvm::Value *> getFreeData(llvm::Module &m,
      llvm::CallSite &ci, ObjectMap &omap,
      llvm::Instruction **insert_after) const = 0;

  StaticAllocInfo getAllocInfo(const llvm::CallInst *ci,
      ObjectMap &omap) const {
    llvm::ImmutableCallSite ics(ci);

    return getAllocInfo(ics, omap);
  }

  virtual bool canAlloc() const = 0;

  StaticAllocInfo getAllocInfo(llvm::CallSite &cs,
      ObjectMap &omap) const {
    llvm::ImmutableCallSite ics(cs);

    return getAllocInfo(ics, omap);
  }

  virtual StaticAllocInfo getAllocInfo(llvm::ImmutableCallSite &cs,
      ObjectMap &omap) const = 0;
};

class UnknownExtInfo : public ExtInfo {
 public:
  UnknownExtInfo() = default;

  bool insertCallCons(llvm::ImmutableCallSite &ci, ObjectMap &omap,
      ConstraintGraph &cg, CFG &cfg, CFG::CFGid *next_id) const override;

  std::vector<AllocInfo> getAllocData(llvm::Module &m, llvm::CallSite &ci,
      ObjectMap &omap, llvm::Instruction **insert_after) const override;

  std::vector<llvm::Value *> getFreeData(llvm::Module &m, llvm::CallSite &ci,
      ObjectMap &omap,
      llvm::Instruction **insert_after) const override;

  StaticAllocInfo getAllocInfo(llvm::ImmutableCallSite &cs,
      ObjectMap &omap) const override;

  // Unknown functions cannot alloc, Universal Value covers this...
  bool canAlloc() const { return false; }
};

class ExtLibInfo {
 public:
  ExtLibInfo() = default;

  void init(llvm::Module &m, ObjectMap &omap);

  const UnknownExtInfo UnknownFunction;

  bool isUnknownFunction(const ExtInfo &inf) const {
    return &inf == &UnknownFunction;
  }

  const ExtInfo &getInfo(const llvm::CallInst *ci) const {
    auto fcn = LLVMHelper::getFcnFromCall(ci);
    if (fcn == nullptr) {
      return UnknownFunction;
    }

    return getInfo(fcn->getName());
  }

  const ExtInfo &getInfo(llvm::CallSite &cs) const {
    auto ci = cast<llvm::CallInst>(cs.getInstruction());
    return getInfo(ci);
  }

  const ExtInfo &getInfo(llvm::ImmutableCallSite &cs) const {
    auto ci = cast<llvm::CallInst>(cs.getInstruction());
    return getInfo(ci);
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

#endif  // INCLUDE_EXTINFO_H_

