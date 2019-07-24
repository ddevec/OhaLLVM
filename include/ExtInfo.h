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

#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/CallSite.h"

#include "include/ValueMap.h"
#include "include/ModInfo.h"
#include "include/LLVMHelper.h"


enum class AllocStatus {
  // Assume weak maybe-struct
  Strong,
  Weak,
  None
};

class Cg;
class CallInfo;
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
  typedef std::tuple<llvm::Value *, llvm::Value *, ValueMap::Id> AllocInfo;

  // A pair representing what is allocated by a given instruction.
  //  - first -- AllocStatus -- If the allocation is weak, strong, none, or
  //                            unknown
  //  - second -- type       -- The conservative type (nullptr if non-struct) of
  //                            the allocation -- used to determine allocation
  //                            size
  typedef std::pair<AllocStatus, const llvm::Type *> StaticAllocInfo;

  virtual bool insertCallCons(Cg &cg, llvm::ImmutableCallSite &cs,
      const CallInfo &ci) const = 0;

  virtual std::vector<AllocInfo> getAllocData(llvm::Module &m,
      llvm::CallSite &ci, ValueMap &map,
      llvm::Instruction **insert_after) const = 0;

  virtual std::vector<llvm::Value *> getFreeData(llvm::Module &m,
      llvm::CallSite &ci, ValueMap &map,
      llvm::Instruction **insert_after) const = 0;

  StaticAllocInfo getAllocInfo(const llvm::CallInst *ci,
      ModInfo &info) const {
    llvm::ImmutableCallSite ics(ci);

    return getAllocInfo(ics, info);
  }

  virtual bool canAlloc() const = 0;

  StaticAllocInfo getAllocInfo(llvm::CallSite &cs,
      ModInfo &info) const {
    llvm::ImmutableCallSite ics(cs);

    return getAllocInfo(ics, info);
  }

  virtual StaticAllocInfo getAllocInfo(llvm::ImmutableCallSite &cs,
      ModInfo &info) const = 0;
};

class UnknownExtInfo : public ExtInfo {
 public:
  UnknownExtInfo() = default;

  bool insertCallCons(Cg &cg, llvm::ImmutableCallSite &cs,
      const CallInfo &ci) const override;

  std::vector<AllocInfo> getAllocData(llvm::Module &m, llvm::CallSite &ci,
      ValueMap &map, llvm::Instruction **insert_after) const override;

  std::vector<llvm::Value *> getFreeData(llvm::Module &m, llvm::CallSite &ci,
      ValueMap &map,
      llvm::Instruction **insert_after) const override;

  StaticAllocInfo getAllocInfo(llvm::ImmutableCallSite &cs,
      ModInfo &info) const override;

  // Unknown functions cannot alloc, Universal Value covers this...
  bool canAlloc() const { return false; }
};

class ExtLibInfo {
 public:
  ExtLibInfo(ExtLibInfo &&) = default;
  ExtLibInfo(const ExtLibInfo &) = delete;

  ExtLibInfo &operator=(ExtLibInfo &&) = default;
  ExtLibInfo &operator=(const ExtLibInfo &) = delete;

  explicit ExtLibInfo(ModInfo &info);

  void init(const llvm::Module &m, ValueMap &map);
  void addGlobalConstraints(const llvm::Module &m, Cg &cg);

  const UnknownExtInfo UnknownFunction;

  bool isUnknownFunction(const ExtInfo &inf) const {
    return &inf == &UnknownFunction;
  }

  const ExtInfo &getInfo(const llvm::Function *fcn) const {
    if (fcn == nullptr) {
      return UnknownFunction;
    }

    auto &ret = getInfo(fcn->getName());
    if (isUnknownFunction(ret) && fcn->isDeclaration()) {
      llvm::dbgs() << "!!! Unknown external call: " << fcn->getName() << "\n";
    }
    return ret;
  }

  const ExtInfo &getInfo(const llvm::CallInst *ci) const {
    auto fcn = LLVMHelper::getFcnFromCall(ci);
    return getInfo(fcn);
  }

  const ExtInfo &getInfo(llvm::CallSite &cs) const {
    auto ci = cast<llvm::CallInst>(cs.getInstruction());
    return getInfo(ci);
  }

  const ExtInfo &getInfo(llvm::ImmutableCallSite &cs) const {
    auto ci = cast<llvm::CallInst>(cs.getInstruction());
    return getInfo(ci);
  }

 private:
  const ExtInfo &getInfo(const std::string &fcn) const {
    auto it = info_.find(fcn);

    // If we don't know
    if (it != std::end(info_)) {
      return *it->second;
    }

    // We don't have it in info_, still check partial matches
    for (auto &pr : matchInfo_) {
      if (fcn.find(pr.first) != std::string::npos) {
        llvm::dbgs() << "  have match on: " << pr.first << "\n";
        return *pr.second;
      }
    }

    return UnknownFunction;
  }

  std::unordered_map<std::string, std::unique_ptr<ExtInfo>> info_;
  // Partial matches
  std::vector<std::pair<std::string, std::unique_ptr<ExtInfo>>> matchInfo_;

  ModInfo &modInfo_;
};

#endif  // INCLUDE_EXTINFO_H_

