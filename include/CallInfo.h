/*
 * Copyright (C) 2016 David Devecsery
 */

#ifndef INCLUDE_CALLINFO_H_
#define INCLUDE_CALLINFO_H_

#include <vector>

#include "llvm/IR/CallSite.h"
#include "llvm/IR/Instruction.h"

#include "include/util.h"
#include "include/ValueMap.h"

class Cg;
class CallInfo {
 public:
  typedef ValueMap::Id Id;

  CallInfo() = delete;
  /*
  CallInfo(const std::vector<Id> &args, Id ret, Id var_arg,
      const llvm::Instruction *ci = nullptr) :
    args_(args), ret_(ret), varArg_(var_arg), ci_(ci) { }
  */
  // Can be constructed as either callee or caller...
  CallInfo(Cg &cg, llvm::ImmutableCallSite &callee_site);
  CallInfo(Cg &cg, const llvm::Function *called_fcn);

  CallInfo(const CallInfo &) = default;
  CallInfo(CallInfo &&) = default;

  CallInfo &operator=(const CallInfo &) = default;
  CallInfo &operator=(CallInfo &&) = default;

  Id ret() const {
    return ret_;
  }

  const std::vector<Id> &args() const {
    return args_;
  }

  Id varArg() const {
    return varArg_;
  }

  const llvm::Instruction *ci() const {
    return ci_;
  }

  void remap(const util::ObjectRemap<Id> &mapper);
  void updateReps(const ValueMap &map);

 private:
  std::vector<Id> args_;
  Id ret_;

  Id varArg_;
  const llvm::Instruction *ci_ = nullptr;
};

#endif  // INCLUDE_CALLINFO_H_
