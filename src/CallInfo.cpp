/*
 * Copyright (C) 2016 David Devecsery
 */

#include "include/CallInfo.h"

#include "include/Cg.h"

CallInfo::CallInfo(Cg &cg, llvm::ImmutableCallSite &callee_site) :
      ci_(callee_site.getInstruction()) {
  // Populate args...
  for (auto it = callee_site.arg_begin(), en = callee_site.arg_end();
      it != en; ++it) {
    if (llvm::isa<llvm::PointerType>((*it)->getType())) {
      args_.push_back(cg.getDef(*it));
    } else {
      args_.push_back(ValueMap::IntValue);
    }
  }

  if (llvm::isa<llvm::PointerType>(ci_->getType())) {
    ret_ = cg.getDef(ci_);
  } else {
    ret_ = cg.vals().createPhonyID();
  }
}

CallInfo::CallInfo(Cg &cg, const llvm::Function *called_fcn) {
  // Populate args...
  for (auto it = called_fcn->arg_begin(), en = called_fcn->arg_end();
      it != en; ++it) {
    if (llvm::isa<llvm::PointerType>(it->getType())) {
      args_.push_back(cg.getDef(&(*it)));
    } else {
      args_.push_back(ValueMap::IntValue);
    }
  }

  ret_ = cg.vals().createPhonyID();
  if (called_fcn->getFunctionType()->isVarArg()) {
    varArg_ = cg.vals().createPhonyID();
  }
}


void CallInfo::remap(const util::ObjectRemap<Id> &mapper) {
  // args:
  for (auto &id : args_) { id = mapper[id]; }
  // ret:
  if (ret_ != Id::invalid()) {
    ret_ = mapper[ret_];
  }

  // varArg:
  if (varArg_ != Id::invalid()) {
    varArg_ = mapper[varArg_];
    assert(varArg_ != Id::invalid());
  }
}

void CallInfo::updateReps(const ValueMap &map) {
  // args:
  for (auto &id : args_) { id = map.getRep(id); }
  // ret:
  if (ret_ != Id::invalid()) {
    ret_ = map.getRep(ret_);
  }

  // varArg:
  if (varArg_ != Id::invalid()) {
    varArg_ = map.getRep(varArg_);
    assert(varArg_ != Id::invalid());
  }
}
