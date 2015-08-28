/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/ObjectMap.h"

#include <utility>

// FIXME: HAX to be removed later
ObjectMap *g_omap = nullptr;

const ObjectMap::ObjID ObjectMap::NullValue =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::eNullValue));

const ObjectMap::ObjID ObjectMap::NullObjectValue =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::eNullObjectValue));

const ObjectMap::ObjID ObjectMap::IntValue =
    ObjectMap::ObjID(static_cast<int32_t>(ObjectMap::ObjEnum::eIntValue));

const ObjectMap::ObjID ObjectMap::UniversalValue =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::eUniversalValue));

const ObjectMap::ObjID ObjectMap::PthreadSpecificValue =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::ePthreadSpecificValue));


ObjectMap::ObjectMap() {
  for (int32_t i = 0; i < static_cast<int32_t>(ObjEnum::eNumDefaultObjs);
      i++) {
    mapping_.push_back(nullptr);
  }

  if (g_omap == nullptr) {
    g_omap = this;
  }
}

std::pair<ObjectMap::Type, const llvm::Value *>
ObjectMap::getValueInfo(ObjectMap::ObjID id) const {
  if (id.val() < static_cast<int32_t>(ObjEnum::eNumDefaultObjs)) {
    return std::make_pair(Type::Special, nullptr);
  }

  auto val = __find_helper(id, idToVal_);
  if (val != nullptr) {
    return std::make_pair(Type::Value, val);
  }

  val = __find_helper(id, idToObj_);
  if (val != nullptr) {
    return std::make_pair(Type::Object, val);
  }

  val = __find_helper(id, idToRet_);
  if (val != nullptr) {
    return std::make_pair(Type::Return, val);
  }

  val = __find_helper(id, idToVararg_);
  if (val != nullptr) {
    return std::make_pair(Type::VarArg, val);
  }

  // ddevec -- This can happen with "temp" values
  // llvm_unreachable("Couldn't Find id!!");
  return std::make_pair(Type::Value, nullptr);
}

ObjectMap::ObjID ObjectMap::__const_node_helper(const llvm::Constant *C,
    ObjID (ObjectMap::*diff)(const llvm::Value *) const,
    ObjID nullv) const {
  if (llvm::isa<const llvm::ConstantPointerNull>(C) ||
      llvm::isa<const llvm::UndefValue>(C)) {
    return nullv;
  } else if (auto GV = llvm::dyn_cast<llvm::GlobalValue>(C)) {
    return (this->*diff)(GV);
  } else if (auto CE = llvm::dyn_cast<llvm::ConstantExpr>(C)) {
    switch (CE->getOpcode()) {
      case llvm::Instruction::GetElementPtr:
        return __const_node_helper(CE->getOperand(0), diff, nullv);
      case llvm::Instruction::IntToPtr:
        return UniversalValue;
      case llvm::Instruction::PtrToInt:
        return IntValue;
      case llvm::Instruction::BitCast:
        return __const_node_helper(CE->getOperand(0), diff, nullv);
      default:
        llvm::errs() << "Const Expr not yet handled: " << *CE << "\n";
        llvm_unreachable(0);
    }
  } else if (llvm::isa<llvm::ConstantInt>(C)) {
    return IntValue;
  } else {
    llvm::errs() << "Const Expr not yet handled: " << *C << "\n";
    llvm_unreachable("Unknown constant expr ptr");
  }
}

