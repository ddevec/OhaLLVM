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

const ObjectMap::ObjID ObjectMap::AggregateValue =
    ObjectMap::ObjID(static_cast<int32_t>(ObjectMap::ObjEnum::eAggregateValue));

const ObjectMap::ObjID ObjectMap::UniversalValue =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::eUniversalValue));

const ObjectMap::ObjID ObjectMap::PthreadSpecificValue =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::ePthreadSpecificValue));

const ObjectMap::ObjID ObjectMap::ArgvValue =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::eArgvValue));

const ObjectMap::ObjID ObjectMap::ArgvObjectValue =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::eArgvObjectValue));

const ObjectMap::ObjID ObjectMap::LocaleObject =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::eLocaleObject));

const ObjectMap::ObjID ObjectMap::CTypeObject =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::eCTypeObject));

const ObjectMap::ObjID ObjectMap::ErrnoObject =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::eErrnoObject));

const ObjectMap::ObjID ObjectMap::CLibObject =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::eCLibObject));

const ObjectMap::ObjID ObjectMap::TermInfoObject =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::eTermInfoObject));

ObjectMap::ObjectMap() {
  for (int32_t i = 0; i < static_cast<int32_t>(ObjEnum::eNumDefaultObjs);
      i++) {
    mapping_.push_back(nullptr);
  }
}

void ObjectMap::replaceDbgOmap(ObjectMap &omap) {
  g_omap = &omap;
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
    ObjID (ObjectMap::*diff)(const llvm::Value *),
    ObjID nullv) {
  if (llvm::isa<const llvm::ConstantPointerNull>(C) ||
      llvm::isa<const llvm::UndefValue>(C)) {
    return nullv;
  } else if (auto GV = dyn_cast<llvm::GlobalValue>(C)) {
    return (this->*diff)(GV);
  } else if (auto CE = dyn_cast<llvm::ConstantExpr>(C)) {
    switch (CE->getOpcode()) {
      case llvm::Instruction::GetElementPtr:
        {
          // Need to calc offset here...
          // But this encounters obj vs value issues...
          auto offs = getGEPOffs(*this, *CE);
          auto obj_id = __const_node_helper(CE->getOperand(0), diff, nullv);
          return getOffsID(obj_id, offs);
        }
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

