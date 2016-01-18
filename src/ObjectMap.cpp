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

const ObjectMap::ObjID ObjectMap::AggregateValue =
    ObjectMap::ObjID(static_cast<int32_t>(ObjectMap::ObjEnum::eAggregateValue));

const ObjectMap::ObjID ObjectMap::PthreadSpecificValue =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::ePthreadSpecificValue));

const ObjectMap::ObjID ObjectMap::ArgvValue =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::eArgvValue));

const ObjectMap::ObjID ObjectMap::ArgvValueObject =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::eArgvValueObject));

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

const ObjectMap::ObjID ObjectMap::ArgvObject =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::eArgvObject));

const ObjectMap::ObjID ObjectMap::ArgvObjectObject =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::eArgvObjectObject));

const ObjectMap::ObjID ObjectMap::StdIOValue =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::eStdIOValue));

const ObjectMap::ObjID ObjectMap::IoctlValue =
    ObjectMap::ObjID(
        static_cast<int32_t>(ObjectMap::ObjEnum::eIoctlValue));

ObjectMap::ObjectMap() {
  for (int32_t i = 0; i < static_cast<int32_t>(ObjEnum::eNumDefaultObjs);
      i++) {
    mapping_.push_back(nullptr);
    reps_.add();
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

