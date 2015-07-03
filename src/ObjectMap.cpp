/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/ObjectMap.h"

const ObjectMap::ObjID ObjectMap::NullValue =
    ObjectMap::ObjID(ObjectMap::ObjEnum::eNullValue);

const ObjectMap::ObjID ObjectMap::NullObjectValue =
    ObjectMap::ObjID(ObjectMap::ObjEnum::eNullObjectValue);

const ObjectMap::ObjID ObjectMap::IntValue =
    ObjectMap::ObjID(ObjectMap::ObjEnum::eIntValue);

const ObjectMap::ObjID ObjectMap::UniversalValue =
    ObjectMap::ObjID(ObjectMap::ObjEnum::eUniversalValue);

const ObjectMap::ObjID ObjectMap::PthreadSpecificValue =
    ObjectMap::ObjID(ObjectMap::ObjEnum::ePthreadSpecificValue);


ObjectMap::ObjectMap() {
  for (int32_t i = 0; i < eNumDefaultObjs; i++) {
    mapping_.push_back(nullptr);
  }
}
