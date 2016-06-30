/*
 * Copyright (C) 2016 David Devecsery
 */

#ifndef INCLUDE_DYNAMICINFO_H_
#define INCLUDE_DYNAMICINFO_H_

#include <cassert>
#include <cstdint>

#include <map>
#include <vector>

#include "llvm/Constants.h"
#include "llvm/Function.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Module.h"

#include "include/DynamicInfo.h"
#include "include/ValueMap.h"
#include "include/CallInfo.h"
#include "include/lib/IndirFcnTarget.h"
#include "include/lib/UnusedFunctions.h"

class DynamicInfo {
 public:
  DynamicInfo(const UnusedFunctions &unused) : used_info(unused) { }
  const UnusedFunctions &used_info;
};

#endif // INCLUDE_DYNAMICINFO_H_
