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
#include "include/lib/CallContextPass.h"

class DynamicInfo {
 public:
  DynamicInfo(const UnusedFunctions &unused, const IndirFunctionInfo &indir,
      const CallContextLoader &call) :
    used_info(unused),
    indir_info(indir),
    call_info(call) { }
  const UnusedFunctions &used_info;
  const IndirFunctionInfo &indir_info;
  const CallContextLoader &call_info;
};

#endif // INCLUDE_DYNAMICINFO_H_
