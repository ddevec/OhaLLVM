/*
 * Copyright (C) 2016 David Devecsery
 */

#ifndef INCLUDE_DYNAMICINFO_H_
#define INCLUDE_DYNAMICINFO_H_

#include <cassert>
#include <cstdint>

#include <map>
#include <vector>

#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"

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
