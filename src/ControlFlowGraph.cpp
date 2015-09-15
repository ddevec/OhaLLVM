/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/ControlFlowGraph.h"

#include <cstdint>

#include <string>
#include <iostream>
#include <fstream>
#include <map>
#include <set>
#include <utility>

#define SPECSFS_DEBUG
#include "include/Debug.h"
#include "include/ObjectMap.h"

#include "llvm/Function.h"
#include "llvm/Support/raw_os_ostream.h"

// DUG Static variable(s) {{{
const CFG::CFGid CFG::CFGInit =
  CFG::CFGid(static_cast<int32_t>(CFG::CFGEnum::CFGInit));
const CFG::CFGid CFG::CFGArgvBegin =
  CFG::CFGid(static_cast<int32_t>(CFG::CFGEnum::CFGArgvBegin));
const CFG::CFGid CFG::CFGArgvEnd =
  CFG::CFGid(static_cast<int32_t>(CFG::CFGEnum::CFGArgvEnd));
//}}}

// DUG modification functions {{{
bool CFG::removeUnusedFunction(ConstraintGraph &cg,
    ObjectMap::ObjID fcn_id) {
  auto it = unusedFunctions_.find(fcn_id);

  if (it != std::end(unusedFunctions_)) {
    for (auto id : it->second) {
      cg.removeConstraint(id);
    }

    unusedFunctions_.erase(fcn_id);

    // Successful removal
    return true;
  } else {
    // Unsuccessful removal
    return false;
  }
}
//}}}

