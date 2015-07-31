/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/DUG.h"

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
const DUG::CFGid DUG::CFGInit =
  DUG::CFGid(static_cast<int32_t>(DUG::CFGEnum::CFGInit));
//}}}

// Constraint {{{
template<typename id_type>
Constraint<id_type>::Constraint(id_type s, id_type d, ConstraintType t) :
  Constraint(s, d, t, 0) { }

template<typename id_type>
Constraint<id_type>::Constraint(id_type d, id_type s, ConstraintType t,
      int32_t o) :
    SEGEdge<id_type>(EdgeKind::Constraint, s, d),
    type_(t), offs_(o) { }
//}}}

// DUG modification functions {{{
DUG::ConsID DUG::add(ConstraintType type, ObjID d, ObjID s, int o) {
  auto s_it = constraintGraph_.findNode(s);
  if (s_it == std::end(constraintGraph_)) {
    constraintGraph_.addNode<ConstraintNode>(s);
  }

  auto d_it = constraintGraph_.findNode(d);
  if (d_it == std::end(constraintGraph_)) {
    constraintGraph_.addNode<ConstraintNode>(d);
  }

  constraintGraph_.addEdge<Constraint<ObjID>>(s, d, type, o);

  return ConsID(s, d);
}

DUG::ObjID DUG::addNode(ObjectMap &omap) {
  auto id = omap.makeTempValue();

  // Put a new node on the back of nodes
  constraintGraph_.addNode<ConstraintNode>(id);

  return id;
}

bool DUG::removeUnusedFunction(DUG::ObjID fcn_id) {
  auto it = unusedFunctions_.find(fcn_id);

  if (it != std::end(unusedFunctions_)) {
    for (auto id : it->second) {
      constraintGraph_.removeEdge(id);
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

