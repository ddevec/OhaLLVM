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

using namespace llvm;  // NOLINT


// Anon namespace
namespace {
// General Helper fcns {{{
DUG::ObjID::base_type obj_id(DUG::ObjID id) {
  return id.val();
}
//}}}

// Support for printing {{{
static void printVal(raw_ostream &ofil, const Value *val) {
  if (val == nullptr) {
    ofil << "temp node";
  } else if (auto GV = dyn_cast<const GlobalValue>(val)) {
    ofil << GV->getName();
  } else if (auto F = dyn_cast<const Function>(val)) {
    ofil << F->getName();
  } else {
    ofil << *val;
  }
}

static std::string getFormatStr(DUG::PEid) {
  return " shape=box";
}

__attribute__((unused))
static std::string getFormatStr(ObjectMap::Type type) {
  switch (type) {
    case ObjectMap::Type::Special:
      return " shape=box color=red";
    case ObjectMap::Type::Value:
      return "";
    case ObjectMap::Type::Object:
      return " shape=box";
    case ObjectMap::Type::Return:
      return " color=blue";
    case ObjectMap::Type::VarArg:
      return " color=red";
    default:
      llvm_unreachable("Shouldn't have uncovered format case");
  }
}

static void printSpecial(raw_ostream &ofil, DUG::ObjID id) {
  if (id == ObjectMap::NullValue) {
    ofil << "NullValue";
  } else if (id == ObjectMap::NullObjectValue) {
    ofil << "NullObjectValue";
  } else if (id == ObjectMap::IntValue) {
    ofil << "IntValue";
  } else if (id == ObjectMap::UniversalValue) {
    ofil << "UniversalValue";
  } else if (id == ObjectMap::UniversalValue) {
    ofil << "PthreadSpecificValue";
  } else {
    llvm_unreachable("Shouldn't have unknown value here!");
  }
}

static const std::string getConsStr(const Constraint<DUG::ObjID> &cons) {
  switch (cons.type()) {
    case ConstraintType::Copy:
      return "copy";
    case ConstraintType::AddressOf:
      return "addr_of";
    case ConstraintType::Load:
      return "load";
    case ConstraintType::Store:
      return "store";
    default:
      llvm_unreachable("Constraint with unexpected type!");
      return "BLEH";
  }
}

template<typename idT>
static void printHeader(raw_ostream &, idT id,
    const DUG &, const ObjectMap &omap) {
  auto pr = omap.getValueInfo(id);
  // If pr is a temp node, don't print it
  if (pr.second == nullptr) {
    return;
  }

  std::string idNode = idToString(id);

  dout << "got val info type: " << static_cast<int>(pr.first) << "\n";
  dout << "For reference, special is : " <<
    static_cast<int>(ObjectMap::Type::Special) << "\n";

  // Need a raw_os_ostream to print a value...
  /*
  ofil << "  " << idNode << " [label=\"";
  auto pr = omap.getValueInfo(id);
  if (pr.first != ObjectMap::Type::Special) {
    printVal(ofil, pr.second);
  } else {
    dout << "Printing special node: " << idNode << "\n";
    printSpecial(ofil, id);
  }
  ofil << "\"" << getFormatStr(pr.first) << "];\n";
  */
}

static void printMultiHeader(raw_ostream &ofil,
    DUG::PEid peid, const std::set<DUG::ObjID> &ids,
    const DUG &, const ObjectMap &omap) {
  std::string idNode = idToString(peid);

  // Need a raw_os_ostream to print a value...
  ofil << "  " << idNode << " [label=\"";
  // Make an iterator from the start, then another indicating the next
  for (auto nit = std::begin(ids), en = std::end(ids), it = nit++; it != en;
      ++it) {
    auto pr = omap.getValueInfo(*it);
    // If pr is a temp node, don't print it
    if (pr.second == nullptr) {
      continue;
    }
    if (pr.first != ObjectMap::Type::Special) {
      printVal(ofil, pr.second);
    } else {
      printSpecial(ofil, *it);
    }
    // Print a newline after each value, except the last
    if (nit != en) {
      ofil << "\n";
      ++nit;
    }
  }

  ofil << "\"" << getFormatStr(peid) << "];\n";
}

static DUG::PEid getPEid(DUG::ObjID id, const DUG &graph) {
  DUG::PEid ret = DUG::PEid(id.val() + (1<<30));
  auto pe = graph.getPE(id);
  if (pe.valid()) {
    ret = pe;
    assert(pe.val() < 1<<30 &&
        "Fetched PE larger than expected");
  }

  return ret;
}

// FIXME: replace and remove
__attribute__((unused))
static void printPENodeHeader(raw_ostream &ofil, const DUG &graph,
    DUG::PEid peid, const std::set<DUG::ObjID> &ids, const ObjectMap &omap) {
  printMultiHeader(ofil, peid, ids, graph, omap);
}


// FIXME: Replace and remove
__attribute__((unused))
static void printConstraintNodeHeader(raw_ostream &ofil, const DUG &graph,
    const Constraint<DUG::ObjID> &con, const ObjectMap &omap,
    std::set<DUG::ObjID> &seen) {
  auto id = con.getTarget();
  auto id2 = con.targetIsDest() ? con.src() : con.dest();
  if (seen.count(id) == 0) {
    seen.insert(id);

    printHeader(ofil, id, graph, omap);
  }

  if (seen.count(id2) == 0) {
    seen.insert(id2);
    printHeader(ofil, id2, graph, omap);
  }
}

static DUG::ObjID getTarget(const Constraint<DUG::ObjID> &con) {
  switch (con.type()) {
    case ConstraintType::Copy:
      return con.dest();
    case ConstraintType::AddressOf:
      return con.src();
    case ConstraintType::Load:
      return con.dest();
    case ConstraintType::Store:
      return con.dest();
    default:
      llvm_unreachable("Unhandled constraint");
  }
}

static DUG::ObjID getOrigin(const Constraint<DUG::ObjID> &con) {
  switch (con.type()) {
    case ConstraintType::Copy:
      return con.src();
    case ConstraintType::AddressOf:
      return con.dest();
    case ConstraintType::Load:
      return con.src();
    case ConstraintType::Store:
      return con.src();
    default:
      llvm_unreachable("Unhandled constraint");
  }
}

__attribute__((unused))
static void printConstraintNodeLinks(raw_ostream &ofil, const DUG &,
    const Constraint<DUG::ObjID> &con, const ObjectMap &) {
  /*
  if (con.isNoop()) {
    return;
  }
  */
  // Okay... now we print the links...
  // This is to decide on the logical arrow direction
  auto id = getTarget(con);
  std::string idNode(idToString(id));

  // This is to decide on the logical arrow direction
  auto id2 = getOrigin(con);
  std::string idNode2(idToString(id2));

  auto consStr = getConsStr(con);

  ofil << "  " << idNode2 << " -> " << idNode <<
    " [label=\"" << consStr << "\"];\n";
}

__attribute__((unused))
static void printPENodeLinks(raw_ostream &ofil, const DUG &graph,
    const Constraint<DUG::ObjID> &con, const ObjectMap &) {
  /*
  if (con.isNoop()) {
    return;
  }
  */
  // Okay... now we print the links...
  // This is to decide on the logical arrow direction
  auto id = getPEid(getTarget(con), graph);
  std::string idNode(idToString(id));

  // This is to decide on the logical arrow direction
  auto id2 = getPEid(getOrigin(con), graph);
  std::string idNode2(idToString(id2));

  auto consStr = getConsStr(con);

  ofil << "  " << idNode2 << " -> " << idNode <<
    " [label=\"" << consStr << "\"];\n";
}
//}}}
}  // end anon. namespace

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

DUG::ConsID DUG::add(ConstraintType type, ObjID d, ObjID s, int o) {
  auto s_it = constraintGraph_.findNode(s);
  if (s_it == std::end(constraintGraph_)) {
    constraintGraph_.addNode<ConstraintNode>(s);
  }

  auto d_it = constraintGraph_.findNode(d);
  if (d_it == std::end(constraintGraph_)) {
    constraintGraph_.addNode<ConstraintNode>(d);
  }

  /*
  llvm::dbgs() << "Adding edge ( " << s << ", " << d << " ) for con type: ";
  switch (type) {
    case ConstraintType::Load:
      llvm::dbgs() << "load";
      break;
    case ConstraintType::Store:
      llvm::dbgs() << "store";
      break;
    case ConstraintType::AddressOf:
      llvm::dbgs() << "address_of";
      break;
    case ConstraintType::Copy:
      llvm::dbgs() << "copy";
      break;
  }
  llvm::dbgs() << "\n";
  */
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

/*
void DUG::associateNode(ObjID id, ObjID val) {
  //assert(static_cast<size_t>(obj_id(id)) < nodes_.size());
  ConstraintNode &node =
    constraintGraph_.getNode(id).data();

  node.id = val;
}
*/

/*
// Debug Printing functions {{{
void DUG::printDotConstraintGraph(const std::string &graphname,
    const ObjectMap &omap) const {
  // Okay, we need to print out some dot nodes
  std::ofstream ostr(graphname, std::ofstream::out);
  // We'll use an llvm raw_ostream adapter
  raw_os_ostream ofil(ostr);

  printDotHeader(ofil);

  std::set<ObjID> seen;
  std::for_each(constraint_begin(), constraint_end(),
      [this, &ofil, &omap, &seen] (const Constraint &con) {
    printConstraintNodeHeader(ofil, *this, con, omap, seen);
  });

  ofil << "\n";

  std::for_each(constraint_begin(), constraint_end(),
      [this, &ofil, &omap] (const Constraint &con) {
    printConstraintNodeLinks(ofil, *this, con, omap);
  });

  printDotFooter(ofil);
}

void DUG::printDotPEGraph(const std::string &graphname,
    const ObjectMap &omap) const {
  // Okay, we need to print out some dot nodes
  std::ofstream ostr(graphname, std::ofstream::out);
  // We'll use an llvm raw_ostream adapter
  raw_os_ostream ofil(ostr);

  printDotHeader(ofil);

  // Collect all of the nodes grouped together
  std::map<PEid, std::set<ObjID>> id_map;
  std::for_each(constraint_begin(), constraint_end(),
      [this, &ofil, &omap, &id_map] (const Constraint &con) {
    // Okay, get each constraint part, and make up our id list
    auto id1 = con.src();
    auto id2 = con.dest();

    id_map[getPEid(id1, *this)].insert(id1);
    id_map[getPEid(id2, *this)].insert(id2);
  });

  std::set<PEid> seen;
  std::for_each(std::begin(id_map), std::end(id_map),
      [this, &ofil, &omap, &seen]
      (const std::pair<PEid, const std::set<ObjID>&> &pr) {
    printPENodeHeader(ofil, *this, pr.first, pr.second, omap);
  });

  std::for_each(constraint_begin(), constraint_end(),
      [this, &ofil, &omap] (const Constraint &con) {
    printPENodeLinks(ofil, *this, con, omap);
  });

  printDotFooter(ofil);
}
*/
//}}}

