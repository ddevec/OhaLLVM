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
template<typename idT>
static std::string idToString(idT id) {
  auto val = id.val();

  if (val == 0) {
    return "a";
  }

  int len = 0;

  auto val_bkp = val;
  while (val_bkp != 0) {
    ++len;
    val_bkp /= 10;
  }

  std::string ret(len, 'a');

  for (int i = 0; i < len; i++) {
    char digit = val % 10;
    val /= 10;

    ret.replace(i, 1, 1, 'a' + digit);
  }

  return ret;
}

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

static const std::string getConsStr(const Constraint &cons) {
  switch (cons.type()) {
    case Constraint::Type::Copy:
      return "copy";
    case Constraint::Type::AddressOf:
      return "addr_of";
    case Constraint::Type::Load:
      return "load";
    case Constraint::Type::Store:
      return "store";
    default:
      llvm_unreachable("Constraint with unexpected type!");
      return "BLEH";
  }
}

template<typename idT>
static void printHeader(raw_ostream &ofil, idT id,
    const DUG &, const ObjectMap &omap) {
  auto pr = omap.getValueInfo(id);
  // If pr is a temp node, don't print it
  if (pr.second == nullptr) {
    return;
  }

  std::string idNode = idToString(id);

  // Need a raw_os_ostream to print a value...
  ofil << "  " << idNode << " [label=\"";
  if (pr.first != ObjectMap::Type::Special) {
    printVal(ofil, pr.second);
  } else {
    printSpecial(ofil, id);
  }
  ofil << "\"" << getFormatStr(pr.first) << "];\n";
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

static void printDotHeader(raw_ostream &ofil) {
  ofil << "digraph graphname {\n";
}

static void printDotFooter(raw_ostream &ofil) {
  // We use endl here, so the file will force flush
  ofil << "}" << "\n";
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

static void printPENodeHeader(raw_ostream &ofil, const DUG &graph,
    DUG::PEid peid, const std::set<DUG::ObjID> &ids, const ObjectMap &omap) {
  printMultiHeader(ofil, peid, ids, graph, omap);
}


static void printConstraintNodeHeader(raw_ostream &ofil, const DUG &graph,
    const Constraint &con, const ObjectMap &omap,
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

static DUG::ObjID getTarget(const Constraint &con) {
  switch (con.type()) {
    case Constraint::Type::Copy:
      return con.dest();
    case Constraint::Type::AddressOf:
      return con.src();
    case Constraint::Type::Load:
      return con.dest();
    case Constraint::Type::Store:
      return con.dest();
    default:
      llvm_unreachable("Unhandled constraint");
  }
}

static DUG::ObjID getOrigin(const Constraint &con) {
  switch (con.type()) {
    case Constraint::Type::Copy:
      return con.src();
    case Constraint::Type::AddressOf:
      return con.dest();
    case Constraint::Type::Load:
      return con.src();
    case Constraint::Type::Store:
      return con.src();
    default:
      llvm_unreachable("Unhandled constraint");
  }
}

static void printConstraintNodeLinks(raw_ostream &ofil, const DUG &,
    const Constraint &con, const ObjectMap &) {
  if (con.isNoop()) {
    return;
  }
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

static void printPENodeLinks(raw_ostream &ofil, const DUG &graph,
    const Constraint &con, const ObjectMap &) {
  if (con.isNoop()) {
    return;
  }
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
Constraint::Constraint(Type t, ObjectMap::ObjID d, ObjectMap::ObjID s) :
  Constraint(t, d, s, 0) { }

Constraint::Constraint(Type t, ObjectMap::ObjID d, ObjectMap::ObjID s,
    int32_t o) : type_(t), dest_(d), src_(s), offs_(o) { }
//}}}


void DUG::prepare(const ObjectMap &omap) {
  // Create a node per constraint (initially)
  nodes_.resize(omap.size());
}

DUG::ConsID DUG::add(Constraint::Type type, ObjID d, ObjID s, int o) {
  constraints_.emplace_back(type, d, s, o);
  return ConsID(constraints_.size()-1);
}

DUG::ObjID DUG::addNode(ObjectMap &omap) {
  auto id = omap.makeTempValue();

  // Put a new node on the back of nodes
  nodes_.emplace_back();

  assert(ObjID(nodes_.size()-1) == id);

  return id;
}

void DUG::addIndirectCall(ObjID id, llvm::Instruction *inst) {
  // Indirect graph...
  indirectCalls_.emplace_back(inst, id);
}

void DUG::associateNode(ObjID id, const Value *val) {
  assert(static_cast<size_t>(obj_id(id)) < nodes_.size());
  DUGNode &node = nodes_[obj_id(id)];

  node.setValue(val);
}

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
//}}}

