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
  const DUG::ObjID::base_type obj_id(DUG::ObjID id) {
    return id.val();
  }
  //}}}

  // Support for printing {{{
  static std::string idToString(DUG::ObjID id) {
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
    if (auto GV = dyn_cast<const GlobalValue>(val)) {
      ofil << GV->getName();
    } else if (auto F = dyn_cast<const Function>(val)) {
      ofil << F->getName();
    } else {
      ofil << *val;
    }
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
        assert(0 && "illegal constraint type");
        return "BLEH";
    }
  }

  static void printHeader(raw_ostream &ofil, DUG::ObjID id,
      const DUG &graph, const ObjectMap &omap) {
      auto pr = omap.getValueInfo(id);

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

  static void printDotHeader(raw_ostream &ofil) {
    ofil << "digraph graphname {\n";
  }

  static void printDotFooter(raw_ostream &ofil) {
    // We use endl here, so the file will force flush
    ofil << "}" << "\n";
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

  static void printConstraintNodeLinks(raw_ostream &ofil, const DUG &graph,
      const Constraint &con, const ObjectMap &omap) {
    // Okay... now we print the links...
    // auto id = con.getTarget();
    auto id = con.dest();
    std::string idNode(idToString(id));

    // auto id2 = con.targetIsDest() ? con.src() : con.dest();
    auto id2 = con.src();
    std::string idNode2(idToString(id2));

    auto consStr = getConsStr(con);

    ofil << "  " << idNode << " -> " << idNode2 <<
      " [label=\"" << consStr << "\"];\n";
  }
  //}}}
}  // end anon. namespace

Constraint::Constraint(Type t, ObjectMap::ObjID d, ObjectMap::ObjID s) :
  Constraint(t, d, s, 0) { }

Constraint::Constraint(Type t, ObjectMap::ObjID d, ObjectMap::ObjID s,
    int32_t o) : type_(t), dest_(d), src_(s), offs_(o) { }

void DUG::prepare(const ObjectMap &omap) {
  // Create a node per constraint (initially)
  nodes_.resize(omap.size());
}

void DUG::add(Constraint::Type type, ObjID d, ObjID s, int o) {
  constraints_.emplace_back(type, d, s, o);
}

DUG::ObjID DUG::addNode(ObjectMap &omap) {
  auto id = omap.makeTempValue();

  // Put a new node on the back of nodes
  nodes_.emplace_back();

  assert(ObjID(nodes_.size()-1) == id);

  return id;
}

void DUG::addIndirectCall(ObjID id, const Value *val) {
  // Indirect graph...
  indirectCalls_.emplace_back(val, id);
}

void DUG::addIndirect(const Value *val, Constraint::Type type,
    ObjID d, ObjID s, int32_t o) {
  addIndirectCall(d, val);

  add(type, d, s, o);
}

void DUG::associateNode(ObjID id, const Value *val) {
  assert(obj_id(id) < nodes_.size());
  DUGNode &node = nodes_[obj_id(id)];

  node.setValue(val);
}

void DUG::printDotConstraintGraph(const std::string &graphname,
    const ObjectMap &omap) const {
  // Okay, we need to print out some dot nodes
  std::ofstream ostr(graphname, std::ofstream::out);
  // We'll use an llvm raw_ostream adapter
  raw_os_ostream ofil(ostr);

  printDotHeader(ofil);

  std::set<ObjID> seen;
  std::for_each(constraint_begin(), constraint_end(),
      [this, &ofil, &omap, &seen](const Constraint &con) {
    printConstraintNodeHeader(ofil, *this, con, omap, seen);
  });

  ofil << "\n";

  std::for_each(constraint_begin(), constraint_end(),
      [this, &ofil, &omap](const Constraint &con) {
    printConstraintNodeLinks(ofil, *this, con, omap);
  });

  printDotFooter(ofil);
}

