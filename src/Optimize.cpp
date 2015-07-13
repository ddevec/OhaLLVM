/*
 * Copyright (C) 2015 David Devecsery
 */

// Turn debugging on/off for this file
// #define SPECSFS_DEBUG

#include <cassert>
#include <cstdint>

#include <limits>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "include/Debug.h"

#include "include/SEG.h"
#include "include/SpecSFS.h"
#include "include/util.h"

#include "llvm/ADT/SparseBitVector.h"

using namespace llvm;  // NOLINT

namespace {

struct HUEdge;

// Simple helpers needed later {{{
static int getIdx(DUG::ObjID id) {
  return id.val();
}
//}}}

typedef SparseBitVector<> Bitmap;

// Data for HU nodes {{{
struct HUData {
  //{{{
  HUData() = default;
  explicit HUData(const SEGNodeEmpty &) { }

  void addPtsTo(DUG::ObjID id) {
    ptsto_.set(getIdx(id));
  }

  const Bitmap &ptsto() const {
    return ptsto_;
  }

  bool indirect() const {
    return indirect_;
  }

  void setIndirect() {
    indirect_ = true;
  }

  void print_label(llvm::raw_ostream &ofil,
      DUG::ObjID id, const ObjectMap &omap) const {
    auto pr = omap.getValueInfo(id);
    if (pr.first != ObjectMap::Type::Special) {
      const llvm::Value *val = pr.second;
      if (val == nullptr) {
        ofil << "temp node";
      } else if (auto GV = dyn_cast<const llvm::GlobalValue>(val)) {
        ofil <<  GV->getName();
      } else if (auto F = dyn_cast<const llvm::Function>(val)) {
        ofil <<  F->getName();
      } else {
        ofil << *val;
      }
    } else {
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
  }

  bool indirect_ = false;

  Bitmap ptsto_;
  //}}}
};


struct HUEdge {
  //{{{
 public:
    template<typename graph_type>
    HUEdge(graph_type *graph, const Constraint &con) :
        src_(con.src()), dest_(con.dest()), type_(con.type()) {
      auto &dest = graph->getNode(con.dest());

      switch (con.type()) {
        case Constraint::Type::Store:
          // I think we just ignore stores
          break;
        case Constraint::Type::Load:
          // Add its own indirect ptsto
          if (con.offs() == 0) {
            dout << "Adding edge: " << idToString(con.src()) << " -> " <<
              idToString(con.dest()) << "\n";
            dest.addPred(con.src());
          } else {
            dout << "Seting: " << idToString(con.src()) << " to indirect\n";
            dest.data().setIndirect();
          }
          break;
        case Constraint::Type::AddressOf:
          dout << "Seting: " << idToString(con.dest()) << "to indirect\n";
          dout << "Adding ptsto: " << idToString(con.src()) << " to ptsto of: "
            << idToString(con.dest()) << "\n";
          dest.data().setIndirect();
          dest.data().addPtsTo(con.src());
          /*
          if (omap.isObject(con.src())) {
            src.data().setIndirect();
          }
          */
          break;
        case Constraint::Type::Copy:
          dout << "Adding edge: " << idToString(con.src()) << " -> " <<
            idToString(con.dest()) << "\n";
          dest.addPred(con.src());
          break;
        default:
          llvm_unreachable("Should never get here!\n");
      }
    }

    DUG::ObjID src() const {
      return src_;
    }

    DUG::ObjID dest() const {
      return dest_;
    }

    void print_label(llvm::raw_ostream &ofil, const ObjectMap &) const {
      switch (type_) {
        case Constraint::Type::Copy:
          ofil << "copy";
          break;
        case Constraint::Type::AddressOf:
          ofil << "addr_of";
          break;
        case Constraint::Type::Load:
          ofil << "load";
          break;
        case Constraint::Type::Store:
          ofil << "store";
          break;
        default:
          llvm_unreachable("Constraint with unexpected type!");
          ofil << "BLEH";
      }
    }

 private:
    //{{{
    DUG::ObjID src_;
    DUG::ObjID dest_;
    Constraint::Type type_;
    //}}}
  //}}}
};

//}}}

// Typedefs for the HU Sparse Evaluation Graph {{{
struct HUData;
typedef SEG<DUG::ObjID, HUData, HUEdge> HUSeg;
typedef HUSeg::Node HUNode;
//}}}

// Acutal HU visit impl {{{
static void visitHU(HUSeg &seg, HUNode &node) {
  // Union our past ptsto sets
  auto &node_data = node.data();
  for (DUG::ObjID node_id : node.preds()) {
    HUNode &pred = seg.getNode(node_id);
    auto &pred_data = pred.data();

    node_data.ptsto_ |= pred_data.ptsto_;
  }
}
//}}}



// Helper Functions {{{
static DUG::PEid getNextPE() {
  static UniqueIdentifier<int32_t> PENum;
  return DUG::PEid(PENum.next());
}


// Comparrison fcn for bitmaps
struct BitmapLT {
  bool operator() (const Bitmap &b1, const Bitmap &b2) {
    auto it1 = std::begin(b1);
    auto it2 = std::begin(b2);
    auto en1 = std::end(b1);
    auto en2 = std::end(b2);

    // True if any element b1 < b2
    for (; it1 != en1 && it2 != en2; ++it1, ++it2) {
      // if it1 < it2 : b1 < b2
      if (*it1 < *it2) {
        return true;
      // If it1 > it2 : b1 > b2
      } else if (*it1 > *it2) {
        return false;
      }
      // Otherwise, they are equal, try the next element
    }

    // If they are equivalent but b1 is longer b1 is less than it b2
    if (it1 != en1) {
      return true;
    }

    return false;
  }
};
//}}}

}  // End anon namespace

// optimizeConstraints {{{
bool SpecSFS::optimizeConstraints(DUG &graph, const ObjectMap &omap) {
  // Okay, we run HU here, over the constraints
  //
  // The algorithm is listed as:
  //  1) Create initial ptsto set for each node
  //  2) In topological order (depth first) for each node:
  //          S = {y:y->x} U {x}. then
  //          pts(x) = for all y in S: U pts(y)
  //  3) Assign labels, s.t.:
  //      for all x,y in V:
  //        pts(x) == pts(y) <-> pe(x) = pe(y)
  //  where pts is the ptsto set for a variable
  //  pe is the pointer equivalence
  //  V is the set of vertecies in the graph

  // Create the initial graph
  HUSeg huSeg(graph.getConstraintGraph());

  if_debug(
    for (auto &pair : nodes) {
      dout << "initial ptsto for node " << idToString(pair.second.obj()) <<
        " is:";
      for (auto int_id : pair.second.ptsto()) {
        dout << " " << idToString(DUG::ObjID(int_id));
      }
      dout << "\n";
    });

  // Now iterate in DFS order
  std::for_each(huSeg.dfs_pred_begin(), huSeg.dfs_pred_end(),
      [&huSeg](DUG::ObjID node_id) {
    // Do the HU visit (pred collection) on each node
    visitHU(huSeg, huSeg.getNode(node_id));
  });

  if_debug(
    for (auto &pair : nodes) {
      dout << "ptsto after HU for node " << idToString(pair.second.obj()) <<
        "is:";
      for (auto int_id : pair.second.ptsto()) {
        dout << " " << idToString(DUG::ObjID(int_id));
      }
      dout << "\n";
    });

  huSeg.printDotFile("optimize.dot", omap);

  //  Used to map objs to the PE class
  std::map<DUG::ObjID, DUG::PEid> obj_to_pe;
  std::map<Bitmap, DUG::PEid, BitmapLT> pts_to_pe;

  // Now create the pointer equivalency ids
  for (auto &pair : huSeg) {
    auto &node = pair.second;

    auto it = pts_to_pe.find(node.data().ptsto());

    DUG::PEid pe;
    if (node.data().indirect()) {
      pe = getNextPE();
      dout << "pe for indirect node: " << pe.val() << "\n";
    } else if (it == std::end(pts_to_pe)) {
      pe = getNextPE();
      pts_to_pe.insert(std::make_pair(node.data().ptsto(), pe));
      dout << "pe for ptsto: " << pe.val() << "\n";
    } else {
      pe = it->second;
      dout << "pe gathered: " << pe.val() << "\n";
    }

    obj_to_pe.insert(std::make_pair(pair.first, pe));
  }

  if_debug(
    std::map<DUG::PEid, std::vector<DUG::ObjID>> pe_to_obj;
    for (auto &pair : obj_to_pe) {
      pe_to_obj[pair.second].push_back(pair.first);
    }

    for (auto &pair : pe_to_obj) {
      dout << "id remapping is now PE (" << pair.first.val() << "): "
        << idToString((pair.first)) << " is:";
      for (auto obj_id : pair.second) {
        dout << " " << idToString(obj_id);
      }
      dout << "\n";
    });

  // Export this data into the graph
  graph.setupPE(obj_to_pe);

  return false;
}
//}}}

