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
// Typedefs for the HU Sparse Evaluation Graph {{{
struct HUData;
typedef SEG<DUG::ObjID, DUG::ObjID, HUData> HUSeg;
typedef HUSeg::Node HUNode;
typedef SparseBitVector<> Bitmap;
//}}}

// Simple helpers needed later {{{
static int getIdx(DUG::ObjID id) {
  return id.val();
}

static DUG::ObjID return_self(DUG::ObjID id) {
  return id;
}
//}}}

// Data for HU nodes {{{
struct HUData {
  //{{{
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

  bool indirect_ = false;

  Bitmap ptsto_;

  // Acutal HU visit impl
  static void visitHU(HUNode &node) {
    // Union our past ptsto sets
    auto &node_data = node.data();
    for (HUNode &pred : node.preds()) {
      auto &pred_data = pred.data();

      node_data.ptsto_ |= pred_data.ptsto_;
    }
  }
  //}}}
};
//}}}

// Debugging fcns {{{
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

// Helpers requiring HUNodes {{{
static void createGraph(const Constraint &con,
    HUNode &src, HUNode &dest,
    const ObjectMap &omap) {

  switch (con.type()) {
    case Constraint::Type::Store:
      // I think we just ignore stores
      break;
    case Constraint::Type::Load:
      // Add its own indirect ptsto
      if (con.offs() == 0) {
        dout << "Adding edge: " << idToString(con.src()) << " -> " <<
          idToString(con.dest()) << "\n";
        dest.addPred(src);
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
      if (omap.isObject(con.src())) {
        src.data().setIndirect();
      }
      break;
    case Constraint::Type::Copy:
      dout << "Adding edge: " << idToString(con.src()) << " -> " <<
        idToString(con.dest()) << "\n";
      dest.addPred(src);
      break;
    default:
      llvm_unreachable("Should never get here!\n");
  }
}
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

  auto init_fcn = [](HUNode &) { };

  auto add_node = [&omap](const Constraint &con, HUNode &src, HUNode &dest) {
    // Okay, now we create a graph node for each
    createGraph(con, src, dest, omap);
  };

  // Create the initial graph
  HUSeg seg(graph.constraint_begin(), graph.constraint_end(),
      return_self, init_fcn, add_node);

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
  std::for_each(seg.dfs_pred_begin(), seg.dfs_pred_end(),
      [](HUNode &n) {
    // Do the HU visit (pred collection) on each node
    HUData::visitHU(n);
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

  //  Used to map objs to the PE class
  std::map<DUG::ObjID, DUG::PEid> obj_to_pe;
  std::map<Bitmap, DUG::PEid, BitmapLT> pts_to_pe;

  // Now create the pointer equivalency ids
  for (auto &pair : seg) {
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

