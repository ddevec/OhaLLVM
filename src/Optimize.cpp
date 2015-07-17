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

// #define SPECSFS_DEBUG
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
struct HUNode : public SEGNode<DUG::ObjID> {
  //{{{
  HUNode(int32_t nodenum, DUG::ObjID id) :
    SEGNode<DUG::ObjID>(NodeKind::HUNode, nodenum, id) { }

  template <typename id_converter>
  HUNode(int32_t nodenum, DUG::ObjID id, const SEGNode<DUG::ObjID> &nd,
        id_converter convert) :
      SEGNode<DUG::ObjID>(NodeKind::HUNode, nodenum, id, nd, convert) { }

  void addPtsTo(DUG::ObjID id) {
    ptsto_.set(getIdx(id));
  }

  const Bitmap &ptsto() const {
    return ptsto_;
  }

  Bitmap &ptsto() {
    return ptsto_;
  }

  bool indirect() const {
    return indirect_;
  }

  void setIndirect() {
    indirect_ = true;
  }

  void print_label(llvm::raw_ostream &ofil,
      const ObjectMap &omap) const override {
    DUG::ObjID id = SEGNode<DUG::ObjID>::id();
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

  // For LLVM RTTI {{{
  static bool classof(const SEGNode<DUG::ObjID> *n) {
    return n->getKind() == NodeKind::HUNode;
  }
  //}}}

  bool indirect_ = false;

  Bitmap ptsto_;
  //}}}
};

// FIXME: HAX to be removed later
ObjectMap *g_omap;

struct HUEdge : public SEGEdge<DUG::ObjID> {
  //{{{
 public:
    // Construction from Constraint {{{
    HUEdge(DUG::ObjID src, DUG::ObjID dest, SEG<DUG::ObjID> &graph,
          const Constraint<DUG::ObjID> &con) :
        SEGEdge(EdgeKind::HUEdge, src, dest),
        type_(con.type()), offs_(con.offs()) {
      // Get our two HU nodes
      auto &dest_node = llvm::cast<HUNode>(graph.getNode(dest));
      auto &src_node = llvm::cast<HUNode>(graph.getNode(src));

      // Add constraints
      switch (type()) {
        case ConstraintType::Store:
          // I think we just ignore stores
          break;
        case ConstraintType::Load:
          // Add its own indirect ptsto
          if (offs() == 0) {
            if_debug(
              dout << "Adding edge: " << idToString(src) << " -> " <<
                idToString(dest) << "\n";
              dout << "Adding pred to: ";
              src_node.print_label(dout, *g_omap);
              dout << "\n");

            src_node.addPred(dest);
          } else {
            dout << "Setting: " << idToString(src) << " to indirect\n";
            src_node.setIndirect();
          }
          break;
        case ConstraintType::AddressOf:
          if_debug(
            dout << "Setting: " << idToString(dest) << " to indirect\n";
            dout << "Adding ptsto: " << idToString(dest) <<
                " to ptsto of: " << idToString(src) << "\n");

          dest_node.setIndirect();
          src_node.addPtsTo(dest);

          if (g_omap->isObject(src)) {
            src_node.setIndirect();
          }

          break;
        case ConstraintType::Copy:
          if_debug(
            dout << "Adding edge: " << idToString(src) << " -> " <<
              idToString(dest) << "\n";
            dout << "Adding pred (copy) to: ";
            src_node.print_label(dout, *g_omap);
            dout << "\n");
          dest_node.addPred(src);
          break;
        default:
          llvm_unreachable("Should never get here!\n");
      }
    }

    /*
    template <typename id_converter>
    HUEdge(DUG::ObjID src, DUG::ObjID dest, const SEGEdge<DUG::ObjID> &node,
        SEG<DUG::ObjID> &graph, id_converter) :
        SEGEdge(EdgeKind::HUEdge, src, dest),
        type_(llvm::cast<Constraint<DUG::ObjID>>(node).type()),
        offs_(llvm::cast<Constraint<DUG::ObjID>>(node).offs()) {
      // Get our two HU nodes
      auto &dest_node = llvm::cast<HUNode>(graph.getNode(dest));
      auto &src_node = llvm::cast<HUNode>(graph.getNode(src));

      // Add constraints
      switch (type()) {
        case ConstraintType::Store:
          // I think we just ignore stores
          break;
        case ConstraintType::Load:
          // Add its own indirect ptsto
          if (offs() == 0) {
            if_debug(
              dout << "Adding edge: " << idToString(src) << " -> " <<
                idToString(dest) << "\n";
              dout << "Adding pred to: ";
              src_node.print_label(dout, *g_omap);
              dout << "\n");

            // src_node.addPred(dest());
          } else {
            dout << "Setting: " << idToString(src()) << " to indirect\n";
            src_node.setIndirect();
          }
          break;
        case ConstraintType::AddressOf:
          if_debug(
            dout << "Setting: " << idToString(dest()) << " to indirect\n";
            dout << "Adding ptsto: " << idToString(dest()) <<
                " to ptsto of: " << idToString(src()) << "\n");

          dest_node.setIndirect();
          src_node.addPtsTo(dest);

          if (g_omap->isObject(src())) {
            src_node.setIndirect();
          }

          break;
        case ConstraintType::Copy:
          if_debug(
            dout << "Adding edge: " << idToString(src) << " -> " <<
              idToString(dest) << "\n";
            dout << "Adding pred (copy) to: ";
            src_node.print_label(dout, *g_omap);
            dout << "\n");
          // dest_node.addPred(src);
          break;
        default:
          llvm_unreachable("Should never get here!\n");
      }
    }
    */
    //}}}

    // Accessors {{{
    int32_t offs() const {
      return offs_;
    }

    ConstraintType type() const {
      return type_;
    }
    //}}}

    // Dot Print Support {{{
    void print_label(llvm::raw_ostream &ofil, const ObjectMap &) const {
      switch (type_) {
        case ConstraintType::Copy:
          ofil << "copy";
          break;
        case ConstraintType::AddressOf:
          ofil << "addr_of";
          break;
        case ConstraintType::Load:
          ofil << "load";
          break;
        case ConstraintType::Store:
          ofil << "store";
          break;
        default:
          llvm_unreachable("Constraint with unexpected type!");
          ofil << "BLEH";
      }
    }
    //}}}

 private:
    //{{{
    ConstraintType type_;
    int32_t offs_;
    //}}}
  //}}}
};

//}}}

// Typedefs for the HU Sparse Evaluation Graph {{{
typedef SEG<DUG::ObjID> HUSeg;
//}}}

// Acutal HU visit impl {{{
static void visitHU(HUSeg &seg, HUNode &node, const ObjectMap &if_debug(omap)) {
  if_debug(
    dout << "Visiting: (" << idToString(node.id()) << ") ";
    node.print_label(dout, omap);
    dout << "\n");
  // Union our past ptsto sets
  for (DUG::ObjID node_id : node.preds()) {
    HUNode &pred = llvm::cast<HUNode>(seg.getNode(node_id));
    if_debug(
      dout << "\tOn pred: (" << idToString(pred.id()) << ") ";
      pred.print_label(dout, omap);
      dout << "\n");

    if_debug(
      dout << "Unioning src ptsto: ";
      for (auto int_id : node.ptsto()) {
        dout << " " << idToString(DUG::ObjID(int_id));
      }
      dout << "\n";
      dout << "with pred ptsto: ";
      for (auto int_id : pred.ptsto()) {
        dout << " " << idToString(DUG::ObjID(int_id));
      }
      dout << "\n");

    node.ptsto() |= pred.ptsto();
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
  // FIXME: HAX to be removed later
  g_omap = const_cast<ObjectMap *>(&omap);
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
  /* Clone it from the constraint graph?
  HUSeg huSeg =
    graph.getConstraintGraph().convert<HUNode, HUEdge>();
    */

  // Instead, create it fresh:
  HUSeg huSeg;

  auto &conGraph = graph.getConstraintGraph();
  // create a HUNode per ConstraintNode:
  std::for_each(conGraph.cbegin(), conGraph.cend(),
      [&huSeg](const DUG::ConstraintGraph::node_iter_type &pr) {
    huSeg.addNode<HUNode>(pr.first);
  });

  std::for_each(conGraph.edges_cbegin(), conGraph.edges_cend(),
      [&huSeg](const DUG::ConstraintGraph::edge_iter_type &pr) {
    auto &cons = llvm::cast<Constraint<DUG::ObjID>>(*pr.second);
    huSeg.addEdge<HUEdge>(pr.first.first, pr.first.second, huSeg, cons);
  });


  if_debug(
    for (auto &pair : huSeg) {
      HUNode &node = llvm::cast<HUNode>(*pair.second);
      dout << "initial ptsto for node " << idToString(pair.second->id()) <<
        " is:";
      for (auto int_id : node.ptsto()) {
        dout << " " << idToString(DUG::ObjID(int_id));
      }
      dout << "\n";
    });

  // Now iterate in topological order (start w/ root, end w/ leaf)
  std::for_each(huSeg.topo_begin(), huSeg.topo_end(),
      [&huSeg, &omap](DUG::ObjID node_id) {
    // Do the HU visit (pred collection) on each node in reverse
    //    topological order
    visitHU(huSeg, llvm::cast<HUNode>(huSeg.getNode(node_id)), omap);
  });

  if_debug(
    for (auto &pair : huSeg) {
      HUNode &node = llvm::cast<HUNode>(*pair.second);
      dout << "ptsto after HU for (";
      if (node.indirect()) {
        dout << "indirect";
      } else {
        dout << "  direct";
      }
      dout << ") node " << idToString(node.id()) <<
        " is:";
      for (auto int_id : node.ptsto()) {
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
    auto &node = llvm::cast<HUNode>(*pair.second);

    auto it = pts_to_pe.find(node.ptsto());

    DUG::PEid pe;
    if (node.indirect()) {
      pe = getNextPE();
      dout << "pe for indirect node: " << pe.val() << "\n";
    } else if (it == std::end(pts_to_pe)) {
      pe = getNextPE();
      pts_to_pe.insert(std::make_pair(node.ptsto(), pe));
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

