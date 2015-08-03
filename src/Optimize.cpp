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

#include "include/SpecSFS.h"

// #define SPECSFS_DEBUG
#include "include/Debug.h"

#include "include/SEG.h"
#include "include/util.h"

namespace {

struct HUEdge;

// Simple helpers needed later {{{
static int getIdx(ConstraintGraph::ObjID id) {
  return id.val();
}
//}}}

// Data for HU nodes {{{
struct HUNode : public SEGNode<ConstraintGraph::ObjID> {
  //{{{
  HUNode(int32_t nodenum, ConstraintGraph::ObjID id) :
    SEGNode<ConstraintGraph::ObjID>(NodeKind::HUNode, nodenum, id) { }

  template <typename id_converter>
  HUNode(int32_t nodenum, ConstraintGraph::ObjID id,
      const SEGNode<ConstraintGraph::ObjID> &nd, id_converter convert) :
      SEGNode<ConstraintGraph::ObjID>(NodeKind::HUNode, nodenum,
          id, nd, convert) { }

  void addPtsTo(ConstraintGraph::ObjID id) {
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
    ConstraintGraph::ObjID id = SEGNode<ConstraintGraph::ObjID>::id();
    auto pr = omap.getValueInfo(id);
    if (pr.first != ObjectMap::Type::Special) {
      const llvm::Value *val = pr.second;
      if (val == nullptr) {
        ofil << "temp node";
      } else if (auto GV = llvm::dyn_cast<const llvm::GlobalValue>(val)) {
        ofil <<  GV->getName();
      } else if (auto F = llvm::dyn_cast<const llvm::Function>(val)) {
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
  static bool classof(const SEGNode<ConstraintGraph::ObjID> *n) {
    return n->getKind() == NodeKind::HUNode;
  }
  //}}}

  bool indirect_ = false;

  Bitmap ptsto_;
  //}}}
};

// FIXME: HAX to be removed later
ObjectMap *g_omap;

struct HUEdge : public SEGEdge<ConstraintGraph::ObjID> {
  //{{{
 public:
    // Construction from Constraint {{{
    HUEdge(ConstraintGraph::ObjID src, ConstraintGraph::ObjID dest,
        SEG<ConstraintGraph::ObjID> &graph,
        const Constraint<ConstraintGraph::ObjID> &con) :
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
    HUEdge(ConstraintGraph::ObjID src, ConstraintGraph::ObjID dest, const SEGEdge<ConstraintGraph::ObjID> &node,
        SEG<ConstraintGraph::ObjID> &graph, id_converter) :
        SEGEdge(EdgeKind::HUEdge, src, dest),
        type_(llvm::cast<Constraint<ConstraintGraph::ObjID>>(node).type()),
        offs_(llvm::cast<Constraint<ConstraintGraph::ObjID>>(node).offs()) {
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
typedef SEG<ConstraintGraph::ObjID> HUSeg;
//}}}

// Acutal HU visit impl {{{
static void visitHU(HUSeg &seg, HUNode &node, const ObjectMap &if_debug(omap)) {
  if_debug(
    dout << "Visiting: (" << idToString(node.id()) << ") ";
    node.print_label(dout, omap);
    dout << "\n");
  // Union our past ptsto sets
  for (ConstraintGraph::ObjID node_id : node.preds()) {
    HUNode &pred = llvm::cast<HUNode>(seg.getNode(node_id));
    if_debug(
      dout << "\tOn pred: (" << idToString(pred.id()) << ") ";
      pred.print_label(dout, omap);
      dout << "\n");

    if_debug(
      dout << "Unioning src ptsto: ";
      for (auto int_id : node.ptsto()) {
        dout << " " << idToString(ConstraintGraph::ObjID(int_id));
      }
      dout << "\n";
      dout << "with pred ptsto: ";
      for (auto int_id : pred.ptsto()) {
        dout << " " << idToString(ConstraintGraph::ObjID(int_id));
      }
      dout << "\n");

    node.ptsto() |= pred.ptsto();
  }
}
//}}}



// Helper Functions {{{


// Comparrison fcn for bitmaps
//}}}

}  // End anon namespace

// optimizeConstraints {{{
bool SpecSFS::optimizeConstraints(ConstraintGraph &graph,
    const ObjectMap &omap) {
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

  auto &conGraph = graph.getSEG();
  // create a HUNode per ConstraintNode:
  std::for_each(conGraph.cbegin(), conGraph.cend(),
      [&huSeg](const ConstraintGraph::ConstraintSEG::node_iter_type &pr) {
    huSeg.addNode<HUNode>(pr.first);
  });

  std::for_each(conGraph.edges_cbegin(), conGraph.edges_cend(),
      [&huSeg](const ConstraintGraph::ConstraintSEG::edge_iter_type &pr) {
    auto &cons = llvm::cast<Constraint<ConstraintGraph::ObjID>>(*pr.second);
    huSeg.addEdge<HUEdge>(pr.first.first, pr.first.second, huSeg, cons);
  });


  if_debug(
    for (auto &pair : huSeg) {
      HUNode &node = llvm::cast<HUNode>(*pair.second);
      dout << "initial ptsto for node " << idToString(pair.second->id()) <<
        " is:";
      for (auto int_id : node.ptsto()) {
        dout << " " << idToString(ConstraintGraph::ObjID(int_id));
      }
      dout << "\n";
    });

  // Now iterate in topological order (start w/ root, end w/ leaf)
  std::for_each(huSeg.topo_begin(), huSeg.topo_end(),
      [&huSeg, &omap](ConstraintGraph::ObjID node_id) {
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
        dout << " " << idToString(ConstraintGraph::ObjID(int_id));
      }
      dout << "\n";
    });

  huSeg.printDotFile("optimize.dot", omap);

  //  Used to map objs to the PE class
  std::map<Bitmap, ConstraintGraph::ObjID, BitmapLT> pts_to_pe;

  // Now create the pointer equivalency ids
  for (auto &pair : huSeg) {
    auto &node = llvm::cast<HUNode>(*pair.second);

    auto it = pts_to_pe.find(node.ptsto());

    if (node.indirect()) {
      dout << "Obj for indirect node: " << node.id() << "\n";
    } else if (it == std::end(pts_to_pe)) {
      pts_to_pe.insert(std::make_pair(node.ptsto(), node.id()));
      dout << "pe for ptsto: " << node.id() << "\n";
    } else {
      graph.getNode(it->second).unite(conGraph, graph.getNode(node.id()));
    }
  }

  return false;
}
//}}}

