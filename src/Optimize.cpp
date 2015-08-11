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

#define SPECSFS_DEBUG
#include "include/Debug.h"

#include "include/SEG.h"
#include "include/util.h"

// FIXME: HAX to be removed later
ObjectMap *g_omap;

namespace {

struct HUEdge;

// Simple helpers needed later {{{
static int getIdx(SEG<ConstraintGraph::ObjID>::NodeID id) {
  return id.val();
}
//}}}

// Data for HU nodes {{{
struct HUNode : public SEGNode<ConstraintGraph::ObjID> {
  //{{{
  typedef typename ConstraintGraph::ObjID ObjID;
  typedef typename SEG<ConstraintGraph::ObjID>::NodeID NodeID;

  HUNode(NodeID node_id, ConstraintGraph::ObjID id) :
    SEGNode<ConstraintGraph::ObjID>(NodeKind::HUNode, node_id, id) { }

  void addPtsTo(NodeID id) {
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
    ObjID id = SEGNode<ObjID>::extId();
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

struct HUEdge : public SEGEdge<ConstraintGraph::ObjID> {
  //{{{
 public:
    typedef typename ConstraintGraph::ObjID ObjID;
    typedef typename SEG<ConstraintGraph::ObjID>::NodeID NodeID;

    // Construction from Constraint {{{
    HUEdge(NodeID src, NodeID dest,
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
              dout << "Adding edge: " << src << " -> " <<
                dest << "\n";
              dout << "Adding pred to: ";
              src_node.print_label(dout, *g_omap);
              dout << "\n");
          } else {
            dout << "Setting: " << src << " to indirect\n";
            src_node.setIndirect();
          }
          break;
        case ConstraintType::AddressOf:
          if_debug(
            dout << "Setting: " << dest << " to indirect\n";
            dout << "Adding ptsto: " << dest <<
                " to ptsto of: " << src << "\n");

          dest_node.setIndirect();
          src_node.addPtsTo(dest);

          if (g_omap->isObject(src_node.extId())) {
            src_node.setIndirect();
          }

          break;
        case ConstraintType::Copy:
          if_debug(
            dout << "Adding edge: " << src << " -> " << dest << "\n";
            dout << "Adding pred (copy) to: ";
            src_node.print_label(dout, *g_omap);
            dout << "\n");
          break;
        default:
          llvm_unreachable("Should never get here!\n");
      }
    }
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
    dout << "Visiting: (" << node.id() << ") ";
    node.print_label(dout, omap);
    dout << "\n");

  // Union our past ptsto sets
  for (auto edge_id : node.preds()) {
    auto &edge = seg.getEdge(edge_id);
    auto node_id = edge.src();
    dout << "Have node_id: " << node_id << "\n";
    HUNode &pred = seg.getNode<HUNode>(node_id);
    if_debug(
      dout << "\tOn pred: (" << pred.id() << ") ";
      pred.print_label(dout, omap);
      dout << "\n");

    if_debug(
      dout << "Unioning src ptsto: ";
      for (auto int_id : node.ptsto()) {
        dout << " " << ConstraintGraph::ObjID(int_id);
      }
      dout << "\n";
      dout << "with pred ptsto: ";
      for (auto int_id : pred.ptsto()) {
        dout << " " << ConstraintGraph::ObjID(int_id);
      }
      dout << "\n");

    node.ptsto() |= pred.ptsto();
  }
}
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

  std::map<ConstraintGraph::NodeID, HUSeg::NodeID> remap;
  std::map<HUSeg::NodeID, ConstraintGraph::NodeID> rev_remap;
  auto &conGraph = graph.getSEG();
  // create a HUNode per ConstraintNode:
  std::for_each(conGraph.cbegin(), conGraph.cend(),
      [&huSeg, &remap, &rev_remap]
      (const ConstraintGraph::ConstraintSEG::node_iter_type &pnode) {
    auto ret = huSeg.addNode<HUNode>(pnode->extId());
    remap[pnode->id()] = ret->second;
    rev_remap[ret->second] = pnode->id();
  });

  std::for_each(conGraph.edges_cbegin(), conGraph.edges_cend(),
      [&huSeg, &remap]
      (const ConstraintGraph::ConstraintSEG::edge_iter_type &pedge) {
    auto &cons = llvm::cast<Constraint<ConstraintGraph::ObjID>>(*pedge);
    dout << "Adding edge: " << cons.src() << " -> " << cons.dest() << "\n";
    huSeg.addEdge<HUEdge>(remap[cons.src()], remap[cons.dest()], huSeg, cons);
  });


  if_debug(
    for (auto &pnode : huSeg) {
      HUNode &node = llvm::cast<HUNode>(*pnode);
      dout << "initial ptsto for node " << node.id() <<
        " is:";
      for (auto int_id : node.ptsto()) {
        dout << " " << ConstraintGraph::ObjID(int_id);
      }
      dout << "\n";
    });

  // Now iterate in topological order (start w/ root, end w/ leaf)
  std::for_each(huSeg.topo_begin(), huSeg.topo_end(),
      [&huSeg, &omap](ConstraintGraph::NodeID node_id) {
    // Do the HU visit (pred collection) on each node in reverse
    //    topological order
    visitHU(huSeg, huSeg.getNode<HUNode>(node_id), omap);
  });

  if_debug(
    for (auto &pnode : huSeg) {
      HUNode &node = llvm::cast<HUNode>(*pnode);
      dout << "ptsto after HU for (";
      if (node.indirect()) {
        dout << "indirect";
      } else {
        dout << "  direct";
      }
      dout << ") node " << node.id() <<
        " is:";
      for (auto int_id : node.ptsto()) {
        dout << " " << ConstraintGraph::ObjID(int_id);
      }
      dout << "\n";
    });

  huSeg.printDotFile("optimize.dot", omap);

  //  Used to map objs to the PE class
  std::map<Bitmap, SEG<ConstraintGraph::ObjID>::NodeID, BitmapLT> pts_to_pe;

  // Now create the pointer equivalency ids
  for (auto &pnode : huSeg) {
    auto &node = llvm::cast<HUNode>(*pnode);

    auto it = pts_to_pe.find(node.ptsto());

    if (node.indirect()) {
      dout << "Obj for indirect node: " << node.id() << "\n";
    } else if (it == std::end(pts_to_pe)) {
      pts_to_pe.insert(std::make_pair(node.ptsto(), node.id()));
      dout << "pe for ptsto: " << node.id() << "\n";
    } else {
      auto &dest_node =
        graph.getNode(rev_remap[it->second]);
      auto &src_node =
        graph.getNode(rev_remap[node.id()]);

      auto src_ext_id = src_node.extId();
      auto dest_ext_id = dest_node.extId();

      llvm::dbgs() << "Merging obj_id: " << dest_ext_id << " with: " <<
        src_ext_id << "\n";
      dest_node.unite(conGraph, src_node);
      auto it1 = conGraph.findNode(src_ext_id);
      auto it2 = conGraph.findNode(dest_ext_id);
      assert(it2 != conGraph.node_map_end());
      assert(it1 != conGraph.node_map_end());

      llvm::dbgs() << "Remap gets: " << it1->second << ", " << it2->second <<
        "\n";
      assert(it1->second == it2->second);
    }
  }

  return false;
}
//}}}

