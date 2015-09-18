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

#include "include/SpecSFS.h"

#include "include/SEG.h"
#include "include/util.h"

namespace {

struct HUEdge;

// Simple helpers needed later {{{
static int getIdx(SEG<ConstraintGraph::ObjID>::NodeID id) {
  return id.val();
}
//}}}

// Data for HU nodes {{{
struct HUNode : public UnifyNode<ConstraintGraph::ObjID> {
  //{{{
  typedef typename ConstraintGraph::ObjID ObjID;
  typedef typename SEG<ConstraintGraph::ObjID>::NodeID NodeID;

  HUNode(NodeID node_id, ConstraintGraph::ObjID id) :
    UnifyNode<ConstraintGraph::ObjID>(NodeKind::HUNode, node_id, id) { }

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
    ofil << SEGNode<ObjID>::id() << " : ";
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
        SEG<ConstraintGraph::ObjID> &graph, const Constraint &con) :
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
          dest_node.setIndirect();
          if_debug(
            dout("Adding edge: " << src << " -> " <<
              dest << "\n");
            dout("Adding pred to: " << src_node.id() << "\n"));
          break;
        case ConstraintType::AddressOf:
          if_debug(
            dout("Setting: " << dest << " to indirect\n");
            dout("Adding ptsto: " << dest <<
                " to ptsto of: " << src << "\n"));

          dest_node.setIndirect();
          src_node.addPtsTo(dest);

          break;
        case ConstraintType::Copy:
        case ConstraintType::GlobalInit:
          if_debug(
            dout("Adding edge: " << src << " -> " << dest << "\n");
            dout("Adding pred (copy) to: " << src_node.id() << "\n"));
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
        case ConstraintType::GlobalInit:
          ofil << "glbl_init";
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
    dout("Visiting: (" << node.id() << ") ");
    // node.print_label(dout, omap);
    dout("\n"));

  // Union our past ptsto sets
  for (auto edge_id : node.preds()) {
    auto &edge = seg.getEdge(edge_id);
    auto node_id = edge.src();
    dout("Have node_id: " << node_id << "\n");
    HUNode &pred = seg.getNode<HUNode>(node_id);
    if_debug(
      dout("\tOn pred: (" << pred.id() << ") ");
      // pred.print_label(dout, omap);
      dout("\n"));

    if_debug(
      dout("Unioning src ptsto: ");
      for (auto int_id : node.ptsto()) {
        dout(" " << ConstraintGraph::ObjID(int_id));
      }
      dout("\n");
      dout("with pred ptsto: ");
      for (auto int_id : pred.ptsto()) {
        dout(" " << ConstraintGraph::ObjID(int_id));
      }
      dout("\n"));

    node.ptsto() |= pred.ptsto();
  }
}
//}}}

}  // End anon namespace

// optimizeConstraints {{{
bool SpecSFS::optimizeConstraints(ConstraintGraph &graph, CFG &cfg,
    const ObjectMap &omap) {

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

  // Create our HU graph
  HUSeg huSeg;

  // Populate the graph
  // create a HUNode per ConstraintNode:
  std::for_each(graph.cbegin(), graph.cend(),
      [&huSeg]
      (const ConstraintGraph::iter_type &pcons) {
    // Store constraints don't define nodes!
    auto dest = pcons->dest();

    if (huSeg.findNode(dest) == huSeg.node_map_end()) {
      huSeg.addNode<HUNode>(dest);
    }

    if (huSeg.findNode(pcons->offsSrc()) == huSeg.node_map_end()) {
      huSeg.addNode<HUNode>(pcons->offsSrc());
    }
  });

  // Add the edges for each constraint
  std::for_each(graph.cbegin(), graph.cend(),
      [&huSeg]
      (const ConstraintGraph::iter_type &pcons) {
    auto cons = *pcons;

    auto src_pr = huSeg.getNodes(cons.offsSrc());
    assert(std::distance(src_pr.first, src_pr.second) == 1);
    auto src_id = src_pr.first->second;

    auto dest = cons.dest();

    auto dest_pr = huSeg.getNodes(dest);
    assert(std::distance(dest_pr.first, dest_pr.second) == 1);
    auto dest_id = dest_pr.first->second;


    huSeg.addEdge<HUEdge>(src_id, dest_id, huSeg, cons);
  });


  if_debug(  //{{{
    for (auto &pnode : huSeg) {
      HUNode &node = llvm::cast<HUNode>(*pnode);
      dout("initial ptsto for node " << node.id() <<
        " is:");
      for (auto int_id : node.ptsto()) {
        dout(" " << ConstraintGraph::ObjID(int_id));
      }
      dout("\n");
    });  //}}}

  if_debug(huSeg.printDotFile("HuStart.dot", *g_omap));

  // Now iterate in topological order (start w/ root, end w/ leaf)
  std::for_each(huSeg.topo_begin(), huSeg.topo_end(),
      [&huSeg, &omap](HUSeg::NodeID node_id) {
    // Do the HU visit (pred collection) on each node in reverse
    //    topological order
    visitHU(huSeg, huSeg.getNode<HUNode>(node_id), omap);
  });

  if_debug(  //{{{
    for (auto &pnode : huSeg) {
      HUNode &node = llvm::cast<HUNode>(*pnode);
      dout("ptsto after HU for (");
      if (node.indirect()) {
        dout("indirect");
      } else {
        dout("  direct");
      }
      dout(") node " << node.id() <<
        " is:");
      for (auto int_id : node.ptsto()) {
        dout(" " << ConstraintGraph::ObjID(int_id));
      }
      dout("\n");
    });  //}}}

  if_debug(huSeg.printDotFile("HuOpt.dot", *g_omap));

  //  Used to map objs to the PE class
  std::map<Bitmap, SEG<ConstraintGraph::ObjID>::NodeID, BitmapLT> pts_to_pe;

  // Now create the pointer equivalency ids
  for (auto &pnode : huSeg) {
    auto &node = llvm::cast<HUNode>(*pnode);

    auto it = pts_to_pe.find(node.ptsto());

    if (node.indirect()) {
      dout("Obj for indirect node: " << node.id() << "\n");
    } else if (it == std::end(pts_to_pe)) {
      pts_to_pe.emplace(node.ptsto(), node.id());
      dout("pe for ptsto: " << node.id() << "\n");
    } else {
      // These nodes are pe equivalent
      // Unite the HU nodes, then iterate through the constraints and adjust ids
      //    based on reps?

      // Get the rep from the ptsto
      auto rep_node = huSeg.getNode<HUNode>(it->second);

      // Unite the node with the rep node
      rep_node.unite(huSeg, node);
    }
  }

  std::map<ObjectMap::ObjID, ObjectMap::ObjID> load_remap;
  // Now iterate each constraint, and update their ObjIDs to point to reps
  std::for_each(std::begin(graph), std::end(graph),
      [&huSeg, &load_remap, &graph] (ConstraintGraph::iter_type &pcons) {
    auto src_pr = huSeg.getNodes(pcons->offsSrc());
    assert(std::distance(src_pr.first, src_pr.second) == 1);
    auto hu_src_id = src_pr.first->second;
    auto src_rep_id = huSeg.getNode(hu_src_id).extId();

    auto dest = pcons->dest();

    auto dest_pr = huSeg.getNodes(dest);
    assert(std::distance(dest_pr.first, dest_pr.second) == 1);
    auto hu_dest_id = dest_pr.first->second;
    auto dest_rep_id = huSeg.getNode(hu_dest_id).extId();


    if (dest_rep_id != pcons->dest()) {
      // If this is a load cons, its dest shouldn't have changed
      dout("new value: " << ValPrint(dest_rep_id) << "\n");
      dout("old value: " << ValPrint(pcons->dest()) << "\n");

      load_remap.emplace(pcons->dest(), dest_rep_id);

      dout("retarget: (" << pcons->offsSrc() << ", " << pcons->dest() <<
        ") -> ("<< src_rep_id << ", " << dest_rep_id << ")\n");

      pcons->retarget(src_rep_id, dest_rep_id);

      // Pcons has been optimized out, go ahead and remove it
      // NOTE: This removal method doesn't modify ConsIDs so it is safe to call
      // from here... yech
      graph.removeConstraint(pcons);
    }
  });

  // NO! We cannot remove duplicates here... because we have live ConsIDs which
  //     will be used when we resolve indir edges!!!
  //     We'll do this after that step
  // Now clean up our constraints (remove duplicates)
  // graph.unique();

  // Now remap all appropriate vector entries
  // meh... O(N * log(N) )
  SEG<CFG::CFGid> &cfg_seg = cfg.getSEG();
  std::for_each(std::begin(cfg_seg), std::end(cfg_seg),
      [&load_remap, &cfg]
      (SEG<CFG::CFGid>::node_iter_type &pnode) {
    CFG::Node &cfg_node = llvm::cast<CFG::Node>(*pnode);

    dout("node eval: "<< cfg_node.extId() << "\n");

    std::vector<std::pair<ObjectMap::ObjID, ObjectMap::ObjID>> remap;
    std::for_each(cfg_node.uses_begin(), cfg_node.uses_end(),
        [&load_remap, &remap] (const ObjectMap::ObjID &obj_id) {
      dout("obj_id eval\n");
      auto it = load_remap.find(obj_id);

      if (it != std::end(load_remap)) {
        if (obj_id != it->second) {
          dout("  Adding remap: (" << obj_id << ", " << it->second <<
            ")\n");
          remap.emplace_back(obj_id, it->second);
        }
      }
    });

    std::for_each(std::begin(remap), std::end(remap),
        [&cfg, &cfg_node] (std::pair<ObjectMap::ObjID, ObjectMap::ObjID> &pr) {
      cfg_node.removeUse(pr.first);
      cfg_node.addUse(pr.second);

      dout("Erasing obj_id: " << pr.first << ": " <<
        ValPrint(pr.first) << "\n");

      cfg.eraseObjToCFG(pr.first);
    });
  });

  return false;
}
//}}}

