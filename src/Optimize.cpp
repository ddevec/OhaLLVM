/*
 * Copyright (C) 2015 David Devecsery
 */

// Turn debugging on/off for this file
// #define SPECSFS_DEBUG

#include <cassert>
#include <cstdint>

#include <algorithm>
#include <limits>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "include/Debug.h"

#include "include/SpecAnders.h"
#include "include/SpecSFS.h"

#include "include/SEG.h"
#include "include/Tarjans.h"
#include "include/util.h"

static SEG::NodeID objToNode(ObjectMap::ObjID id) {
  return SEG::NodeID(id.val());
}

static ObjectMap::ObjID nodeToObj(SEG::NodeID id) {
  return ObjectMap::ObjID(id.val());
}

namespace {

// Data for HU nodes {{{
struct HUNode : public SEG::Node {
  //{{{
  typedef typename SEG::NodeID NodeID;

  explicit HUNode(NodeID node_id) :
    SEG::Node(NodeKind::HUNode, node_id) { }

  void addPtsTo(int32_t id) {
    ptsto_.set(id);
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

  void unite(SEG &seg, SEG::Node &n) override {
    auto &node = cast<HUNode>(n);

    indirect_ |= node.indirect();
    ptsto() |= node.ptsto();

    node.ptsto().clear();

    SEG::Node::unite(seg, n);
  }

  void print_label(dbg_ostream &o_fil,
      const ObjectMap &omap) const override {
    auto id = SEG::Node::id();
    auto obj_id = nodeToObj(id);
    o_fil << id << ": (" << ValPrint(obj_id, omap) << ") i: " << indirect() <<
      " ptsto: {";
    for (auto elm : ptsto()) {
      o_fil << " " << elm;
    }
    o_fil << " }";
  }

  // For LLVM RTTI {{{
  static bool classof(const SEG::Node *n) {
    return n->getKind() == NodeKind::HUNode;
  }
  //}}}

  bool indirect_ = false;

  // For tarjan's
  int32_t lowlink = -1;
  int32_t index = -1;
  bool onStack = false;

  Bitmap ptsto_;
  //}}}
};

class HUCalc {
  //{{{
 public:
    static const int32_t PENonPtr = 0;

    HUCalc() = default;

    static bool isNonPtr(HUNode &nd) {
      bool ret = nd.ptsto().test(PENonPtr);
      // If its a non-ptr the ptsto size must be 1
      assert(!ret || nd.ptsto().count() == 1);

      return ret;
    }

    void giveNewPE(HUNode &node) {
      node.ptsto().set(nextPE_);
      nextPE_++;
    }

    int32_t getPE(SEG::NodeID id, int32_t offs) {
      auto it = gepToPE_.find(std::make_pair(id, offs));

      if (it == std::end(gepToPE_)) {
        auto rp = gepToPE_.emplace(std::make_pair(id, offs),
            nextPE_);
        nextPE_++;
        assert(rp.second);
        it = rp.first;
      }

      return it->second;
    }

    // Here we run tarjan's algorithm, this merges our SCC's as only strong
    // edges are represented in our graph
    void visitHU(SEG &seg, HUNode &node) {
      node.index = nextIndex_;
      node.lowlink = nextIndex_;
      nextIndex_++;

      nodeStack_.push_back(node.id());

      node.onStack = true;

      for (auto pred_id : node.preds()) {
        auto &pred_node = seg.getNode<HUNode>(pred_id);
        if (pred_node.index < 0) {
          visitHU(seg, pred_node);
          node.lowlink = std::min(pred_node.lowlink, node.lowlink);
        } else if (pred_node.onStack) {
          node.lowlink = std::min(node.lowlink, pred_node.index);
        }
      }

      if (node.lowlink == node.index) {
        dout("Node rep: (" << node.id() << ") "  <<
          ValPrint(nodeToObj(node.id())) << "\n");
        // Do the SCC merging
        while (true) {
          auto merge_id = nodeStack_.back();
          nodeStack_.pop_back();

          auto &merge_node = seg.getNode<HUNode>(merge_id);
          merge_node.onStack = false;

          if (merge_id == node.id()) {
            break;
          }

          dout("  merging in: (" << merge_node.id() << ") " <<
            ValPrint(nodeToObj(merge_node.id())) << "\n");
          node.unite(seg, merge_node);
        }

        // If this node is indirect, add a new PE, so it can't be merged w/ its
        //   preds
        if (node.indirect()) {
          dout("  indirect, adding PE: " << nextPE_ << "\n");
          node.addPtsTo(nextPE_);
          nextPE_++;
        }

        // We also merge in the ptsto sets from our pred, in our topological
        // node visit post-merge
        dout("  gathering pred ptstos\n");
        for (auto pred_id : node.preds()) {
          auto &pred_node = seg.getNode<HUNode>(pred_id);

          if (pred_node.id() == node.id()) {
            continue;
          }

          dout("  have pred: " << pred_node.id() << "\n");
          if_debug(
            dout("  pred ptsto: ");
            for (auto pts : pred_node.ptsto()) {
              dout(" " << pts);
            }
            dout("\n"));

          assert(!pred_node.ptsto().empty());

          // Merge in our preds ptsto, unless they are a nonptr
          if (!pred_node.ptsto().test(PENonPtr)) {
            node.ptsto() |= pred_node.ptsto();
          }
        }

        if (node.ptsto().empty()) {
          node.addPtsTo(PENonPtr);
        }

        if_debug(
          dout("  node ptsto: ");
          for (auto pts : node.ptsto()) {
            dout(" " << pts);
          }
          dout("\n"));
      }
    }

    void calcHU(SEG &seg) {
      nextIndex_ = 0;
      nodeStack_.clear();

      for (auto &pnode : seg) {
        // Do the HU visit (pred collection) on each node in reverse
        //    topological order
        auto &node = cast<HUNode>(*pnode);
        if (node.index < 0) {
          visitHU(seg, node);
        }
      }
    }

 private:
    int32_t nextIndex_ = 0;
    int32_t nextPE_ = 1;
    std::vector<SEG::NodeID> nodeStack_;
    std::map<std::pair<SEG::NodeID, int32_t>, int32_t> gepToPE_;
  //}}}
};


static void addHUEdge(SEG::NodeID src, SEG::NodeID dest,
    SEG &graph, const Constraint &con, HUCalc &calc) {
  // Get our two HU nodes
  auto &dest_node = graph.getNode<HUNode>(dest);
  auto &src_node = graph.getNode<HUNode>(src);

  // Add constraints
  switch (con.type()) {
    case ConstraintType::Store:
      break;
    case ConstraintType::Load:
      // Add its own indirect ptsto
      dest_node.setIndirect();
      break;
    case ConstraintType::AddressOf:
      if_debug(
        dout("Setting: " << dest << " to indirect\n");
        dout("Adding ptsto: " << dest <<
            " to ptsto of: " << src << "\n"));
      dest_node.setIndirect();

      break;
    case ConstraintType::Copy:
      if_debug(
        dout("Adding edge: " << src << " -> " << dest << "\n");
        dout("Adding pred (copy) to: " << src_node.id() << "\n"));

      // Deal with gep instructions...
      // TODO(ddevec): What about gep with idx 0?
      //   I think we can ignore this...
      if (con.offs() != 0) {
        dest_node.addPtsTo(calc.getPE(src, con.offs()));
      // If not a GEP, we've got a copy
      } else {
        dest_node.addPred(graph, src_node.id());
      }

      break;
    default:
      llvm_unreachable("Should never get here!\n");
  }
}
//}}}

}  // End anon namespace

// SFS HU implementation {{{
bool SpecSFS::optimizeConstraints(ConstraintGraph &graph, CFG &cfg,
    ObjectMap &omap) {

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
  SEG hu_graph;

  // Populate the graph
  // create a HUNode per ConstraintNode:
  ObjectMap::ObjID max_src_dest_id = ObjectMap::ObjID(-1);
  std::for_each(graph.cbegin(), graph.cend(),
      [&max_src_dest_id]
      (const ConstraintGraph::iter_type &pcons) {
    // Store constraints don't define nodes!
    auto dest = pcons->dest();
    auto src = pcons->src();
    auto rep = pcons->rep();

    if (dest > max_src_dest_id) {
      max_src_dest_id = dest;
    }

    if (src > max_src_dest_id) {
      max_src_dest_id = src;
    }

    if (rep > max_src_dest_id) {
      max_src_dest_id = rep;
    }
  });

  // go to max val + 1, so if I find id 0, there should be 1 element
  for (int i = 0; i < max_src_dest_id.val()+1; i++) {
    // Add a node per potential dest
    auto node_id = hu_graph.addNode<HUNode>();
    assert(node_id.val() == i);

    // If the node is not a value, make it indirect, so its not merged
    //   arbitrarily
    auto obj_id = nodeToObj(node_id);
    if (!omap.isValue(obj_id) || graph.isIndirCall(obj_id)) {
      auto &node = hu_graph.getNode<HUNode>(node_id);
      node.setIndirect();
    }
  }

  HUCalc calc;

  // Add a PE for each store rep, so they aren't merged
  std::for_each(graph.cbegin(), graph.cend(),
      [&hu_graph, &calc]
      (const ConstraintGraph::iter_type &pcons) {
    // Store constraints don't define nodes!
    auto rep_id = pcons->rep();
    auto node_rep_id = objToNode(rep_id);
    auto &node = hu_graph.getNode<HUNode>(node_rep_id);
    calc.giveNewPE(node);
  });

  // Add the edges for each constraint
  std::for_each(graph.cbegin(), graph.cend(),
      [&hu_graph, &calc]
      (const ConstraintGraph::iter_type &pcons) {
    auto cons = *pcons;

    auto src_id = cons.src();
    auto dest_id = cons.dest();

    // Convert to nodes:
    auto dest_node_id = objToNode(dest_id);
    auto src_node_id = objToNode(src_id);

    addHUEdge(src_node_id, dest_node_id, hu_graph, cons, calc);
  });

  // if_debug(hu_graph.printDotFile("HuStart.dot", *g_omap));
  // hu_graph.printDotFile("HuStart.dot", *g_omap);

  // Now iterate in topological order (start w/ root, end w/ leaf)
  // NOTE: visitHU enforces topo order... internally

  calc.calcHU(hu_graph);

  // if_debug(hu_graph.printDotFile("HuStart.dot", *g_omap));
  // hu_graph.printDotFile("HuOpt.dot", *g_omap);

  //  Used to map objs to the PE class
  std::map<Bitmap, SEG::NodeID, BitmapLT> pts_to_pe;

  // Find equiv classes for each node in the hu_graph
  // Merge nodes into their equiv classes
  for (auto &pnode : hu_graph) {
    auto &node = cast<HUNode>(*pnode);

    auto &ptsto = node.ptsto();

    // Set empty nodes to nonptr
    if (ptsto.empty() || ptsto.test(HUCalc::PENonPtr)) {
      ptsto.clear();
      ptsto.set(HUCalc::PENonPtr);
    }

    auto it = pts_to_pe.find(ptsto);

    if (it == std::end(pts_to_pe)) {
      pts_to_pe.emplace(ptsto, node.id());
    } else {
      auto &rep_node = hu_graph.getNode<HUNode>(it->second);

      rep_node.unite(hu_graph, node);
    }
  }

  // Need to update omap!  value to ObjID ptr needs to change:
  for (int i = 0; i < max_src_dest_id.val(); i++) {
    auto node_id = SEG::NodeID(i);

    auto &node = hu_graph.getNode(node_id);

    auto rep_id = node.id();

    if (rep_id != node_id) {
      /*
      llvm::dbgs() << "Updating omap: (" << node_id << ") " <<
        ValPrint(nodeToObj(node_id)) << " -> " << rep_id << "\n";
      */
      // setObjIDRep(nodeToObj(node_id), nodeToObj(rep_id));
      omap.mergeObjRep(nodeToObj(node_id), nodeToObj(rep_id));
    }
  }

  // Okay, now we have equiv classes... update our constraint graph ObjIDs to
  // point to them (and note what we upated)
  // As well as: the uses and defs in the CFG
  std::set<Constraint> dedup;
  for (size_t i = 0; i < graph.constraintSize(); i++) {
    ConstraintGraph::ConsID id(i);
    auto &cons = graph.getConstraint(id);

    auto rep_obj_id = cons.rep();
    auto src_obj_id = cons.src();
    auto dest_obj_id = cons.dest();
    auto &src_rep_node = hu_graph.getNode<HUNode>(objToNode(src_obj_id));
    auto &dest_rep_node = hu_graph.getNode<HUNode>(objToNode(dest_obj_id));
    /*
    auto &rep_rep_node = hu_graph.getNode<HUNode>(objToNode(rep_obj_id));
    auto src_rep_id = omap.getRep(nodeToObj(src_rep_node.id()));
    auto dest_rep_id = omap.getRep(nodeToObj(dest_rep_node.id()));
    auto rep_rep_id = omap.getRep(nodeToObj(rep_rep_node.id()));
    */
    auto src_rep_id = omap.getRep(src_obj_id);
    auto dest_rep_id = omap.getRep(dest_obj_id);
    auto rep_rep_id = omap.getRep(rep_obj_id);

    dout("Initial cons: " << cons << "\n");
    // Always change the rep
    /*
    llvm::dbgs() << "inital rep: " << ValPrint(rep_obj_id) << "\n";
    llvm::dbgs() << "Updating rep: " << rep_obj_id << " to: " << rep_rep_id <<
      "\n";
    */
    /*
    if (rep_obj_id.val() == 159943 || rep_rep_id.val() == 159943) {
      llvm::dbgs() << "Updating cons rep " << rep_obj_id << " to: " <<
          rep_rep_id << "\n";
    }

    if (dest_rep_id.val() == 159943 || dest_obj_id.val() == 159943) {
      llvm::dbgs() << "Updating cons dest " << dest_obj_id << " to: " <<
          dest_rep_id << "\n";
    }
    */
    cons.updateRep(rep_rep_id);

    // Update src and dest to reps
    //   but, don't change the src_id of addr_of nodes
    if (cons.type() == ConstraintType::AddressOf) {
      assert(omap.getRep(src_obj_id) == src_obj_id);
      cons.retarget(src_obj_id, dest_rep_id);
    } else {
      cons.retarget(src_rep_id, dest_rep_id);
    }

    if (HUCalc::isNonPtr(src_rep_node) || HUCalc::isNonPtr(dest_rep_node)) {
      // If this constriant had a node in the cfg, remove it
      if (cons.type() == ConstraintType::Load ||
          cons.type() == ConstraintType::Store) {
        cfg.eraseObjToCFG(rep_obj_id);
      }
      // llvm::dbgs() << __LINE__ << " Deleting rep: " << cons.rep() << "\n";
      graph.removeConstraint(id);
      continue;
    }

    // If we have a copy to self, delete it
    if (cons.type() == ConstraintType::Copy &&
        cons.src() == cons.dest() && cons.offs() == 0) {
      // llvm::dbgs() << __LINE__ << " Deleting rep: " << cons.rep() << "\n";
      // llvm::dbgs() << "  With dest: " << cons.dest() << "\n";
      graph.removeConstraint(id);
      continue;
    }

    // If I find a duplicate COPY or ADDR OF cons
    // NOTE: Cannot do this for LOAD or STORE cons, because they take flow
    //   sensitive info, not represented here
    if (cons.type() == ConstraintType::Copy ||
        cons.type() == ConstraintType::AddressOf) {
      dout("Have cons: " << cons << "\n");
      auto it = dedup.find(cons);
      if (it == std::end(dedup)) {
        dedup.insert(cons);
      } else {
        // llvm::dbgs() << __LINE__ << " Deleting rep: " << cons.rep() << "\n";
        // llvm::dbgs() << "  With dest: " << cons.dest() << "\n";
        graph.removeConstraint(id);
      }
    }
  }

  // Don't update def-use or objToCFG, as the reps haven't changed?
  // Now fix up our defs, uses, and global inits w/in the CFG
  // Iterate each CFG node
  // Replace the ObjID with the rep ObjID as found in calc
  for (auto &pnode : cfg.getSEG()) {
    auto &cfg_node = cast<CFG::Node>(*pnode);

    std::set<ObjectMap::ObjID> new_uses;
    std::for_each(cfg_node.uses_begin(), cfg_node.uses_end(),
        [&omap, &hu_graph, &new_uses] (ObjectMap::ObjID use) {
      auto new_use = omap.getRep(use);
      new_uses.insert(new_use);
    });

    std::set<ObjectMap::ObjID> new_defs;
    std::for_each(cfg_node.defs_begin(), cfg_node.defs_end(),
        [&omap, &hu_graph, &new_defs] (ObjectMap::ObjID def) {
      auto new_def = omap.getRep(def);
      new_defs.insert(new_def);
    });

    cfg_node.swapDefs(new_defs);
    cfg_node.swapUses(new_uses);
  }

  // I don't think I need to remap this, the old mapping should still be
  //    legal...
  // Create new objToCFG for the cfg
  std::map<ObjectMap::ObjID, CFG::CFGid> new_obj_to_cfg;
  std::for_each(cfg.obj_to_cfg_cbegin(), cfg.obj_to_cfg_cend(),
      [&new_obj_to_cfg, &hu_graph, &omap]
      (const std::pair<const ObjectMap::ObjID, CFG::CFGid> &pr) {
    auto new_obj_id = omap.getRep(pr.first);

    /*
    if (new_obj_id != pr.first) {
      llvm::dbgs() << "Inserting " << new_obj_id << " to obj_to_cfg at: " <<
          pr.second << "\n";
      llvm::dbgs() << "  In place of: " << pr.first << "\n";
    }
    */

    // NOTE: I don't think the addition has to succeed.  THe two nodes are
    // equivalent, so if they were on different CFG nodes that shouldn't matter,
    // either is the same...

    if_debug_enabled(auto ret =)
      new_obj_to_cfg.emplace(new_obj_id, pr.second);
    assert(ret.second);
  });
  cfg.swapObjToCFG(new_obj_to_cfg);

  return false;
}
//}}}

// Anders Optimizations {{{
class OptNode : public SEG::Node {
 public:
  typedef SEG::NodeID NodeID;
  explicit OptNode(NodeKind kind, NodeID node_id) :
    SEG::Node(kind, node_id) { }

  virtual bool isNonPtr() = 0;

  static bool classof(const SEG::Node *node) {
    return (node->getKind() > NodeKind::OptNode &&
            node->getKind() <= NodeKind::OptNodeEnd);
  }
};

// Cleanup constraints after optimizations {{{
struct HCDNode;
static int32_t updateAndersConstraints(ConstraintGraph &cg, ObjectMap &omap,
    SEG &graph, ObjectMap::ObjID max_src_dest_id) {
  // First, update the omap
  for (int32_t i = 0; i < max_src_dest_id.val(); i++) {
    SEG::NodeID node_id(i);
    auto &node = graph.getNode(node_id);

    auto rep_id = node.id();

    if (rep_id != node_id) {
      if (nodeToObj(rep_id) == ObjectMap::ObjID(112778) ||
          nodeToObj(node_id) == ObjectMap::ObjID(112778)) {
        llvm::dbgs() << "Updating omap rep from: " << rep_id << " to: " <<
          node_id << "\n";
      }
      omap.mergeObjRep(nodeToObj(node_id), nodeToObj(rep_id));
    }
  }

  int32_t num_removed = 0;
  std::set<Constraint> dedup;
  // Second, update the constraint graph
  for (size_t i = 0; i < cg.constraintSize(); i++) {
    ConstraintGraph::ConsID id(i);

    auto pcons = cg.tryGetConstraint(id);
    if (pcons == nullptr) {
      continue;
    }

    auto &cons = *pcons;

    auto rep_obj_id = cons.rep();
    auto src_obj_id = cons.src();
    auto dest_obj_id = cons.dest();
    auto &src_rep_node = graph.getNode<OptNode>(objToNode(src_obj_id));
    auto &rep_rep_node = graph.getNode<OptNode>(objToNode(rep_obj_id));
    auto &dest_rep_node = graph.getNode<OptNode>(objToNode(dest_obj_id));
    auto src_rep_id = omap.getRep(nodeToObj(src_rep_node.id()));
    auto dest_rep_id = omap.getRep(nodeToObj(dest_rep_node.id()));
    auto rep_rep_id = omap.getRep(nodeToObj(rep_rep_node.id()));

    /*
    // if (llvm::isa<HCDNode>(src_rep_node)) {
      if (rep_obj_id != rep_rep_id || src_obj_id != src_rep_id || dest_obj_id !=
          dest_rep_id) {
        llvm::dbgs() << "Remapping:\n";
      }
      if (rep_obj_id != rep_rep_id) {
        llvm::dbgs() << "  rep: " << rep_obj_id << " -> " <<
          rep_rep_id  << "\n";
      }
    // }
    */
    cons.updateRep(rep_rep_id);

    if (cons.type() == ConstraintType::AddressOf) {
      /*
      // if (llvm::isa<HCDNode>(src_rep_node)) {
        if (dest_obj_id != dest_rep_id) {
          llvm::dbgs() << "  src: " << src_obj_id << " -> " <<
            src_obj_id << "\n";
          llvm::dbgs() << "  dest: " << dest_obj_id << " -> " <<
            dest_rep_id << "\n";
        }
      // }
      */
      cons.retarget(src_obj_id, dest_rep_id);
    } else {
      /*
      // if (llvm::isa<HCDNode>(src_rep_node)) {
        if (src_obj_id != src_rep_id || dest_obj_id != dest_rep_id) {
          llvm::dbgs() << "  src: " << src_obj_id << " -> " <<
            src_rep_id << "\n";
          llvm::dbgs() << "  dest: " << dest_obj_id << " -> " <<
            dest_rep_id << "\n";
        }
      // }
      */
      cons.retarget(src_rep_id, dest_rep_id);
    }

    if (src_rep_node.isNonPtr() || dest_rep_node.isNonPtr()) {
      /*
      // if (llvm::isa<HCDNode>(src_rep_node)) {
        llvm::dbgs() << "Removing non-ptr: " << id << ": " <<
          cg.getConstraint(id) << "\n";
        if (src_rep_node.isNonPtr()) {
          llvm::dbgs() << "  reason: non-ptr src: " <<
            src_rep_node.id() << "\n";
        }

        if (dest_rep_node.isNonPtr()) {
          llvm::dbgs() << "  reason: non-ptr dest: " << dest_rep_node.id()
            << "\n";
        }
      // }
      */
      cg.removeConstraint(id);
      num_removed++;
      continue;
    }

    // If we have a copy to self, delete it
    if (cons.type() == ConstraintType::Copy &&
        cons.src() == cons.dest() && cons.offs() == 0) {
      /*
      // if (llvm::isa<HCDNode>(src_rep_node)) {
        llvm::dbgs() << "Removing copy to self: " << id << ": " <<
          cg.getConstraint(id) << "\n";
      // }
      */
      cg.removeConstraint(id);
      num_removed++;
      // FIXME: Do I need to check dedup with this?  probably not...
      continue;
    }

    auto it = dedup.find(cons);
    if (it == std::end(dedup)) {
      dedup.insert(cons);
    } else {
      /*
      // if (llvm::isa<HCDNode>(src_rep_node)) {
        llvm::dbgs() << "Removing duplicate: " << id << ": " <<
          cg.getConstraint(id) << "\n";
      // }
      */
      cg.removeConstraint(id);
      num_removed++;
    }
  }

  std::map<ObjectMap::ObjID, ConstraintGraph::IndirectCallInfo>
    new_indirect_calls;
  // Also manage indirect function calls?:
  // FALSE: We haven't inserted constraints for indirect function calls yet
  //    We just need to update the ObjIDs in the ConstraintGraph
  std::for_each(cg.indir_begin(), cg.indir_end(),
      [&new_indirect_calls, &omap]
      (std::pair<const ObjectMap::ObjID,
         ConstraintGraph::IndirectCallInfo> & pr) {
    auto new_key_id = omap.getRep(pr.first);

    auto &info = pr.second;

    auto new_callee_id = omap.getRep(info.callee());

    info.setCallee(new_callee_id);

    for (auto &arg_id : info) {
      arg_id = omap.getRep(arg_id);
    }

    new_indirect_calls.emplace(new_key_id,
      std::move(info));
  });

  cg.updateIndirectCalls(std::move(new_indirect_calls));

  return num_removed;
}
//}}}

// HVN {{{
class HVNNode : public OptNode {
  //{{{
 public:
  static const int32_t PENonPtr = 0;

  typedef typename SEG::NodeID NodeID;

  explicit HVNNode(NodeID node_id) :
    OptNode(NodeKind::HVNNode, node_id) { }

  void addPtsTo(int32_t id) {
    ptsto_.set(id);
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

  bool isNonPtr() override {
    auto ret = ptsto().test(PENonPtr);
    assert(!ret || ptsto().count() == 1);
    return ret;
  }

  void unite(SEG &seg, SEG::Node &n) override {
    auto &node = cast<HVNNode>(n);

    indirect_ |= node.indirect();
    ptsto() |= node.ptsto();

    node.ptsto().clear();

    SEG::Node::unite(seg, n);
  }

  // For LLVM RTTI {{{
  // NOTE: We don't use RTTI with HVNNodes...
  static bool classof(const SEG::Node *node) {
    return node->getKind() == NodeKind::HVNNode;
  }
  //}}}

  // Dot print support {{{
  void print_label(dbg_ostream &o, const ObjectMap &) const override {
    char idr_chr = indirect() ? 'I' : 'D';
    o << id() << " (" << idr_chr << ")" << ":";
    for (auto id : ptsto_) {
      o << " " << id;
    }
  }
  //}}}

 private:
  bool indirect_ = false;
  Bitmap ptsto_;
  //}}}
};

class HVNData {
  //{{{
 public:
  int32_t getNextPE() {
    return nextPE_++;
  }

  int32_t getGEPPE(SEG::NodeID node_id, int32_t offs) {
    auto it = gepToPE_.find(std::make_pair(node_id, offs));

    if (it == std::end(gepToPE_)) {
      auto rp = gepToPE_.emplace(std::make_pair(node_id, offs), getNextPE());
      assert(rp.second);
      it = rp.first;
    }

    return it->second;
  }

  int32_t getHashValue(const HVNNode &node) {
    auto &ptsto = node.ptsto();

    auto it = hashValueMap_.find(ptsto);
    if (it == std::end(hashValueMap_)) {
      auto rv = hashValueMap_.emplace(ptsto, getNextPE());
      assert(rv.second);
      it = rv.first;
    }

    return it->second;
  }

  int32_t getPEForID(SEG::NodeID id) {
    auto it = idToPE_.find(id);
    if (it == std::end(idToPE_)) {
      auto rv = idToPE_.emplace(id, getNextPE());
      assert(rv.second);
      it = rv.first;
    }

    return it->second;
  }

 private:
  // 0 is non-ptr
  int32_t nextPE_ = 1;

  std::map<std::pair<SEG::NodeID, int32_t>, int32_t> gepToPE_;

  std::unordered_map<Bitmap, int32_t, BitmapHash> hashValueMap_;

  std::unordered_map<SEG::NodeID, int32_t, SEG::NodeID::hasher> idToPE_;
  //}}}
};

// Does HVN optimization on offline graph constructed from cg, merges optimized
//   ids in omap and cg
// This is actually HU...
// Returns the number of removed constraints
int32_t HVN(ConstraintGraph &cg, ObjectMap &omap) {
  // Iterate the cg, and create a node for each constraint
  // First calculate the number of nodes needed:

  SEG hvn_graph;
  HVNData data;

  // retruns the largest id in the constraint graph
  auto max_src_dest_id = cg.getMaxID();
  // Now, create a node for each possible destination:
  for (int32_t i = 0; i < max_src_dest_id.val()+1; i++) {
    auto node_id = hvn_graph.addNode<HVNNode>();
    assert(node_id.val() == i);

    // Force objects and indirect calls to be indirect
    //  -- This isn't always managed properly in the next step, due to the
    //     arithmetic associated with object locations.  This handles it
    auto obj_id = nodeToObj(node_id);
    // if (!omap.isValue(obj_id) || hvn_graph.isIndirCall(obj_id))
    if (!omap.isValue(obj_id)) {
      auto &node = hvn_graph.getNode<HVNNode>(node_id);
      node.setIndirect();
    }
  }

  // Also, set all indirect call arg and return nodes to indirect:
  std::for_each(cg.indir_begin(), cg.indir_end(),
      [&hvn_graph]
      (const std::pair<const ObjectMap::ObjID,
           ConstraintGraph::IndirectCallInfo> &pr) {
    // Create an indir call cons
    // Populate w/ callsite info
    auto callinst = pr.first;
    auto &call_info = pr.second;

    // If this returns a pointer, that return is an indirect node
    if (call_info.isPointer()) {
      hvn_graph.getNode<HVNNode>(objToNode(callinst)).setIndirect();
    }

    // Each argument id is an indirect node
    for (auto arg_id : call_info) {
      hvn_graph.getNode<HVNNode>(objToNode(arg_id)).setIndirect();
    }
  });

  // Now, fill in the graph edges:
  std::set<SEG::NodeID> touched;
  for (const auto &pcons : cg) {
    if (pcons == nullptr) {
      continue;
    }
    auto dest_node_id = objToNode(pcons->dest());
    auto &dest_node = hvn_graph.getNode<HVNNode>(dest_node_id);
    auto src_node_id = objToNode(pcons->src());
    auto &src_node = hvn_graph.getNode<HVNNode>(src_node_id);

    /*
    auto &rep_node = hvn_graph.getNode<HVNNode>(objToNode(pcons->rep()));
    if (rep_node.id() == SEG::NodeID(366)) {
      llvm::dbgs() << "Have node with dest 366: " << *pcons << "\n";
    }

    if (src_node.id() == SEG::NodeID(366)) {
      llvm::dbgs() << "Have node with src 366: " << *pcons << "\n";
    }

    if (dest_node.id() == SEG::NodeID(366)) {
      llvm::dbgs() << "Have node with rep 366: " << *pcons << "\n";
    }

    if (dest_node.id() == SEG::NodeID(354)) {
      llvm::dbgs() << "Have node with dest 354: " << *pcons << "\n";
    }

    if (src_node.id() == SEG::NodeID(354)) {
      llvm::dbgs() << "Have node with src 354: " << *pcons << "\n";
    }

    if (rep_node.id() == SEG::NodeID(354)) {
      llvm::dbgs() << "Have node with rep 354: " << *pcons << "\n";
    }
    */

    touched.insert(dest_node_id);
    touched.insert(src_node_id);

    // Handle the edge addition appropriately
    switch (pcons->type()) {
      case ConstraintType::Load:
        // Load cons cause the dest to be indirect, but add no edges
        dest_node.setIndirect();
        break;
      case ConstraintType::Store:
        // Store cons are ignored
        // However, we need to ensure that the constraint is not optimized
        //   out, so we set the node to be indirect
        hvn_graph.getNode<HVNNode>(objToNode(pcons->rep())).setIndirect();
        break;
      case ConstraintType::AddressOf:
        // Alloc cons cause the dest to be indirect, no need to put objects in
        //   the graph (NOTE: They are set to indirect above)
        dest_node.setIndirect();
        break;
      case ConstraintType::Copy:
        // Copy cons:
        // Without offsets are edges
        if (pcons->offs() == 0) {
          dest_node.addPred(hvn_graph, src_node.id());
        // With offsets create a new PE, labeled by the src, offs combo
        } else {
          dest_node.addPtsTo(data.getGEPPE(src_node.id(), pcons->offs()));
        }
        break;
    }
  }

  // Set any untouched nodes to be an "indirect node" so it isn't incorrectly
  //   merged (since the untouched nodes may have been previously merged when
  //   running HRU, we could cause incorrect points-to sets by merging them)
  for (auto &pnode : hvn_graph) {
    auto &node = cast<HVNNode>(*pnode);
    if (touched.find(node.id()) == std::end(touched)) {
      node.setIndirect();
    }
  }

  // Calculate HVN algorithm:
  //   Run Tarjans to find SCCs
  //     Unite any nodes in scc (maintain indirection conservatively)
  //     NOTE: This is done automatically by the HVNNode class (overriding
  //         unite)
  //   On topological traversal:
  //     Merge PE sets with any preds PEs

  // This is our tarjans topological order visit function
  //   Here we calculate the appropriate PE set for the node, given its preds
  auto traverse_pe = [&data, &hvn_graph] (const SEG::Node &nd) {
    auto &node = cast<HVNNode>(nd);

    // llvm::dbgs() << "visit: " << node.id() << "\n";

    // If node is indirect, add a new PE
    if (node.indirect()) {
      node.addPtsTo(data.getNextPE());
    }

    // Now, unite any pred ids:
    for (auto pred_id : node.preds()) {
      auto &pred_node = hvn_graph.getNode<HVNNode>(pred_id);

      // skip pointers to self
      if (pred_node.id() == node.id()) {
        continue;
      }

      // If the pred node isn't a non_ptr
      if (!pred_node.ptsto().test(HVNNode::PENonPtr)) {
        node.ptsto().set(data.getHashValue(pred_node));
      }

      if (node.ptsto().empty()) {
        node.addPtsTo(HVNNode::PENonPtr);
      }
    }
  };

  // hvn_graph.printDotFile("HVNStart.dot", *g_omap);
  // Finally run Tarjan's:
  RunTarjans<decltype(should_visit_default), decltype(traverse_pe)>
    (hvn_graph, should_visit_default, traverse_pe);

  // hvn_graph.printDotFile("HVNDone.dot", *g_omap);

  // Now, use PE set as index into PE mapping, assign equivalent PEs
  std::map<Bitmap, SEG::NodeID, BitmapLT> pts_to_pe;

  // Find equiv classes for each node, unify the nodes in the class
  for (auto &pnode : hvn_graph) {
    auto &node = cast<HVNNode>(*pnode);

    auto &ptsto = node.ptsto();

    if (ptsto.empty() || ptsto.test(HVNNode::PENonPtr)) {
      ptsto.clear();
      ptsto.set(HVNNode::PENonPtr);
    }

    auto it = pts_to_pe.find(ptsto);

    if (it == std::end(pts_to_pe)) {
      pts_to_pe.emplace(ptsto, node.id());
    } else {
      auto &rep_node = hvn_graph.getNode<HVNNode>(it->second);

      /*
      if (rep_node.id() == SEG::NodeID(4957) ||
          node.id() == SEG::NodeID(4957)) {
        llvm::dbgs() << "  merge " << node.id() << " with " <<
          rep_node.id() << "\n";
      }

      if (rep_node.id() == SEG::NodeID(3441) ||
          node.id() == SEG::NodeID(3441)) {
        llvm::dbgs() << "  merge " << node.id() << " with " <<
          rep_node.id() << "\n";
      }

      if (rep_node.id() == SEG::NodeID(3440) ||
          node.id() == SEG::NodeID(3440)) {
        llvm::dbgs() << "  merge " << node.id() << " with " <<
          rep_node.id() << "\n";
      }
      if (rep_node.id() == SEG::NodeID(6509) ||
          node.id() == SEG::NodeID(6509)) {
        llvm::dbgs() << "  merge " << node.id() << " with " <<
          rep_node.id() << "\n";
      }
      */
      rep_node.unite(hvn_graph, node);
    }
  }

  // Finally, adjust omap and CG so all nodes have remapped ids according to the
  //   elected leaders

  auto num_removed = updateAndersConstraints(cg, omap, hvn_graph,
      max_src_dest_id);

  return num_removed;
}
//}}}

// HU {{{
typedef HVNNode AndersHUNode;
typedef HVNData AndersHUData;

int32_t HU(ConstraintGraph &cg, ObjectMap &omap) {
  // Iterate the cg, and create a node for each constraint
  // First calculate the number of nodes needed:

  SEG hu_graph;
  AndersHUData data;

  // retruns the largest id in the constraint graph
  auto max_src_dest_id = cg.getMaxID();
  // Now, create a node for each possible destination:
  for (int32_t i = 0; i < max_src_dest_id.val()+1; i++) {
    auto node_id = hu_graph.addNode<AndersHUNode>();
    assert(node_id.val() == i);

    // Force objects and indirect calls to be indirect
    //  -- This isn't always managed properly in the next step, due to the
    //     arithmetic associated with object locations.  This handles it
    auto obj_id = nodeToObj(node_id);
    // if (!omap.isValue(obj_id) || hu_graph.isIndirCall(obj_id))
    if (!omap.isValue(obj_id)) {
      auto &node = hu_graph.getNode<AndersHUNode>(node_id);
      node.setIndirect();
      node.addPtsTo(data.getNextPE());
    }
  }

  // Also, set all indirect call arg and return nodes to indirect:
  std::for_each(cg.indir_begin(), cg.indir_end(),
      [&hu_graph, &data]
      (const std::pair<const ObjectMap::ObjID,
           ConstraintGraph::IndirectCallInfo> &pr) {
    // Create an indir call cons
    // Populate w/ callsite info
    auto callinst = pr.first;
    auto &call_info = pr.second;

    // If this returns a pointer, that return is an indirect node
    if (call_info.isPointer()) {
      auto &node = hu_graph.getNode<AndersHUNode>(objToNode(callinst));
      node.setIndirect();
      node.addPtsTo(data.getNextPE());
    }

    // Each argument id is an indirect node
    for (auto arg_id : call_info) {
      auto &node = hu_graph.getNode<AndersHUNode>(objToNode(arg_id));
      node.setIndirect();
      node.addPtsTo(data.getNextPE());
    }
  });

  // Now, fill in the graph edges:
  std::set<SEG::NodeID> touched;
  for (const auto &pcons : cg) {
    if (pcons == nullptr) {
      continue;
    }
    auto dest_node_id = objToNode(pcons->dest());
    auto &dest_node = hu_graph.getNode<AndersHUNode>(dest_node_id);
    auto src_node_id = objToNode(pcons->src());
    auto &src_node = hu_graph.getNode<AndersHUNode>(src_node_id);

    /*
    auto &rep_node = hu_graph.getNode<AndersHUNode>(objToNode(pcons->rep()));
    if (rep_node.id() == SEG::NodeID(366)) {
      llvm::dbgs() << "Have node with dest 366: " << *pcons << "\n";
    }

    if (src_node.id() == SEG::NodeID(366)) {
      llvm::dbgs() << "Have node with src 366: " << *pcons << "\n";
    }

    if (dest_node.id() == SEG::NodeID(366)) {
      llvm::dbgs() << "Have node with rep 366: " << *pcons << "\n";
    }

    if (dest_node.id() == SEG::NodeID(354)) {
      llvm::dbgs() << "Have node with dest 354: " << *pcons << "\n";
    }

    if (src_node.id() == SEG::NodeID(354)) {
      llvm::dbgs() << "Have node with src 354: " << *pcons << "\n";
    }

    if (rep_node.id() == SEG::NodeID(354)) {
      llvm::dbgs() << "Have node with rep 354: " << *pcons << "\n";
    }
    */

    touched.insert(dest_node_id);
    touched.insert(src_node_id);

    // Handle the edge addition appropriately
    switch (pcons->type()) {
      case ConstraintType::Load:
        // Load cons cause the dest to be indirect, but add no edges
        dest_node.setIndirect();
        // Nodes are equivalent if their source input set is (only for
        //   andersens, as flow information may change this for sfs)
        dest_node.addPtsTo(data.getPEForID(src_node.id()));
        // dest_node.addPtsTo(data.getNextPE());
        break;
      case ConstraintType::Store:
        // Store cons are ignored
        // However, we need to ensure that the constraint is not optimized
        //   out, so we set the node to be indirect
        hu_graph.getNode<AndersHUNode>(objToNode(pcons->rep())).setIndirect();
        break;
      case ConstraintType::AddressOf:
        // Alloc cons cause the dest to be indirect, no need to put objects in
        //   the graph (NOTE: They are set to indirect above)
        dest_node.setIndirect();
        dest_node.addPtsTo(data.getNextPE());
        break;
      case ConstraintType::Copy:
        // Copy cons:
        // Without offsets are edges
        if (pcons->offs() == 0) {
          dest_node.addPred(hu_graph, src_node.id());
        // With offsets create a new PE, labeled by the src, offs combo
        } else {
          dest_node.addPtsTo(data.getGEPPE(src_node.id(), pcons->offs()));
        }
        break;
    }
  }

  // Set any untouched nodes to be an "indirect node" so it isn't incorrectly
  //   merged (since the untouched nodes may have been previously merged when
  //   running HRU, we could cause incorrect points-to sets by merging them)
  for (auto &pnode : hu_graph) {
    auto &node = cast<AndersHUNode>(*pnode);
    if (touched.find(node.id()) == std::end(touched)) {
      node.setIndirect();
      node.addPtsTo(data.getNextPE());
    }
  }

  // Calculate HU algorithm:
  //   Run Tarjans to find SCCs
  //     Unite any nodes in scc (maintain indirection conservatively)
  //     NOTE: This is done automatically by the AndersHUNode class (overriding
  //         unite)
  //   On topological traversal:
  //     Merge PE sets with any preds PEs

  // This is our tarjans topological order visit function
  //   Here we calculate the appropriate PE set for the node, given its preds
  auto traverse_pe = [&data, &hu_graph] (const SEG::Node &nd) {
    auto &node = cast<AndersHUNode>(nd);

    // llvm::dbgs() << "visit: " << node.id() << "\n";


    // Now, unite any pred ids:
    for (auto pred_id : node.preds()) {
      auto &pred_node = hu_graph.getNode<AndersHUNode>(pred_id);

      // skip pointers to self
      if (pred_node.id() == node.id()) {
        continue;
      }

      // If the pred node isn't a non_ptr
      if (!pred_node.ptsto().test(AndersHUNode::PENonPtr)) {
        node.ptsto() |= pred_node.ptsto();
      }

      if (node.ptsto().empty()) {
        node.addPtsTo(AndersHUNode::PENonPtr);
      }
    }
  };

  // hu_graph.printDotFile("HUStart.dot", *g_omap);
  // Finally run Tarjan's:
  RunTarjans<decltype(should_visit_default), decltype(traverse_pe)>
    (hu_graph, should_visit_default, traverse_pe);

  // hu_graph.printDotFile("HUDone.dot", *g_omap);

  // Now, use PE set as index into PE mapping, assign equivalent PEs
  std::unordered_map<Bitmap, SEG::NodeID, BitmapHash> pts_to_pe;

  // Find equiv classes for each node, unify the nodes in the class
  for (auto &pnode : hu_graph) {
    auto &node = cast<AndersHUNode>(*pnode);

    auto &ptsto = node.ptsto();

    if (ptsto.empty() || ptsto.test(AndersHUNode::PENonPtr)) {
      ptsto.clear();
      ptsto.set(AndersHUNode::PENonPtr);
    }

    auto it = pts_to_pe.find(ptsto);

    if (it == std::end(pts_to_pe)) {
      pts_to_pe.emplace(ptsto, node.id());
    } else {
      auto &rep_node = hu_graph.getNode<AndersHUNode>(it->second);

      /*
      if (rep_node.id() == SEG::NodeID(4957) ||
          node.id() == SEG::NodeID(4957)) {
        llvm::dbgs() << "  merge " << node.id() << " with " <<
          rep_node.id() << "\n";
      }

      if (rep_node.id() == SEG::NodeID(3441) ||
          node.id() == SEG::NodeID(3441)) {
        llvm::dbgs() << "  merge " << node.id() << " with " <<
          rep_node.id() << "\n";
      }

      if (rep_node.id() == SEG::NodeID(3440) ||
          node.id() == SEG::NodeID(3440)) {
        llvm::dbgs() << "  merge " << node.id() << " with " <<
          rep_node.id() << "\n";
      }
      */
      if (rep_node.id() == SEG::NodeID(6509) ||
          node.id() == SEG::NodeID(6509)) {
        llvm::dbgs() << "  merge " << node.id() << " with " <<
          rep_node.id() << "\n";
      }
      rep_node.unite(hu_graph, node);
    }
  }

  // Finally, adjust omap and CG so all nodes have remapped ids according to the
  //   elected leaders

  auto num_removed = updateAndersConstraints(cg, omap, hu_graph,
      max_src_dest_id);

  return num_removed;
}
//}}}


// HRU {{{
void HRU(ConstraintGraph &cg, ObjectMap &omap, int32_t min_removed) {
  int32_t itr = 0;
  int32_t num_removed;
  do {
    llvm::dbgs() << "HRU iter: " << itr << "\n";
    num_removed = HU(cg, omap);
    // num_removed = HVN(cg, omap);
    llvm::dbgs() << "  num_removed: " << num_removed << "\n";
    itr++;
  } while (num_removed > min_removed);
}
//}}}

// HCD {{{
class HCDNode : public OptNode {
  //{{{
 public:
  typedef typename SEG::NodeID NodeID;

  explicit HCDNode(NodeID node_id) :
    OptNode(NodeKind::HCDNode, node_id) { }

  void unite(SEG &seg, SEG::Node &n) override {
    auto &node = cast<HCDNode>(n);

    // If we are not both ref nodes, the non-ref should be the leader
    if (ref() && !node.ref()) {
      node.unite(seg, *this);
      return;
    }

    /*
    llvm::dbgs() << "Merging: " << id() << (ref() ? " R " : " D ") << " and "
        << node.id() << (node.ref() ? " R " : " D ") << "\n";
    */

    // Add any ref nodes to our ref set
    if (node.ref()) {
      refReps_.insert(node.id());
    }
    refReps_.insert(std::begin(node.refReps_), std::end(node.refReps_));

    SEG::Node::unite(seg, n);
  }

  // setters {{{
  void setRef() {
    ref_ = true;
  }
  //}}}

  // Accessors {{{
  bool ref() const {
    return ref_;
  }

  const std::set<NodeID> &getRefs() const {
    return refReps_;
  }

  bool isNonPtr() override {
    return false;
  }
  //}}}

  // For LLVM RTTI {{{
  // NOTE: We don't use RTTI with HCDNode...
  static bool classof(const SEG::Node *n) {
    return n->getKind() == NodeKind::HCDNode;
  }
  //}}}

  // Dot print support {{{
  void print_label(dbg_ostream &o, const ObjectMap &) const override {
    char idr_chr = ref() ? 'R' : 'D';
    o << id() << " (" << idr_chr << ")";
  }
  //}}}

 private:
  bool ref_ = false;
  std::set<NodeID> refReps_;
  //}}}
};

class HCDData {
  //{{{
 public:
  explicit HCDData(SEG &hcd_graph) : hcdGraph_(hcd_graph) { }

  HCDData(const HCDData &) = delete;
  HCDData &operator=(const HCDData &) = delete;

  HCDNode &getRefNode(SEG::NodeID id) {
    auto ref_it = nodeToRef_.find(id);

    if (ref_it == std::end(nodeToRef_)) {
      auto new_node_id = hcdGraph_.addNode<HCDNode>();
      auto &hcd_node = hcdGraph_.getNode<HCDNode>(new_node_id);
      hcd_node.setRef();

      auto rc = nodeToRef_.emplace(id, new_node_id);
      refToNode_.emplace(new_node_id, id);
      assert(rc.second);
      ref_it = rc.first;
    }

    auto &ret = hcdGraph_.getNode<HCDNode>(ref_it->second);
    assert(ret.ref());
    return ret;
  }

  HCDNode &getNodeDeref(SEG::NodeID id) {
    auto ref_it = refToNode_.find(id);

    assert(ref_it != std::end(refToNode_));

    auto &ret = hcdGraph_.getNode<HCDNode>(ref_it->second);
    assert(!ret.ref());
    return ret;
  }

 private:
  SEG &hcdGraph_;
  std::map<SEG::NodeID, SEG::NodeID> nodeToRef_;
  std::map<SEG::NodeID, SEG::NodeID> refToNode_;
  //}}}
};

void SpecAnders::HCD(ConstraintGraph &graph, ObjectMap &omap) {
  // Okay, need to get our hcd constarints....
  SEG hcd_graph;

  HCDData data(hcd_graph);

  // Now, initailize the nodelist
  auto max_id = graph.getMaxID();

  // Fill up the offline constraint graph
  for (ObjectMap::ObjID obj_id(0); obj_id <= max_id; obj_id++) {
    if_debug_enabled(auto node_id = )
      hcd_graph.addNode<HCDNode>();
    assert(node_id.val() == obj_id.val());
  }

  // NOTE: This is done in HCDData...
  // Denote which edges in the graph are indirect
  //  Iterate each constraint, if it is the dest of a load, it loads to/stores
  //  from a REF node.  We will need to add a REF node,
  //      and make a REF to nodeid mapping...

  // Populate the edges of the offline constraint graph:
  for (auto &pcons : graph) {
    if (pcons == nullptr) {
      continue;
    }
    auto dest_node_id = objToNode(pcons->dest());
    auto &dest_node = hcd_graph.getNode<HCDNode>(dest_node_id);
    auto src_node_id = objToNode(pcons->src());
    auto &src_node = hcd_graph.getNode<HCDNode>(src_node_id);

    switch (pcons->type()) {
      case ConstraintType::Load:
        //   Load -- REF(src) -> dest
        {
          // Get the ref of this source:
          auto &src_ref = data.getRefNode(src_node.id());

          // Now, add some edges
          dest_node.addPred(hcd_graph, src_ref.id());
        }
        break;
      case ConstraintType::Store:
        //   Store -- src -> REF(dest)
        {
          auto &dest_ref = data.getRefNode(dest_node.id());

          dest_ref.addPred(hcd_graph, src_node.id());
        }
        break;
      case ConstraintType::Copy:
        //   Copy -- normal
        //     GEP (copy w/ offset) -- Ignore
        if (pcons->offs() == 0) {
          dest_node.addPred(hcd_graph, src_node.id());
        }
        break;
      case ConstraintType::AddressOf:
        //   AddrOf -- ignore
        break;
      default:
        llvm_unreachable("HCD bad constraint type");
        break;
    }
  }

  // Use Tarjans to detect SCCs
  RunTarjans<decltype(should_visit_default), decltype(scc_visit_default)>
    (hcd_graph, should_visit_default, scc_visit_default);

  // Update our HCD data structure
  // And update our constraints/cg for any merged node ids...
  // To update constraint strucutres:
  // Iterate through each constraint:
  //   Get rep node
  //   Merge
  for (auto &pn : hcd_graph) {
    auto pnode = cast<HCDNode>(pn.get());

    // This node must either have 0 ref'd nodes, or be a ref node itself
    //   (ref nodes cannot be the leaders of non-trivial scc groups)
    assert(pnode->getRefs().size() == 0 || !pnode->ref());

    if (pnode->ref() || !pnode->isRep()) {
      continue;
    }

    auto &ref_nodes = pnode->getRefs();
    for (auto &ref_id : ref_nodes) {
      // Convert from ref_id to node_id
      auto deref_id = data.getNodeDeref(ref_id).id();
      hcdPairs_.emplace(nodeToObj(deref_id),
         nodeToObj(pnode->id()));
    }
  }

  // Handle non-ref SCCs here (update constraints/graph info)
  updateAndersConstraints(graph, omap, hcd_graph, max_id);
}
//}}}
//}}}

