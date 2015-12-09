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
#include <utility>
#include <vector>

#include "include/Debug.h"

#include "include/SpecSFS.h"

#include "include/SEG.h"
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

// optimizeConstraints {{{
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
      setObjIDRep(nodeToObj(node_id), nodeToObj(rep_id));
      omap.updateObjID(nodeToObj(node_id), nodeToObj(rep_id));
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
    auto &rep_rep_node = hu_graph.getNode<HUNode>(objToNode(rep_obj_id));
    auto &dest_rep_node = hu_graph.getNode<HUNode>(objToNode(dest_obj_id));
    auto src_rep_id = nodeToObj(src_rep_node.id());
    auto dest_rep_id = nodeToObj(dest_rep_node.id());
    auto rep_rep_id = nodeToObj(rep_rep_node.id());

    dout("Initial cons: " << cons << "\n");
    // Always change the rep
    /*
    llvm::dbgs() << "inital rep: " << ValPrint(rep_obj_id) << "\n";
    llvm::dbgs() << "Updating rep: " << rep_obj_id << " to: " << rep_rep_id <<
      "\n";
    */
    cons.updateRep(rep_rep_id);

    // Update src and dest to reps
    //   but, don't change the src_id of addr_of nodes
    if (cons.type() == ConstraintType::AddressOf) {
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
        assert(id.val() != 120638);
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
        assert(id.val() != 120638);
        graph.removeConstraint(id);
      }
    }
  }

  // Now fix up our defs, uses, and global inits w/in the CFG
  // Iterate each CFG node
  // Replace the ObjID with the rep ObjID as found in calc
  for (auto &pnode : cfg.getSEG()) {
    auto &cfg_node = cast<CFG::Node>(*pnode);

    std::set<ObjectMap::ObjID> new_uses;
    std::for_each(cfg_node.uses_begin(), cfg_node.uses_end(),
        [&hu_graph, &new_uses] (ObjectMap::ObjID use) {
      auto node_id = objToNode(use);
      auto &node = hu_graph.getNode(node_id);
      auto rep_node_id = node.id();
      auto new_use = nodeToObj(rep_node_id);
      new_uses.insert(new_use);
    });

    std::set<ObjectMap::ObjID> new_defs;
    std::for_each(cfg_node.defs_begin(), cfg_node.defs_end(),
        [&hu_graph, &new_defs] (ObjectMap::ObjID def) {
      auto node_id = objToNode(def);
      auto &node = hu_graph.getNode(node_id);
      auto rep_node_id = node.id();
      auto new_def = nodeToObj(rep_node_id);
      new_defs.insert(new_def);
    });

    cfg_node.swapDefs(new_defs);
    cfg_node.swapUses(new_uses);
  }

  // Create new objToCFG for the cfg
  std::map<ObjectMap::ObjID, CFG::CFGid> new_obj_to_cfg;
  std::for_each(cfg.obj_to_cfg_cbegin(), cfg.obj_to_cfg_cend(),
      [&new_obj_to_cfg, &hu_graph, &omap]
      (const std::pair<const ObjectMap::ObjID, CFG::CFGid> &pr) {
    auto node_id = objToNode(pr.first);
    auto &node = hu_graph.getNode(node_id);
    auto rep_id = node.id();
    auto new_obj_id = nodeToObj(rep_id);

    /*
    llvm::dbgs() << "Inserting " << new_obj_id << " to obj_to_cfg at: " <<
        pr.second << "\n";
    */

    if_debug_enabled(auto ret =)
      new_obj_to_cfg.emplace(new_obj_id, pr.second);
    assert(ret.second);
  });
  cfg.swapObjToCFG(new_obj_to_cfg);

  return false;
}
//}}}

