/*
 * Copyright (C) 2015 David Devecsery
 */

// #define SPECSFS_DEBUG
// #define SPECSFS_LOGDEBUG

#include <algorithm>
#include <map>
#include <utility>
#include <vector>

#include "include/AndersHelpers.h"
#include "include/DUG.h"
#include "include/Debug.h"
#include "include/SolveHelpers.h"
#include "include/SpecAnders.h"
#include "include/SpecSFS.h"

// SpecSFS Solve {{{
int32_t dbg_dugnodeid(DUGNode *node) {
  return node->id().val();
}

bool SpecSFS::solve(DUG &dug,
    std::map<ObjectMap::ObjID, Bitmap> dyn_constraints) {
  // Add allocs to worklist -- The ptstoset for the alloc will be updated on
  //   solve evaluation
  std::vector<ObjectMap::ObjID> dests;
  std::vector<uint32_t> priority;
  Worklist<DUGNode> work;

  logout("SOLVE\n");

  std::for_each(dug.nodes_begin(), dug.nodes_end(),
      [this, &work, &dests]
      (DUG::node_iter_type &pnd) {
    auto pnode = pnd.get();
    DUGNode &node = cast<DUGNode>(*pnode);

    if (llvm::isa<DUG::AllocNode>(pnode)) {
      // Add allocs as 0 priority entries to our heap
      work.push(&node, 0);
    }

    dests.push_back(node.dest());
    dests.push_back(node.src());
  });

  std::sort(std::begin(dests), std::end(dests));
  auto dest_it = std::unique(std::begin(dests), std::end(dests));
  dests.erase(dest_it, std::end(dests));

  // Assign a 0 prio entry for each node
  priority.assign(dug.getNumNodes(), 0);
  TopLevelPtsto pts_top(dests, std::move(dyn_constraints));

  // Solve the graph
  int32_t vtime = 1;
  uint32_t prio;
  while (auto pnd = work.pop(prio)) {
    // Don't process the node if we've processed it this round
    /*
    dout("node: " << pnd->id() << ":  Comparing prio " << prio << " < " <<
        priority[pnd->id().val()] << "\n");
    */
    if (prio < priority[pnd->id().val()]) {
      continue;
    }

    /*
    dout("node: " << pnd->id() << ":  assigning priority to: " << vtime <<
        "\n");
    */
    priority[pnd->id().val()] = vtime;
    vtime++;

    dout("Processing node: " << pnd->id() << "\n");
    pnd->process(dug, pts_top, work, priority);
  }

  // Data is held in pts_top
  // Move our local set of data into the class's
  pts_top_ = std::move(pts_top);

  // All Done!
  return false;
}

void DUG::AllocNode::process(DUG &dug, TopLevelPtsto &pts_top,
    Worklist<DUGNode> &work, const std::vector<uint32_t> &priority) {
  dout("Process alloc start\n");
  // Update the top level variables for this alloc
  PtstoSet &dest_pts = pts_top.at(dest(), offset());

  logout("n " << id() << "\n");
  logout("t " << 0 << "\n");

  logout("r " << rep() << "\n");
  logout("s " << src() << "\n");
  logout("d " << dest() << " " << dest_pts << "\n");
  logout("f " << offset() << "\n");

  bool change = dest_pts.set(ObjectMap::getOffsID(src(), offset()));

  dout("  pts_top[" << dest() << "] + " << offset() << " is now: "
      << dest_pts << "\n");
  logout("D " << dest() << " " << dest_pts << "\n");

  // Add all top level variables updated to worklist
  if (change) {
    std::for_each(succ_begin(), succ_end(),
        [&dug, &work, &priority](DUG::DUGid succ_id) {
      auto &nd = dug.getNode(succ_id);
      dout("  Pushing nd to work: " << nd.id() << "\n");
      work.push(&nd, priority[nd.id().val()]);
    });
  }
}

void DUG::CopyNode::process(DUG &dug, TopLevelPtsto &pts_top,
    Worklist<DUGNode> &work, const std::vector<uint32_t> &priority) {
  dout("Process copy start\n");

  // Update the top level variables for this copy
  PtstoSet &dest_pts = pts_top.at(dest());

  // Get this offset for top level variables
  PtstoSet &src_pts = pts_top.at(src());

  dout("  src_top[" << src() << "] + " << offset() << " is: " <<
      src_pts << "\n");

  logout("n " << id() << "\n");
  logout("t " << 4 << "\n");

  logout("r " << rep() << "\n");
  logout("s " << src() << " " << src_pts << "\n");
  logout("d " << dest() << " " << dest_pts << "\n");
  logout("f " << offset() << "\n");

  // bool change = (dest_pts |= src_pts);
  auto &struct_list = dug.getStructInfo();
  bool change = dest_pts.orOffs(src_pts, offset(), struct_list);

  logout("D " << dest() << " " << dest_pts << "\n");
  dout("  pts_top[" << dest() << "] is now: " << dest_pts << "\n");

  // Add all updated successors to worklist
  if (change) {
    std::for_each(succ_begin(), succ_end(),
        [&dug, &work, &priority](DUG::DUGid succ_id) {
      auto &nd = dug.getNode(succ_id);
      dout("  Pushing nd to work: " << nd.id() << "\n");
      work.push(&nd, priority[nd.id().val()]);
    });
  }
}

void DUG::LoadNode::processShared(DUG &dug, TopLevelPtsto &pts_top,
    Worklist<DUGNode> &work, const std::vector<uint32_t> &priority,
    PtstoGraph &in) {
  assert(!isDUGRep());
  dout("Process load start\n");
  // add a ptsto from src to the values contained in our partition set from the
  //    top level varaible dest
  // Add all successors to worklist
  //
  // For each variable potentially pointed to by dest (from top)
  //   For each object potentially pointed to by that variable (from our IN set)
  //     Add that edge to dest
  //
  // If we added any edges:
  //   Add all successors to work
  PtstoSet &src_pts = pts_top.at(src());
  dout("value at src() (" << src() << ")\n");
  dout("value at dest() (" << dest() << ")\n");
  PtstoSet &dest_pts = pts_top.at(dest());
  dout("SHARED\n");
  dout("Load is " << rep() << "\n");

  logout("SHARED\n");
  logout("n " << id() << "\n");
  logout("t " << 11 << "\n");

  logout("r " << rep() << "\n");
  logout("s " << src() << " " << src_pts << "\n");
  logout("d " << dest() << " " << dest_pts << "\n");

  logout("i " << in << "\n");

  bool changed = false;
  std::for_each(std::begin(src_pts), std::end(src_pts),
      [this, &dug, &work, &changed, &dest_pts, &in]
      (DUG::ObjID id) {
    dout("  id is: " << id << "\n");
    dout("  in is: " << in << "\n");

    auto &pts = in.at(id);

    dout("  pts is: " << pts << "\n");

    changed |= (dest_pts |= pts);
  });

  logout("D " << dest() << " " << dest_pts << "\n");

  if_debug(
    dout("  pts_top[" << dest() << "] is now: ");
    std::for_each(std::begin(dest_pts), std::end(dest_pts),
        [this](DUG::ObjID obj_id) {
      dout(" " << obj_id);
    });
    dout("\n"));

  // Also propigate address taken info
  // We need to update the ptsto of all of our part_successors
  if (in.hasChanged()) {
    std::for_each(std::begin(part_succs_), std::end(part_succs_),
        [this, &dug, &work, &priority, &pts_top, &in]
        (std::pair<DUG::PartID, DUG::DUGid> &part_pr) {
      auto part_id = part_pr.first;
      auto dug_id = part_pr.second;

      auto &nd = dug.getNode(dug_id);

      bool ch = nd.in().orPart(in, dug.objToPartMap(), part_id);

      if (ch) {
        work.push(&nd, priority[nd.id().val()]);
      }
    });
  }

  dout("  Load dest is: " << dest() << "\n");
  dout("  Load src is: " << src() << "\n");
  // If our input set has changed, we alert our succs
  if (changed) {
    std::for_each(succ_begin(), succ_end(),
        [&dug, &work, &priority](DUG::DUGid succ_id) {
      auto &nd = dug.getNode(succ_id);
      dout("  Pushing nd to work: " << nd.id() << "\n");
      work.push(&nd, priority[nd.id().val()]);
    });
  }
  dout("ENDSHARED\n");
  logout("ENDSHARED\n");
}

void DUG::LoadNode::process(DUG &dug, TopLevelPtsto &pts_top,
    Worklist<DUGNode> &work, const std::vector<uint32_t> &priority) {
  assert(isDUGRep());
  dout("Process load start\n");
  // add a ptsto from src to the values contained in our partition set from the
  //    top level varaible dest
  // Add all successors to worklist
  //
  // For each variable potentially pointed to by dest (from top)
  //   For each object potentially pointed to by that variable (from our IN set)
  //     Add that edge to dest
  //
  // If we added any edges:
  //   Add all successors to work
  PtstoSet &src_pts = pts_top.at(src());
  dout("value at src() (" << src() << ")\n");
  dout("value at dest() (" << dest() << ")\n");
  PtstoSet &dest_pts = pts_top.at(dest());
  dout("Load is " << rep() << "\n");

  logout("n " << id() << "\n");
  logout("t " << 2 << "\n");

  logout("r " << rep() << "\n");
  logout("s " << src() << " " << src_pts << "\n");
  logout("d " << dest() << " " << dest_pts << "\n");

  logout("i " << in() << "\n");

  bool changed = false;
  std::for_each(std::begin(src_pts), std::end(src_pts),
      [this, &dug, &work, &changed, &dest_pts](DUG::ObjID id) {
    dout("  id is: " << id << "\n");
    dout("  in is: " << in_ << "\n");

    PtstoSet &pts = in_.at(id);

    dout("  pts is: " << pts << "\n");

    changed |= (dest_pts |= pts);
  });

  logout("D " << dest() << " " << dest_pts << "\n");

  if_debug(
    dout("  pts_top[" << dest() << "] is now: ");
    std::for_each(std::begin(dest_pts), std::end(dest_pts),
        [this](DUG::ObjID obj_id) {
      dout(" " << obj_id);
    });
    dout("\n"));

  // Also propigate address taken info?
  // Okay... if our in-set has changed since last time we were visited (I assume
  //    it has...)
  // We need to update the ptsto of all of our part_successors

  dout("  Load dest is: " << dest() << "\n");
  dout("  Load src is: " << src() << "\n");
  // If our input set has changed, we alert our succs
  if (in().hasChanged()) {
    std::for_each(std::begin(part_succs_), std::end(part_succs_),
        [this, &dug, &work, &priority, &pts_top]
        (std::pair<DUG::PartID, DUG::DUGid> &part_pr) {
      auto part_id = part_pr.first;
      auto dug_id = part_pr.second;

      auto &nd = dug.getNode(dug_id);

      dout("  part_id is: " << part_id << "\n");

      dout("  Checking node: " << dug_id << "\n");

      auto pld_nd = dyn_cast<DUG::LoadNode>(&nd);
      if (pld_nd != nullptr && !pld_nd->isDUGRep()) {
        auto &ld_nd = *pld_nd;

        ld_nd.processShared(dug, pts_top, work, priority, in_);
      } else {
        bool ch = nd.in().orPart(in_, dug.objToPartMap(), part_id);

        if (ch) {
          dout("    Pushing nd to work: " << nd.id() << " (with prio: " <<
              priority[nd.id().val()] << ")\n");
          work.push(&nd, priority[nd.id().val()]);
        }
      }
    });

    // Clear our changed info
    in().resetChanged();
  // If in hasn't changed, we still have to run all shared, in case their inputs
  //   changed
  } else {
    std::for_each(std::begin(part_succs_), std::end(part_succs_),
        [this, &dug, &work, &priority, &pts_top]
        (std::pair<DUG::PartID, DUG::DUGid> &part_pr) {
      auto dug_id = part_pr.second;
      auto &nd = dug.getNode(dug_id);
      auto pld_nd = dyn_cast<DUG::LoadNode>(&nd);
      if (pld_nd != nullptr && !pld_nd->isDUGRep()) {
        auto &ld_nd = *pld_nd;

        ld_nd.processShared(dug, pts_top, work, priority, in_);
      }
    });
  }

  if (changed) {
    std::for_each(succ_begin(), succ_end(),
        [&dug, &work, &priority](DUG::DUGid succ_id) {
      auto &nd = dug.getNode(succ_id);
      dout("  Pushing nd to work: " << nd.id() << "\n");
      work.push(&nd, priority[nd.id().val()]);
    });
  }
}

void DUG::StoreNode::process(DUG &dug, TopLevelPtsto &pts_top,
    Worklist<DUGNode> &work, const std::vector<uint32_t> &priority) {
  dout("Process store start\n");
  dout("Store is: " << rep() << "\n");
  // if strong && concrete
  //   clear all outgoing edges from pts_top(src) from out
  //
  // Add edges from pts_top(src) to pts_top(dest) to our OUT set
  //
  // For each partition successor:
  //   For all variables in OUT
  //     add OUT(v) to their succ.IN(v)
  //     if (succ.IN.changed)
  //       Add succ to worklist
  dout("  Source is: " << src() << "\n");
  dout("  Dest is: " << dest() << "\n");
  PtstoSet &src_pts = pts_top.at(src());
  PtstoSet &dest_pts = pts_top.at(dest());
  bool change = false;

  dout("  Initial src_pts: " << src_pts << "\n");
  dout("  Initial dest_pts: " << dest_pts << "\n");

  logout("n " << id() << "\n");
  logout("t " << 1 << "\n");

  logout("r " << rep() << "\n");
  logout("s " << src() << " " << src_pts << "\n");
  logout("d " << dest() << " " << dest_pts << "\n");

  logout("i " << in() << "\n");
  logout("o " << out_ << "\n");

  // If this is a strong update, remove all outgoing edges from dest
  // NOTE: This is a strong update if we are updating a single concrete location
  if (strong() && dest_pts.size() == 1) {
    // Clear all outgoing edges from pts_top(src) from out
    dout("DOING STRONG UPDATE!!!\n");
    dout("dest is: " << dest() << "\n");
    dout("in is: " << in() << "\n");

    change |= out_.orExcept(in(), *std::begin(dest_pts));

    // Add edges to out with in
    change |= out_.assign(*std::begin(dest_pts), src_pts);
  } else {
    dout("  Weak store:\n");
    dout("    Initial out: " << out_ << "\n");
    dout("    Initial in: " << in() << "\n");
    // Combine out with in
    change |= (out_ |= in());

    // Also, add the stored element(s):
    std::for_each(std::begin(dest_pts), std::end(dest_pts),
        [this, &change, &src_pts] (ObjectMap::ObjID elm) {
      change |= out_.orElement(elm, src_pts);
    });
  }


  dout("    Final out: " << out_ << "\n");
  dout("    Final in: " << in() << "\n");
  logout("I " << in() << "\n");
  logout("O " << out_ << "\n");

  // If something changed, update all successors
  if (out_.hasChanged()) {
    dout("  Have change on node with src: " <<
      src() << ", dest: " <<
      dest() << "\n");
    // FIXME: Only do this for changed info?
    // For each successor partition of this store
    std::for_each(std::begin(part_succs_), std::end(part_succs_),
        [this, &work, &dug, &priority, &pts_top]
        (std::pair<DUG::PartID, DUG::DUGid> &part_pr) {
      auto part_id = part_pr.first;
      auto dug_id = part_pr.second;
      auto &nd = dug.getNode(dug_id);
      assert(nd.id() == dug_id);

      dout("  part_id is: " << part_id << "\n");

      dout("  Checking node: " << dug_id << "\n");

      // dout("  before in for nd is: " << nd.in() << "\n");

      auto pld_nd = dyn_cast<DUG::LoadNode>(&nd);
      if (pld_nd != nullptr && !pld_nd->isDUGRep()) {
        auto &ld_nd = *pld_nd;
        ld_nd.processShared(dug, pts_top, work, priority, out_);
      } else {
        // Update the input set of the successor node
        bool c = nd.in().orPart(out_, dug.objToPartMap(), part_id);

        // dout("  after in for nd is: " << nd.in() << "\n");

        if (c) {
          dout("    Pushing nd to work: " << nd.id() << " (with prio: " <<
              priority[nd.id().val()] << ")\n");
          // Propigate info?
          work.push(&nd, priority[nd.id().val()]);
        }
      }
    });

    out_.resetChanged();
  // Still have to run shared nodes
  } else {
    std::for_each(std::begin(part_succs_), std::end(part_succs_),
        [this, &work, &dug, &priority, &pts_top]
        (std::pair<DUG::PartID, DUG::DUGid> &part_pr) {
      auto dug_id = part_pr.second;
      auto &nd = dug.getNode(dug_id);

      auto pld_nd = dyn_cast<DUG::LoadNode>(&nd);
      if (pld_nd != nullptr && !pld_nd->isDUGRep()) {
        auto &ld_nd = *pld_nd;
        ld_nd.processShared(dug, pts_top, work, priority, out_);
      }
    });
  }
}

void DUG::PhiNode::process(DUG &dug, TopLevelPtsto &, Worklist<DUGNode> &work,
    const std::vector<uint32_t> &priority) {
  dout("Process PHI start\n");
  // For all successors:
  //   succ.IN |= IN
  // if succ.IN.changed():
  //   worklist.add(succ.IN)

  logout("n " << id() << "\n");
  logout("t " << 5 << "\n");

  logout("r " << rep() << "\n");
  logout("i " << in() << "\n");
  if (in().hasChanged()) {
    dout("  Got change in IN\n");
    std::for_each(std::begin(part_succs_), std::end(part_succs_),
        [this, &work, &dug, &priority]
        (std::pair<DUG::PartID, DUG::DUGid> &part_pr) {
      auto dug_id = part_pr.second;
      auto part_id = part_pr.first;

      auto &nd = dug.getNode(dug_id);

      dout("  Checking IN for node: " << nd.id() << "\n");
      dout("    nd.in() is " << nd.id() << "\n");
      // FIXME?? Does this need to be a part_or?
      bool ch = nd.in().orPart(in_, dug.objToPartMap(), part_id);
      if (ch) {
        dout("  Pushing nd to work: " << nd.id() << "\n");
        work.push(&nd, priority[nd.id().val()]);
      }
    });

    in().resetChanged();
  }
}

// Constant nodes! currently caused by the cold-path dynamic ptsto optimization
void DUG::ConstNode::process(DUG &dug, TopLevelPtsto &pts_top,
    Worklist<DUGNode> &work, const std::vector<uint32_t> &priority) {
  // Constant nodes only run once, as they break incoming edges
  if (!run_) {
    run_ = true;

    dout("Process const start\n");
    // Update the top level variables for this alloc
    PtstoSet &dest_pts = pts_top.at(dest(), offset());

    logout("n " << id() << "\n");
    logout("t " << 6 << "\n");

    logout("r " << rep() << "\n");
    logout("s " << src() << "\n");
    logout("d " << dest() << " " << dest_pts << "\n");
    logout("f " << offset() << "\n");

    // We clear the dest_pts, and force it to be exactly our pts
    dest_pts.clear();
    for (auto obj_id : constObjSet_) {
      dest_pts.set(obj_id);
    }

    dout("  pts_top[" << dest() << "] + " << offset() << " is now: "
        << dest_pts << "\n");

    logout("D " << dest() << " " << dest_pts << "\n");

    // NOTE: We assume we changed dest
    // Add all top level variables updated to worklist
    std::for_each(succ_begin(), succ_end(),
        [&dug, &work, &priority](DUG::DUGid succ_id) {
      auto &nd = dug.getNode(succ_id);
      dout("  Pushing nd to work: " << nd.id() << "\n");
      work.push(&nd, priority[nd.id().val()]);
    });
  }
}

// Constant nodes! currently caused by the cold-path dynamic ptsto optimization
void DUG::ConstPartNode::process(DUG &dug, TopLevelPtsto &pts_top,
    Worklist<DUGNode> &work, const std::vector<uint32_t> &priority) {
  // Constant nodes only run once, as they break incoming edges
  if (!run_) {
    run_ = true;

    dout("Process const start\n");
    // Update the top level variables for this alloc
    PtstoSet &dest_pts = pts_top.at(dest(), offset());

    logout("n " << id() << "\n");
    logout("t " << 6 << "\n");

    logout("r " << rep() << "\n");
    logout("s " << src() << "\n");
    logout("d " << dest() << " " << dest_pts << "\n");
    logout("f " << offset() << "\n");

    // We clear the dest_pts, and force it to be exactly our pts
    dest_pts.clear();
    for (auto obj_id : constObjSet_) {
      dest_pts.set(obj_id);
    }

    dout("  pts_top[" << dest() << "] + " << offset() << " is now: "
        << dest_pts << "\n");

    logout("D " << dest() << " " << dest_pts << "\n");

    // NOTE: We assume we changed dest
    // Add all top level variables updated to worklist
    std::for_each(succ_begin(), succ_end(),
        [&dug, &work, &priority]
        (DUG::DUGid succ_id) {
      auto &nd = dug.getNode(succ_id);
      dout("  Pushing nd to work: " << nd.id() << "\n");
      work.push(&nd, priority[nd.id().val()]);
    });
  }

  // FIXME: Should only do this if the input set changes...
  // We also propigate partition successors
  std::for_each(std::begin(part_succs_), std::end(part_succs_),
      [this, &dug, &work, &priority]
      (std::pair<DUG::PartID, DUG::DUGid> &part_pr) {
    auto part_id = part_pr.first;
    auto dug_id = part_pr.second;

    auto &nd = dug.getNode(dug_id);
    /*
    dout("    succ is: " << ValPrint(pr.second) << "\n");
    dout("    part_to_obj contains: " << "\n");
    std::for_each(std::begin(part_to_obj), std::end(part_to_obj),
      [](std::pair<DUG::DUGid, DUG::ObjID> &pr) {
      dout("      " << ValPrint(pr.second) << "\n");
    });
    */
    bool ch = nd.in().orPart(in_, dug.objToPartMap(), part_id);

    if (ch) {
      work.push(&nd, priority[nd.id().val()]);
    }
  });
}
//}}}

// Anders Solve {{{
bool SpecAnders::solve() {
  // We're initially given a graph of nodes, with constraints representing the
  //   information flow relations within the nodes.
  // Create a worklist
  // Also, create the priority list for the worklist
  std::vector<uint32_t> priority;
  Worklist<AndersNode> work;

  logout("SOLVE\n");

  // Populate the worklist with all nodes
  for (auto &node : graph_) {
    work.push(&node, 0);
  }

  priority.assign(graph_.size(), 0);

  int32_t vtime = 1;
  uint32_t prio;
  // While the worklist has work
  while (auto pnd = work.pop(prio)) {
    // Don't process the node if we've processed it this round
     /*
    llvm::dbgs() << "pnd->id() is: " << pnd->id() << "\n";
    llvm::dbgs() << "priority is: " << priority[pnd->id().val()] << "\n";
    */
    if (prio < priority[pnd->id().val()]) {
      continue;
    }

    // Pop the next node from the worklist
    priority[pnd->id().val()] = vtime;
    vtime++;

    // llvm::dbgs() << "Processing node: " << pnd->id() << "\n";
    // For each constraint in this node
    for (auto &pcons : pnd->constraints()) {
      // Process the constraint
      pcons->process(graph_, work, priority);
    }

    // Also, now that they've updated their info, lets update pointsto sets

    // Cleanup succs?
    // pnd->succs().unique();

    for (auto succ_id : pnd->succs()) {
      auto &succ_node = graph_.getNode(succ_id);

      /*
      llvm::dbgs() << "Unioning succ: " << succ_node.id() << " and " <<
        pnd->id() << "\n";
        */
      bool ch = (succ_node.ptsto() |= pnd->ptsto());

      if (ch) {
        work.push(&succ_node, priority[succ_node.id().val()]);
      }
    }
  }

  return false;
}

void AndersStoreCons::process(AndersGraph &graph, Worklist<AndersNode> &wl,
    const std::vector<uint32_t> &priority) const {
  // This is a store:
  // *n < b
  // For each points-to in dest
  bool ch = false;
  auto &dest_node = graph.getNode(dest());
  auto &dest_pts = dest_node.ptsto();
  auto &src_node = graph.getNode(src());
  for (auto pts_id : dest_pts) {
    ch |= src_node.succs().insert(pts_id);
  }

  if (ch) {
    wl.push(&src_node, priority[src().val()]);
  }
}

void AndersLoadCons::process(AndersGraph &graph, Worklist<AndersNode> &wl,
    const std::vector<uint32_t> &priority) const {
  // This is a store:
  // a < *n
  // For each points-to in src
  auto &src_node = graph.getNode(src());
  auto &src_pts = src_node.ptsto();
  for (auto pts_id : src_pts) {
    auto &pt_node = graph.getNode(pts_id);
    bool ch = pt_node.succs().insert(dest());

    if (ch) {
      wl.push(&pt_node, priority[pts_id.val()]);
    }
  }
}

/*
void AndersAllocCons::process(AndersGraph &graph, Worklist &wl,
    const std::vector<uint32_t> &priority) const {
  // Allocation:
  //   Update the ptsto of dest with src
  auto &dest_node = graph.getNode(dest());

  bool ch = dest_node.ptsto().set(src());

  if (ch) {
    wl.push(&dest_node, priority[dest().val()]);
  }
}
*/

/*
void AndersCopyCons::process(AndersGraph &graph, Worklist &wl,
    const std::vector<uint32_t> &priority) const {
  auto &dest_node = graph.getNode(dest());
  auto &src_node = graph.getNode(src());

  bool ch = dest_node.ptsto() |= src_node.ptsto();

  if (ch) {
    wl.push(&dest_node, priority[dest().val()]);
  }
}
*/

// Handles constraints related to indirect functions
void AndersIndirCallCons::process(AndersGraph &graph, Worklist<AndersNode> &wl,
    const std::vector<uint32_t> &priority) const {
  // We keep track of the arg nodes for this callsite
  auto &args = args_;

  // We keep track of the ret for this callsite
  auto ret_id = ret();

  auto &callee_node = graph.getNode(callee());

  // For each function in the points-to set of the callee pointer:
  for (auto obj_id : callee_node.ptsto()) {
    // Okay, we have a function here...
    // Get the args for this function (from aux info in the graph)
    auto &fcn_info = graph.getFcnInfo(obj_id);
    auto &dest_args = fcn_info.second;
    auto dest_ret = fcn_info.first;

    // Create an edge from our args to their args
    // ... and push that node to our worklist
    int idx = 0;
    for (auto src_arg_id : args) {
      auto dest_arg_id = dest_args[idx];

      // okay, got the dest args... add edges
      // llvm::dbgs() << "  src_arg_id: " << src_arg_id << "\n";
      auto &src_arg_node = graph.getNode(src_arg_id);
      bool ch = src_arg_node.succs().insert(dest_arg_id);

      // Also add all of those nodes to our worklist
      if (ch) {
        wl.push(&src_arg_node, priority[src_arg_id.val()]);
      }

      idx++;
    }

    // Get the rets for these functions (from the graph)
    if (ret_id != ObjectMap::ObjID::invalid()) {
      // Create an edge from their ret to our ret (if we have a ret)
      // ... and push that node to our worklist
      auto &ret_node = graph.getNode(dest_ret);
      bool ch = ret_node.succs().insert(ret_id);
      if (ch) {
        wl.push(&ret_node, priority[dest_ret.val()]);
      }
    }
  }
}


// FIXME: From solve helpers..
void AndersNode::EdgeSet::unique(AndersGraph &graph) {
  // Convert all ids to rep ids:
  std::vector<ObjID> new_edges;
  for (auto id : edges_) {
    id = graph.getRep(id);

    // Ignore invalid/deleted nodes
    if (id == ObjID::invalid()) {
      continue;
    }

    new_edges.push_back(id);
  }

  edges_ = std::move(new_edges);
  std::sort(std::begin(edges_), std::end(edges_));
  auto it = std::unique(std::begin(edges_), std::end(edges_));
  edges_.erase(it, std::end(edges_));
}


//}}}

