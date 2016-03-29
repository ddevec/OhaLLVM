/*
 * Copyright (C) 2015 David Devecsery
 */

// #define SPECSFS_DEBUG
// #define SPECANDERS_DEBUG
// #define SPECSFS_LOGDEBUG

#ifdef SPECANDERS_DEBUG
#  define adout(...) dout(__VA_ARGS__)
#else
#  define adout(...)
#endif

#include <algorithm>
#include <limits>
#include <map>
#include <set>
#include <stack>
#include <utility>
#include <vector>

#include "include/AndersHelpers.h"
#include "include/ConstraintGraph.h"
#include "include/DUG.h"
#include "include/Debug.h"
#include "include/SolveHelpers.h"
#include "include/SpecAnders.h"
#include "include/SpecSFS.h"

static llvm::cl::opt<int32_t> //  NOLINT
  solve_debug_id("anders-solve-id", llvm::cl::init(-1),
      llvm::cl::value_desc("int"),
      llvm::cl::desc("Specifies IDs to trace in the anders-solve process"));

extern llvm::cl::opt<bool> //  NOLINT
  anders_no_opt;

// Number of edges/number of processed nodes before we allow LCD to run
#define LCD_SIZE 600
#define LCD_PERIOD std::numeric_limits<int32_t>::max()

static size_t lcd_merge_count = 0;

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
  bool change = dest_pts.orOffs(src_pts, offset());

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

  dout("src is " << src() << " " << src_pts << "\n");
  dout("dest is " << dest() << " " << dest_pts << "\n");

  if (dest().val() == 201515) {
    llvm::dbgs() << "SHARED_LOAD\n";
    llvm::dbgs() << "value at src() (" << src() << ")\n";
    llvm::dbgs() << "value at dest() (" << dest() << ")\n";
    llvm::dbgs() << "SHARED\n";
    llvm::dbgs() << "Load is " << rep() << "\n";
    llvm::dbgs() << "src is " << src() << " " << src_pts << "\n";
    llvm::dbgs() << "dest is " << dest() << " " << dest_pts << "\n";
    llvm::dbgs() << "in is " << in << " " << dest_pts << "\n";
  }

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
    for (auto &part_pr : part_succs_) {
      auto part_id = part_pr.first;
      auto dug_id = part_pr.second;

      auto &nd = dug.getNode(dug_id);

      /*
      if (!nd.in().canOrPart(in, dug.objToPartMap(), part_id)) {
        llvm::dbgs() << "orPart failing, node: " << id() << "\n";
        llvm::dbgs() << "  Load SHARED\n";
        llvm::dbgs() << "  value at src() (" << src() << ")\n";
        llvm::dbgs() << "  value at dest() (" << dest() << ")\n";
        llvm::dbgs() << "  src is " << src() << " " << src_pts << "\n";
        llvm::dbgs() << "  dest is " << dest() << " " << dest_pts << "\n";
        llvm::dbgs() << "  nd.in() is: " << nd.in() << "\n";
        llvm::dbgs() << "  in is: " << in << "\n";
        llvm::dbgs() << "  part_id is: " << part_id << "\n";
        llvm::dbgs() << "  nd is: " << nd.id() << "\n";
      }
      */

      bool ch = nd.in().orPart(in, dug.objToPartMap(), part_id);

      if (ch) {
        work.push(&nd, priority[nd.id().val()]);
      }
    }
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

  if (dest().val() == 201515) {
    llvm::dbgs() << "LOAD\n";
    llvm::dbgs() << "value at src() (" << src() << ")\n";
    llvm::dbgs() << "value at dest() (" << dest() << ")\n";
    llvm::dbgs() << "Load is " << rep() << "\n";
    llvm::dbgs() << "src is " << src() << " " << src_pts << "\n";
    llvm::dbgs() << "dest is " << dest() << " " << dest_pts << "\n";
    llvm::dbgs() << "in is " << in_ << " " << dest_pts << "\n";
  }

  bool changed = false;
  for (auto id : src_pts) {
    dout("  id is: " << id << "\n");
    dout("  in is: " << in_ << "\n");

    if (!in_.has(id)) {
      llvm::dbgs() << "LOAD src or failing, node: " << DUGNode::id() << "\n";
      llvm::dbgs() << "  LOAD\n";
      llvm::dbgs() << "  value at src() (" << src() << ")\n";
      llvm::dbgs() << "  value at dest() (" << dest() << ")\n";
      llvm::dbgs() << "  value at rep() (" << rep() << ")\n";
      llvm::dbgs() << "  src is " << src() << " " << src_pts << "\n";
      llvm::dbgs() << "  dest is " << dest() << " " << dest_pts << "\n";
      llvm::dbgs() << "  in_ is " << in_ << "\n";
      llvm::dbgs() << "  id is: " << id << "\n";
    }

    PtstoSet &pts = in_.at(id);

    dout("  pts is: " << pts << "\n");

    changed |= (dest_pts |= pts);
  }

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
    for (auto &part_pr : part_succs_) {
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
        /*
        if (!nd.in().canOrPart(in_, dug.objToPartMap(), part_id)) {
          llvm::dbgs() << "orPart failing, node: " << id() << "\n";
          llvm::dbgs() << "  LOAD\n";
          llvm::dbgs() << "  value at src() (" << src() << ")\n";
          llvm::dbgs() << "  value at dest() (" << dest() << ")\n";
          llvm::dbgs() << "  src is " << src() << " " << src_pts << "\n";
          llvm::dbgs() << "  dest is " << dest() << " " << dest_pts << "\n";
          llvm::dbgs() << "  nd.in() is: " << nd.in() << "\n";
          llvm::dbgs() << "  nd is: " << nd.id() << "\n";
        }
        */
        bool ch = nd.in().orPart(in_, dug.objToPartMap(), part_id);

        if (ch) {
          dout("    Pushing nd to work: " << nd.id() << " (with prio: " <<
              priority[nd.id().val()] << ")\n");
          work.push(&nd, priority[nd.id().val()]);
        }
      }
    }

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

  if (dest().val() == 50817) {
    llvm::dbgs() << "STORE\n";
    llvm::dbgs() << "value at src() (" << src() << ")\n";
    llvm::dbgs() << "value at dest() (" << dest() << ")\n";
    llvm::dbgs() << "Load is " << rep() << "\n";
    llvm::dbgs() << "src is " << src() << " " << src_pts << "\n";
    llvm::dbgs() << "dest is " << dest() << " " << dest_pts << "\n";
    llvm::dbgs() << "in is " << in_ << " " << dest_pts << "\n";
    llvm::dbgs() << "out is " << out_ << " " << dest_pts << "\n";
  }

  // If this is a strong update, remove all outgoing edges from dest
  // NOTE: This is a strong update if we are updating a single concrete location
  if (strong() && dest_pts.singleton()) {
    // Clear all outgoing edges from pts_top(src) from out
    dout("DOING STRONG UPDATE!!!\n");
    dout("dest is: " << dest() << "\n");
    dout("in is: " << in() << "\n");

    dout("    Initial out: " << out_ << "\n");
    dout("    Initial in: " << in() << "\n");

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
    for (auto elm : dest_pts) {
      if (!out_.has(elm)) {
        llvm::dbgs() << "orElement failing, node: " << id() << "\n";
        llvm::dbgs() << "  WEAK STORE\n";
        llvm::dbgs() << "  value at src() (" << src() << ")\n";
        llvm::dbgs() << "  value at dest() (" << dest() << ")\n";
        llvm::dbgs() << "  src is " << src() << " " << src_pts << "\n";
        llvm::dbgs() << "  dest is " << dest() << " " << dest_pts << "\n";
        llvm::dbgs() << "  out_ is: " << out_ << "\n";
        llvm::dbgs() << "  elm is: " << elm << "\n";
      }
      change |= out_.orElement(elm, src_pts);
    }
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
    for (auto &part_pr : part_succs_) {
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
        //
        /*
        if (!nd.in().canOrPart(out_, dug.objToPartMap(), part_id)) {
          llvm::dbgs() << "orPart failing, node: " << id() << "\n";
          llvm::dbgs() << "  LOAD\n";
          llvm::dbgs() << "  part_id: " << part_id << "\n";
          llvm::dbgs() << "  value at src() (" << src() << ")\n";
          llvm::dbgs() << "  value at dest() (" << dest() << ")\n";
          llvm::dbgs() << "  src is " << src() << " " << src_pts << "\n";
          llvm::dbgs() << "  dest is " << dest() << " " << dest_pts << "\n";
          llvm::dbgs() << "  nd.in() is: " << nd.in() << "\n";
          llvm::dbgs() << "  out_ is: " << out_ << "\n";
          llvm::dbgs() << "  nd is: " << dug_id << "\n";
          llvm::dbgs() << "  nd.id() is: " << nd.id() << "\n";
        }
        */

        bool c = nd.in().orPart(out_, dug.objToPartMap(), part_id);

        // dout("  after in for nd is: " << nd.in() << "\n");

        if (c) {
          dout("    Pushing nd to work: " << nd.id() << " (with prio: " <<
              priority[nd.id().val()] << ")\n");
          // Propigate info?
          work.push(&nd, priority[nd.id().val()]);
        }
      }
    }

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

// SCC Helpers (For anders) {{{
class RunNuutila {
 public:
  static const int32_t IndexInvalid = -1;

  RunNuutila(AndersGraph &g, const std::unordered_set<AndersNode *> &nodes,
      Worklist<AndersNode> &wl, const std::vector<uint32_t> &priority) :
      graph_(g), wl_(wl), priority_(priority) {
    // For each candidate node, visit it if it hasn't been visited, and compute
    //   SCCs, as dicated by Nuutila's Tarjan variant
    nodeData_.resize(graph_.size());
    // llvm::dbgs() << "START NUUTILA\n";
    for (auto pnode : nodes) {
      // llvm::dbgs() << "  ITER NUUTILA: " << nodeStack_.size() <<  "\n";
      auto &node_data = getData(pnode->id());
      if (g.isRep(*pnode) && node_data.root == IndexInvalid) {
        visit2(pnode->id());
      }
    }
    // llvm::dbgs() << "END NUUTILA\n";

    assert(nodeStack_.empty());
  }

 private:
  struct TarjanData {
    int32_t root = IndexInvalid;
  };

  struct TarjanData &getData(AndersGraph::ObjID id) {
    assert(id != AndersGraph::ObjID::invalid());
    assert(id.val() >= 0);
    assert(static_cast<size_t>(id.val()) < nodeData_.size());
    return nodeData_.at(id.val());
  }

  struct TarjanData &getRepData(AndersGraph::ObjID id) {
    return getData(graph_.getRep(id));
  }

  void visit2(AndersGraph::ObjID node_id) {
    assert(merged_.find(node_id) == std::end(merged_));
    assert(graph_.isRep(node_id));
    auto &node_data = getRepData(node_id);

    /*
    llvm::dbgs() << "Visit: " << node_id << ": dfs = " << nextIndex_ << "\n";
    */
    node_data.root = nextIndex_;
    auto dfs_idx = nextIndex_;
    nextIndex_++;

    auto &start_node = graph_.getNode(node_id);
    for (auto succ_val : start_node.copySuccs()) {
      auto succ_id = ObjectMap::ObjID(succ_val);

      auto dest_id = graph_.getRep(succ_id);
      auto dest_data = &getRepData(dest_id);

      // FIXME: Edge cleanup here?

      // Ignore merged successors
      if (merged_.find(dest_id) == std::end(merged_)) {
        /*
        llvm::dbgs() << "      " << node_id << " succ: " << dest_id << "\n";
        */
        if (dest_data->root == IndexInvalid) {
          visit2(graph_.getRep(dest_id));

          // Need to get new node_data, as we have have merged it in the prior
          //   loop
          dest_id = graph_.getRep(dest_id);
          dest_data = &getRepData(dest_id);
        }

        if (dest_data->root < node_data.root) {
          /*
          llvm::dbgs() << "  node < dest: " << node_id
            << " (" << node_data.root << ") <= " << dest_id <<
            " (" << dest_data->root << ")\n";
          */
          node_data.root = dest_data->root;
        }
      }
    }

    // FIXME: Finish edge cleanup here?
    assert(graph_.isRep(node_id));

    /*
    llvm::dbgs() << "    " << node_id << " root: " << node_data.root <<
      ", dfs: " << dfs_idx << "\n";
    */
    if (node_data.root == dfs_idx) {
      bool ch = false;

      while (!nodeStack_.empty()) {
        auto next_id = nodeStack_.top();
        auto &next_data = getData(next_id);
        if (next_data.root < dfs_idx) {
          break;
        }
        // llvm::dbgs() << "  --Stack popping: " << next_id << "\n";
        nodeStack_.pop();

        auto rep_next_id = graph_.getRep(next_id);
        auto &node_rep = graph_.getNode(node_id);

        // If we weren't already merged (HCD can cause this)
        if (rep_next_id != node_rep.id()) {
          lcd_merge_count++;
          auto &nd = graph_.getNode(rep_next_id);
          /*
          if (node_id == ObjectMap::NullValue ||
              nd.id() == ObjectMap::NullValue) {
            llvm::dbgs() << "Nuutilia merge null: " << node_id << " : " <<
              nd.id() << "\n";
          }
          */
          graph_.merge(node_rep, nd);
        }

        ch = true;
      }

      auto node_rep_id = graph_.getRep(node_id);
      // llvm::dbgs() << "  ~~merged_.insert(" << node_id << ")\n";
      merged_.insert(node_rep_id);

      if (ch) {
        auto &node = graph_.getNode(node_rep_id);
        assert(node.id() == node_rep_id);
        wl_.push(&node, priority_[node_rep_id.val()]);
      }
    } else {
      // llvm::dbgs() << "  ++Stack pushing: " << node_id << "\n";
      assert(graph_.isRep(node_id));
      nodeStack_.push(node_id);
    }
  }

  int32_t nextIndex_ = 1;
  std::stack<AndersGraph::ObjID> nodeStack_;
  std::vector<TarjanData> nodeData_;
  std::set<AndersGraph::ObjID> merged_;

  AndersGraph &graph_;
  Worklist<AndersNode> &wl_;
  const std::vector<uint32_t> &priority_;
};
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

  // Populate the worklist with any node with a non-empty ptsto set
  adout("init solve:\n");
  for (auto &node : graph_) {
    if (!node.ptsto().empty()) {
      adout("  " << node.id() << "\n");
      work.push(&node, 0);
    }
  }

  priority.assign(graph_.size(), 0);

  int32_t vtime = 1;
  uint32_t prio;

  size_t hcd_merge_count = 0;
  size_t lcd_check_count = 0;
  size_t hcd_merge_last = 0;
  size_t lcd_merge_last = 0;
  size_t lcd_check_last = 0;

  int32_t lcd_last_time = 1;
  struct lcd_edge_hash {
    size_t operator()(const std::pair<AndersGraph::ObjID, AndersGraph::ObjID>
        &pr) const {
      size_t ret = AndersGraph::ObjID::hasher()(pr.first);
      ret <<= 1;
      ret ^= AndersGraph::ObjID::hasher()(pr.second);
      return ret;
    }
  };
  std::unordered_set<std::pair<AndersGraph::ObjID, AndersGraph::ObjID>,
    lcd_edge_hash> lcd_edges;
  std::unordered_set<AndersNode *> lcd_nodes;
  // While the worklist has work
  // Pop the next node from the worklist

  while (auto pnd = work.pop(prio)) {
    // Don't process the node if we've processed it this round
    if (prio < priority[pnd->id().val()]) {
      continue;
    }

    if (!graph_.isRep(*pnd)) {
      continue;
    }

    if (lcd_merge_last + 1000 <= lcd_merge_count) {
      llvm::dbgs() << "LCD Merge Count: " << lcd_merge_count << "\n";
      lcd_merge_last = lcd_merge_count;
    }

    if (lcd_check_last + 1000 <= lcd_check_count) {
      llvm::dbgs() << "LCD check count: " << lcd_check_count << "\n";
      lcd_check_last = lcd_check_count;
    }

    if (hcd_merge_last + 1000 <= hcd_merge_count) {
      llvm::dbgs() << "HCD Merge Count: " << hcd_merge_count << "\n";
      hcd_merge_last = hcd_merge_count;
    }

    priority[pnd->id().val()] = vtime;
    vtime++;

    // If we're near the point of infinite loop:
    /*
    if (lcd_check_count > 5000) {
      anders_do_debug = true;
    }
    */

    // If this node is part of HCD:
    auto hcd_itr = hcdPairs_.find(pnd->id());
    if (hcd_itr != std::end(hcdPairs_)) {
      // For each ptsto in this node:
      bool did_merge = false;
      for (auto dest_id : pnd->ptsto()) {
        // Collapse (pointed-to-node, rep)
        // Add rep to worklist
        auto &dest_node = graph_.getNode(dest_id);
        auto &rep_node = graph_.getNode(hcd_itr->second);

        // Don't merge w/ self, or with the int value or null value
        if (dest_node.id() != rep_node.id() &&
            dest_node.id() != ObjectMap::IntValue &&
            rep_node.id() != ObjectMap::NullValue &&
            dest_node.id() != ObjectMap::NullValue) {
          graph_.merge(rep_node, dest_node);
          did_merge = true;

          hcd_merge_count++;
        }
      }

      if (did_merge) {
        auto &rep_node = graph_.getNode(hcd_itr->second);
        work.push(&rep_node, priority[rep_node.id().val()]);
      }

      // The merge may have caused us to no longer be a rep, in which case, we
      //   shouldn't analyze this node any further
      if (!graph_.isRep(*pnd)) {
        continue;
      }
    }

    adout("Node: " << pnd->id() << "\n");

    // llvm::dbgs() << "Processing node: " << pnd->id() << "\n";
    // For each constraint in this node
    // Note: getUpdateSet also resets the update set
    auto update_set = pnd->getUpdateSet();
    if (!update_set.empty()) {
      auto &cons_list = pnd->constraints();

      // This is only safe because I guarantee that once a cons goes into the
      // set I will never change its index
      auto cons_eq = [this, &cons_list] (size_t lhs_idx, size_t rhs_idx) {
        auto &plhs = cons_list[lhs_idx];
        auto &prhs = cons_list[rhs_idx];

        auto lhs_src = graph_.getNode(plhs->src()).id();
        auto rhs_src = graph_.getNode(prhs->src()).id();

        auto lhs_dest = plhs->dest();
        if (lhs_dest != AndersCons::ObjID::invalid()) {
          lhs_dest = graph_.getNode(lhs_dest).id();
        }

        auto rhs_dest = prhs->dest();
        if (rhs_dest != AndersCons::ObjID::invalid()) {
          rhs_dest = graph_.getNode(rhs_dest).id();
        }

        auto lhs_offs = plhs->offs();
        auto rhs_offs = prhs->offs();

        return plhs->getKind() == prhs->getKind() && lhs_src == rhs_src &&
          lhs_dest == rhs_dest && lhs_offs == rhs_offs;
      };

      auto cons_hash = [this, &cons_list] (size_t idx) {
        assert(idx < cons_list.size());

        auto &pcons = cons_list[idx];

        assert(pcons->src() != AndersCons::ObjID::invalid());
        auto src = graph_.getNode(pcons->src()).id();

        // Invalid can happen for indirect constraints
        auto dest = pcons->dest();
        if (dest != AndersCons::ObjID::invalid()) {
          dest = graph_.getNode(dest).id();
        }
        // llvm::dbgs() << "  dest: " << dest << "\n";
        auto kind = pcons->getKind();
        auto offs = pcons->offs();

        auto ret = AndersCons::ObjID::hasher()(src);
        ret <<= 1;
        ret ^= AndersCons::ObjID::hasher()(dest);
        ret <<= 1;
        ret ^= std::hash<int32_t>()(offs);
        ret <<= 1;
        ret ^= std::hash<int32_t>()(static_cast<int32_t>(kind));

        return ret;
      };
      std::unordered_set<size_t, decltype(cons_hash), decltype(cons_eq)>
        cons_set(cons_list.size() * 2 , cons_hash, cons_eq);

      for (size_t idx = 0; idx < cons_list.size();) {
        auto &pcons = cons_list[idx];

        // Don't remove indir call constraints
        if (!llvm::isa<AndersIndirCallCons>(pcons.get())) {
          if (cons_set.find(idx) == std::end(cons_set)) {
            cons_set.insert(idx);
          } else {
            cons_list[idx] = std::move(cons_list.back());
            cons_list.pop_back();
            continue;
          }
        }
        ++idx;

        // Process the constraint
        pcons->process(graph_, work, priority, update_set);
      }

      // This is only safe to put inside of the updated() conditional because
      // GEP edges cannot be added by constraints in my current implementation
      auto &edges = pnd->gepSuccs();
      std::set<std::pair<ObjectMap::ObjID, int32_t>> seen_edges;
      // for (auto succ_pr : pnd->succs())
      for (size_t idx = 0; idx < edges.size();) {
        auto &succ_pr = edges[idx];
        auto succ_id = succ_pr.first;
        auto succ_offs = succ_pr.second;

        auto &succ_node = graph_.getNode(succ_id);

        // Dedup the edges
        auto new_pr = std::make_pair(succ_node.id(), succ_offs);
        if (seen_edges.find(new_pr) != std::end(seen_edges)) {
          edges[idx] = edges.back();
          edges.pop_back();
          continue;
        } else {
          seen_edges.insert(new_pr);
        }
        idx++;


        adout("  GEPsucc: " << succ_node.id() << "\n");

        /*
        llvm::dbgs() << "Unioning succ: " << succ_node.id() << " and " <<
          pnd->id() << "\n";
        */
        auto &succ_pts = succ_node.ptsto();

        adout("  f: " << succ_offs << "\n");
        // adout("  i: " << pnd->ptsto() << "\n");
        adout("  u: " << update_set << "\n");
        adout("  o: " << succ_node.id() << ": " << succ_pts << "\n");
        // Don't gep with intvalue:
        auto update_set_clean = pnd->ptsto();

        update_set_clean.reset(ObjectMap::IntValue);
        update_set_clean.reset(ObjectMap::NullValue);

        bool ch = succ_pts.orOffs(update_set_clean, succ_offs);

        adout("  ch: " << ch << "\n");
        adout("  O: " << succ_node.id() << ": " << succ_pts << "\n");



        auto edge = std::make_pair(pnd->id(), succ_node.id());
        // If we haven't run LCD on this edge before, the points-to sets are not
        //   empty, and the two points-to sets are equal
        if (!anders_no_opt) {
          if (lcd_edges.find(edge) == std::end(lcd_edges) &&
              !pnd->ptsto().empty() &&
              pnd->ptsto() == succ_pts) {
            lcd_check_count++;
            lcd_nodes.insert(pnd);
            lcd_edges.insert(edge);
          }
        }

        if (ch) {
          adout("    pnd: " << pnd->id() << ": gep push: " <<
            succ_node.id() << "\n");
          work.push(&succ_node, priority[succ_node.id().val()]);
        }
      }
    }

    auto &copy_edges = pnd->copySuccs();
    Bitmap new_copy_edges;
    for (auto succ_val : copy_edges) {
      auto succ_id = ObjectMap::ObjID(succ_val);
      // Nothing should write to null value ever ever ever
      assert(succ_id != ObjectMap::NullValue);

      auto &succ_node = graph_.getNode(succ_id);

      // If we've already analyzed this node...
      if (new_copy_edges.test(succ_node.id().val())) {
        continue;
      }

      new_copy_edges.set(succ_node.id().val());

      adout("  succ: " << succ_node.id() << "\n");

      /*
      llvm::dbgs() << "Unioning succ: " << succ_node.id() << " and " <<
        pnd->id() << "\n";
      */
      auto &succ_pts = succ_node.ptsto();

      adout("  f: 0\n");
      // adout("  i: " << pnd->ptsto() << "\n");
      adout("  u: " << update_set << "\n");
      adout("  o: " << succ_node.id() << ": " << succ_pts << "\n");

      /*
      if (solve_debug_id > 0 &&
          pnd->ptsto().test(ObjectMap::ObjID(solve_debug_id)) &&
          !succ_pts.test(ObjectMap::ObjID(solve_debug_id))) {
        llvm::dbgs() << "  Node: " << succ_node.id() << " |= " << pnd->id() <<
          " gaining id: " << solve_debug_id << "\n";
      }
      */

      bool ch = succ_pts |= pnd->ptsto();

      adout("  ch: " << ch << "\n");
      adout("  O: " << succ_node.id() << ": " << succ_pts << "\n");

      auto edge = std::make_pair(pnd->id(), succ_node.id());
      // If we haven't run LCD on this edge before, the points-to sets are not
      //   empty, and the two points-to sets are equal
      if (lcd_edges.find(edge) == std::end(lcd_edges) &&
          !update_set.empty() &&
          pnd->ptsto() == succ_pts) {
        lcd_check_count++;
        lcd_nodes.insert(pnd);
        lcd_edges.insert(edge);
      }

      if (ch) {
        adout("    pnd: " << pnd->id() << ": copy push: " <<
          succ_node.id() << "\n");
        work.push(&succ_node, priority[succ_node.id().val()]);
      }
    }
    pnd->setCopySuccs(std::move(new_copy_edges));


    // llvm::dbgs() << "lcd_nodes.size(): " << lcd_nodes.size() << "\n";
    if (lcd_nodes.size() > LCD_SIZE ||
        (vtime - lcd_last_time) > LCD_PERIOD) {
      // llvm::dbgs() << " !! Running lcd\n";
      // Do lcd
      RunNuutila(graph_, lcd_nodes, work, priority);
      // Clear lcd_nodes
      lcd_nodes.clear();
      lcd_last_time = vtime;
    }
  }

  llvm::dbgs() << "Final hcd_merge_count: " << hcd_merge_count << "\n";
  llvm::dbgs() << "Final lcd_check_count: " << lcd_check_count << "\n";
  llvm::dbgs() << "Final lcd_merge_count: " << lcd_merge_count << "\n";

  return false;
}

void AndersStoreCons::process(AndersGraph &graph, Worklist<AndersNode> &wl,
    const std::vector<uint32_t> &priority,
    const PtstoSet &update_dest) const {
  // This is a store:
  // *n < b
  // For each points-to in dest
  bool ch = false;
  // auto &dest_pts = update_dest;
  /*
  auto &dest_node = graph.getNode(dest());
  auto &dest_pts = dest_node.ptsto();
  */

  auto &dest_pts = update_dest;
  auto &src_node = graph.getNode(src());

  // adout("    storecons for: " << dest_node.id() << "\n");

  if (src_node.id() == ObjectMap::IntValue ||
      src_node.id() == ObjectMap::NullValue) {
    return;
  }

  ch = src_node.addCopyEdges(dest_pts);
  /*
  for (auto dest_id : dest_pts) {
    auto &pt_node = graph.getNode(dest_id);
    adout("      pts_node: " << pt_node.id() << "\n");
    if (pt_node.id() != src_node.id() &&
        pt_node.id() != ObjectMap::IntValue &&
        pt_node.id() != ObjectMap::NullValue) {
      ch |= src_node.addCopyEdge(pt_node.id());
      adout("      " << src_node.id() << " <- edge - " <<
         pt_node.id() << "\n");
    }
  }
  */

  if (ch) {
    adout("  StoreCons: added: " << src_node.id() << " to WL\n");
    wl.push(&src_node, priority[src_node.id().val()]);
  }
}

void AndersLoadCons::process(AndersGraph &graph, Worklist<AndersNode> &wl,
    const std::vector<uint32_t> &priority,
    const PtstoSet &update_src) const {
  // This is a store:
  // a < *n
  // For each points-to in src
  // auto &src_pts = update_src;
  // auto &src_pts = graph.getNode(src()).ptsto();
  auto &src_pts = update_src;
  auto &dest_node = graph.getNode(dest());
  assert(dest_node.id() != ObjectMap::IntValue);
  assert(dest_node.id() != ObjectMap::NullValue);

  for (auto pts_id : src_pts) {
    auto &pt_node = graph.getNode(pts_id);
    // Don't add ptr to yourself, or null
    if (pt_node.id() != dest_node.id() &&
        pt_node.id() != ObjectMap::IntValue &&
        pt_node.id() != ObjectMap::NullValue) {
      bool ch = pt_node.addCopyEdge(dest_node.id());

      if (ch) {
        adout("  LoadCons: added: " << pt_node.id() << " to WL\n");
        wl.push(&pt_node, priority[pt_node.id().val()]);
      }
    }
  }
}

// Handles constraints related to indirect functions
void AndersIndirCallCons::process(AndersGraph &graph, Worklist<AndersNode> &wl,
    const std::vector<uint32_t> &priority,
    const PtstoSet &callee_update) const {
  // We keep track of the arg nodes for this callsite
  auto &args = args_;

  // We keep track of the ret for this callsite
  auto ret_id = ret();

  // auto &callee_node = graph.getNode(callee());
  /*
  llvm::dbgs() << "Update indir call to: " << callee() << ": " <<
    callee_node.ptsto() << "\n";
  */

  auto &callee_pts = callee_update;
  // auto &callee_pts = callee_node.ptsto();

  // For each function in the points-to set of the callee pointer:
  for (auto obj_id : callee_pts) {
    adout("  obj_id: " << obj_id << "\n");
    // Okay, we have a function here...
    // Get the args for this function (from aux info in the graph)
    // auto &fcn_info = graph.getFcnInfo(obj_id);
    auto fcn_itr = graph.tryGetFcnInfo(obj_id);
    if (fcn_itr != graph.fcns_end()) {
      auto &fcn_info = fcn_itr->second;
      auto &dest_args = fcn_info.second;
      auto dest_ret = fcn_info.first;

      // Create an edge from our args to their args
      // ... and push that node to our worklist
      size_t idx = 0;
      for (auto src_arg_id : args) {
        if (idx < dest_args.size()) {
          auto dest_arg_id = dest_args[idx];

          // okay, got the dest args... add edges
          adout("  src_arg_id: " << src_arg_id << "\n");
          adout("  dest_arg_id: " << dest_arg_id << "\n");

          auto &src_arg_node = graph.getNode(src_arg_id);
          auto &dest_arg_node = graph.getNode(dest_arg_id);

          bool ch;
          if (src_arg_node.id() == ObjectMap::NullValue) {
            ch = dest_arg_node.ptsto().set(ObjectMap::NullValue);
          } else if (src_arg_node.id() == ObjectMap::IntValue) {
            ch = dest_arg_node.ptsto().set(ObjectMap::IntValue);
          } else {
            ch = src_arg_node.addCopyEdge(dest_arg_node.id());
          }

          // Also add all of those nodes to our worklist
          if (ch) {
            wl.push(&src_arg_node, priority[src_arg_node.id().val()]);
          }
        } else {
          break;
        }

        idx++;
      }

      // Get the rets for these functions (from the graph)
      if (ret_id != ObjectMap::ObjID::invalid()) {
        // Create an edge from their ret to our ret (if we have a ret)
        // ... and push that node to our worklist
        auto &ret_id_node = graph.getNode(ret_id);
        auto &ret_node = graph.getNode(dest_ret);
        assert(ret_id != ObjectMap::NullValue);
        // Don't add edges to int or null..
        bool ch = ret_node.addCopyEdge(ret_id_node.id());

        if (ch) {
          wl.push(&ret_node, priority[ret_node.id().val()]);
        }
      }
    } else {
      adout("Couldn't find fcn for: " << obj_id << "\n");
      // llvm::dbgs() << "Couldn't find fcn for: " << obj_id << "\n";
    }
  }
}

//}}}

