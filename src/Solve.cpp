/*
 * Copyright (C) 2015 David Devecsery
 */

#include <utility>
#include <vector>

#include "include/SpecSFS.h"
#include "include/DUG.h"
#include "include/SolveHelpers.h"

bool SpecSFS::solve(DUG &dug) {
  Worklist work;
  // Add allocs to worklist -- The ptstoset for the alloc will be updated on
  //   solve evaluation
  std::vector<DUG::DUGid> dests;

  std::for_each(dug.nodes_begin(), dug.nodes_end(),
      [this, &work, &dests]
      (DUG::node_iter_type &pnd) {
    auto pnode = pnd.get();
    DUGNode &node = llvm::cast<DUGNode>(*pnode);

    if (llvm::isa<DUG::AllocNode>(pnode)) {
      llvm::dbgs() << "Adding node: " << node.id() << " to worklist\n";
      work.push(&node);
    }

    dests.push_back(node.dest());
  });

  PtstoGraph pts_top(dests);

  // Solve the graph
  while (auto pnd = work.pop()) {
    llvm::dbgs() << "Processing node: " << pnd->id() << "\n";
    pnd->process(dug, pts_top, work);
  }

  // Data is held in pts_top
  // Move our local set of data into the class's
  pts_top_ = std::move(pts_top);

  // All Done!
  return false;
}

void DUG::AllocNode::process(DUG &dug, PtstoGraph &pts_top, Worklist &work) {
  // Update the top level variables for this alloc
  bool change = pts_top.at(DUGNode::dest()).set(DUGNode::src());
  // Add all top level variables updated to worklist
  if (change) {
    std::for_each(succ_begin(), succ_end(),
        [&dug, &work](DUG::ObjID id) {
      work.push(&dug.getNode(id));
    });
  }
}

void DUG::CopyNode::process(DUG &dug, PtstoGraph &pts_top, Worklist &work) {
  // Update the top level variables for this copy
  bool change = (pts_top.at(dest()) |= pts_top.at(src()));
  // Add all updated successors to worklist
  if (change) {
    std::for_each(succ_begin(), succ_end(),
        [&dug, &work](DUG::ObjID id) {
      work.push(&dug.getNode(id));
    });
  }
}

void DUG::LoadNode::process(DUG &dug, PtstoGraph &pts_top, Worklist &work) {
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
  PtstoSet src_pts = pts_top.at(src());
  PtstoSet &dest_pts = pts_top.at(dest());
  bool changed = false;
  std::for_each(std::begin(src_pts), std::end(src_pts),
      [this, &dug, &work, &changed, &dest_pts](DUG::ObjID id) {
    PtstoSet &pts = in_.at(id);

    changed |= (dest_pts |= pts);
  });

  // Also propigate address taken info?
  // Okay... if our in-set has changed since last time we were visited (I assume
  //    it has...)
  // We need to update the ptsto of all of our part_successors
  // FIXME: Only do this for changed info?
  std::for_each(std::begin(part_succs_), std::end(part_succs_),
      [this, &dug, &work] (DUG::PartID part_id) {
    auto &part_to_obj = dug.getObjs(part_id);

    std::for_each(std::begin(part_to_obj), std::end(part_to_obj),
        [this, &dug, &work] (DUG::ObjID obj_id) {
      auto &nd = dug.getNode(obj_id);
      bool ch = (nd.in() |= in_);

      if (ch) {
        work.push(&nd);
      }
    });
  });

  if (changed) {
    std::for_each(succ_begin(), succ_end(),
        [&dug, &work](DUG::ObjID id) {
      work.push(&dug.getNode(id));
    });
  }
}

void DUG::StoreNode::process(DUG &dug, PtstoGraph &pts_top, Worklist &work) {
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
  PtstoSet src_pts = pts_top.at(src());
  PtstoSet dest_pts = pts_top.at(dest());
  bool change = false;

  PtstoGraph in_tmp(in_);

  // If this is a strong update, remove all outgoing edges from src
  if (strong() && src_pts.size() == 1) {
    // Clear all outgoing edges from pts_top(src) from out
    in_tmp.clear(src());
  }

  // Add edges to out with in
  change |= (out_ |= in_);

  std::for_each(std::begin(dest_pts), std::end(dest_pts),
      [this, &change, &dest_pts] (DUG::ObjID id) {
    // Get the pts set in our for this id:
    PtstoSet &out_src = out_.at(id);

    change |= (out_src |= dest_pts);
  });

  // If something changed, update all successors
  if (change) {
    // FIXME: Only do this for changed info?
    std::for_each(std::begin(part_succs_), std::end(part_succs_),
        [this, &work, &dug] (DUG::PartID part_id) {
      auto &part_to_obj = dug.getObjs(part_id);

      std::for_each(std::begin(part_to_obj), std::end(part_to_obj),
          [this, &dug, &work] (DUG::ObjID obj_id) {
        auto &nd = dug.getNode(obj_id);

        std::for_each(std::begin(out_), std::end(out_),
            [this, &dug, &work, &nd]
            (std::pair<const DUG::ObjID, PtstoSet> &pr) {
          bool c = (nd.in().at(pr.first) |= pr.second);

          if (c) {
            // Propigate info?
            work.push(&nd);
          }
        });
      });
    });
  }
}

void DUG::PhiNode::process(DUG &dug, PtstoGraph &, Worklist &work) {
  // For all successors:
  //   succ.IN |= IN
  // if succ.IN.changed():
  //   worklist.add(succ.IN)
  std::for_each(succ_begin(), succ_end(),
      [this, &work, &dug](DUG::ObjID id) {
    bool change = false;

    auto &nd = dug.getNode(id);

    change = (nd.in() |= in());
    if (change) {
      work.push(&nd);
    }
  });
}

