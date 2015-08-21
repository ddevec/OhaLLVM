/*
 * Copyright (C) 2015 David Devecsery
 */

#include <algorithm>
#include <utility>
#include <vector>

#include "include/SpecSFS.h"
#include "include/DUG.h"
#include "include/SolveHelpers.h"

bool SpecSFS::solve(DUG &dug, ObjectMap &) {
  Worklist work;
  // Add allocs to worklist -- The ptstoset for the alloc will be updated on
  //   solve evaluation
  std::vector<ObjectMap::ObjID> dests;

  std::for_each(dug.nodes_begin(), dug.nodes_end(),
      [this, &work, &dests]
      (DUG::node_iter_type &pnd) {
    auto pnode = pnd.get();
    DUGNode &node = llvm::cast<DUGNode>(*pnode);

    if (llvm::isa<DUG::AllocNode>(pnode)) {
      work.push(&node);
    }

    dests.push_back(node.dest());
    dests.push_back(node.src());
  });

  std::sort(std::begin(dests), std::end(dests));
  auto dest_it = std::unique(std::begin(dests), std::end(dests));
  dests.erase(dest_it, std::end(dests));

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
  llvm::dbgs() << "Process alloc start\n";
  // Update the top level variables for this alloc
  auto &top = pts_top.at(dest());
  bool change = top.set(src());
  llvm::dbgs() << "  pts_top[" << dest() << "] is now: ";
  std::for_each(std::begin(top), std::end(top),
      [this](DUG::ObjID obj_id) {
    llvm::dbgs() << " " << obj_id;
  });
  llvm::dbgs() << "\n";

  // Add all top level variables updated to worklist
  if (change) {
    std::for_each(succ_begin(), succ_end(),
        [&dug, &work](DUG::EdgeID id) {
      auto &edge = dug.getEdge(id);
      work.push(&dug.getNode(edge.dest()));
    });
  }
}

void DUG::CopyNode::process(DUG &dug, PtstoGraph &pts_top, Worklist &work) {
  llvm::dbgs() << "Process copy start\n";
  // Update the top level variables for this copy
  PtstoSet &top = pts_top.at(dest());
  bool change = (top |= pts_top.at(src()));

  llvm::dbgs() << "  pts_top[" << dest() << "] is now: ";
  std::for_each(std::begin(top), std::end(top),
      [this](DUG::ObjID obj_id) {
    llvm::dbgs() << " " << obj_id;
  });
  llvm::dbgs() << "\n";

  // Add all updated successors to worklist
  if (change) {
    std::for_each(succ_begin(), succ_end(),
        [&dug, &work](DUG::EdgeID id) {
      auto &edge = dug.getEdge(id);
      work.push(&dug.getNode(edge.dest()));
    });
  }
}

void DUG::LoadNode::process(DUG &dug, PtstoGraph &pts_top, Worklist &work) {
  llvm::dbgs() << "Process load start\n";
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
  PtstoSet &dest_pts = pts_top.at(dest());
  bool changed = false;
  std::for_each(std::begin(src_pts), std::end(src_pts),
      [this, &dug, &work, &changed, &dest_pts](DUG::ObjID id) {
    PtstoSet &pts = in_.at(id);

    changed |= (dest_pts |= pts);
  });

  llvm::dbgs() << "  pts_top[" << dest() << "] is now: ";
  std::for_each(std::begin(dest_pts), std::end(dest_pts),
      [this](DUG::ObjID obj_id) {
    llvm::dbgs() << " " << obj_id;
  });
  llvm::dbgs() << "\n";

  // Also propigate address taken info?
  // Okay... if our in-set has changed since last time we were visited (I assume
  //    it has...)
  // We need to update the ptsto of all of our part_successors
  // FIXME: Only do this for changed info?
  std::for_each(std::begin(part_succs_), std::end(part_succs_),
      [this, &dug, &work] (DUG::PartID part_id) {
    auto &part_to_obj = dug.getObjs(part_id);

    std::for_each(std::begin(part_to_obj), std::end(part_to_obj),
        [this, &dug, &work] (std::pair<DUG::DUGid, ObjectMap::ObjID> &pr) {
      auto &nd = dug.getNode(pr.first);
      bool ch = (nd.in() |= in_);

      if (ch) {
        work.push(&nd);
      }
    });
  });

  if (changed) {
    std::for_each(succ_begin(), succ_end(),
        [&dug, &work](DUG::EdgeID id) {
      auto &edge = dug.getEdge(id);
      work.push(&dug.getNode(edge.dest()));
    });
  }
}

void DUG::StoreNode::process(DUG &dug, PtstoGraph &pts_top, Worklist &work) {
  llvm::dbgs() << "Process store start\n";
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
  PtstoSet &src_pts = pts_top.at(src());
  PtstoSet &dest_pts = pts_top.at(dest());
  bool change = false;

  PtstoGraph in_tmp(in_);

  // If this is a strong update, remove all outgoing edges from src
  if (strong() && src_pts.size() == 1) {
    // Clear all outgoing edges from pts_top(src) from out
    in_tmp.clear(src());
  }

  // Add edges to out with in
  change |= (out_ |= in_);

  /*
  llvm::dbgs() << "About to update out_.  out_ contains ids: ";
  std::for_each(out_.cbegin(), out_.cend(),
      [](const std::pair<const ObjID, PtstoSet> &pr) {
    llvm::dbgs() << " " << pr.first;
  });
  llvm::dbgs() << "\n";
  */

  std::for_each(std::begin(out_), std::end(out_),
      [this, &change, &dest_pts]
      (std::pair<const ObjID, PtstoSet> &pr) {
    change |= (pr.second |= dest_pts);
  });

  /*
  std::for_each(std::begin(dest_pts), std::end(dest_pts),
      [this, &change, &dest_pts] (DUG::ObjID id) {
    // Get the pts set in out for this id:
    llvm::dbgs() << "Scannign dest_pts id of: " << id << "\n";
    PtstoSet &out_src = out_.at(id);

    change |= (out_src |= dest_pts);
  });
  */

  // If something changed, update all successors
  if (change) {
    extern ObjectMap &g_omap;
    llvm::dbgs() << "  Have change on node with src: " <<
      *g_omap.valueAtID(src()) << ", dest: " <<
      *g_omap.valueAtID(dest()) << "\n";
    // FIXME: Only do this for changed info?
    std::for_each(std::begin(part_succs_), std::end(part_succs_),
        [this, &work, &dug] (DUG::PartID part_id) {
      llvm::dbgs() << "  Checking part_id: " << part_id << "\n";
      auto &part_to_obj = dug.getObjs(part_id);

      std::for_each(std::begin(part_to_obj), std::end(part_to_obj),
          [this, &dug, &work] (std::pair<DUG::DUGid, ObjectMap::ObjID> &pr) {
        llvm::dbgs() << "  Checking node: " << pr.first << "\n";
        auto &nd = dug.getNode(pr.first);

        std::for_each(std::begin(out_), std::end(out_),
            [this, &dug, &work, &nd]
            (std::pair<const DUG::ObjID, PtstoSet> &pr) {
          llvm::dbgs() << "    Updating in for: " << pr.first << "\n";

          llvm::dbgs() << "    in is currently: " << nd.in().at(pr.first) <<
              "\n";
          llvm::dbgs() << "    out is: " << pr.second << "\n";
          bool c = (nd.in().at(pr.first) |= pr.second);

          if (c) {
            llvm::dbgs() << "    Pushing nd to work: " << nd.id() << "\n";
            // Propigate info?
            work.push(&nd);
          }
        });
      });
    });
  }
}

void DUG::PhiNode::process(DUG &dug, PtstoGraph &, Worklist &work) {
  llvm::dbgs() << "Process PHI start\n";
  // For all successors:
  //   succ.IN |= IN
  // if succ.IN.changed():
  //   worklist.add(succ.IN)
  std::for_each(std::begin(part_succs_), std::end(part_succs_),
      [this, &work, &dug](DUG::PartID part_id) {
    auto &part_to_obj = dug.getObjs(part_id);

    std::for_each(std::begin(part_to_obj), std::end(part_to_obj),
        [this, &work, &dug] (std::pair<DUG::DUGid, ObjectMap::ObjID> &pr) {
      bool change = false;
      // auto dug_id = dug.getEdge(edge_id).dest();
      auto dug_id = pr.first;

      auto &nd = dug.getNode(dug_id);

      change = (nd.in() |= in());
      if (change) {
        work.push(&nd);
      }
    });
  });
}

