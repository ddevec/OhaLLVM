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
  PtstoSet &dest_pts = pts_top.at(dest());

  bool change = dest_pts.set(src());

  llvm::dbgs() << "  pts_top[" << dest() << "] is now: " << dest_pts << "\n";

  // Add all top level variables updated to worklist
  if (change) {
    std::for_each(succ_begin(), succ_end(),
        [&dug, &work](DUG::EdgeID id) {
      auto &edge = dug.getEdge(id);
      auto &nd = dug.getNode(edge.dest());
      llvm::dbgs() << "  Pushing nd to work: " << nd.id() << "\n";
      work.push(&nd);
    });
  }
}

void DUG::CopyNode::process(DUG &dug, PtstoGraph &pts_top, Worklist &work) {
  llvm::dbgs() << "Process copy start\n";
  // Update the top level variables for this copy
  PtstoSet &dest_pts = pts_top.at(dest());
  PtstoSet &src_pts = pts_top.at(src());
  bool change = (dest_pts |= src_pts);

  llvm::dbgs() << "  pts_top[" << dest() << "] is now: " << dest_pts << "\n";

  // Add all updated successors to worklist
  if (change) {
    std::for_each(succ_begin(), succ_end(),
        [&dug, &work](DUG::EdgeID id) {
      auto &edge = dug.getEdge(id);
      auto &nd = dug.getNode(edge.dest());
      llvm::dbgs() << "  Pushing nd to work: " << nd.id() << "\n";
      work.push(&nd);
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
  llvm::dbgs() << "value at src() (" << src() << ") is: " <<
    ValPrint(src()) << "\n";
  llvm::dbgs() << "value at dest() (" << dest() << ") is: " <<
    ValPrint(dest()) << "\n";
  PtstoSet &dest_pts = pts_top.at(dest());
  llvm::dbgs() << "Load is " << rep() << ": " <<
    ValPrint(rep()) << "\n";

  bool changed = false;
  std::for_each(std::begin(src_pts), std::end(src_pts),
      [this, &dug, &work, &changed, &dest_pts](DUG::ObjID id) {
    llvm::dbgs() << "  id is: " << id << ": " << ValPrint(id) << "\n";
    llvm::dbgs() << "  in is: " << in_ << "\n";

    PtstoSet &pts = in_.at(id);

    llvm::dbgs() << "  pts is: " << pts << "\n";

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
  llvm::dbgs() << "  Load dest is: " << ValPrint(dest()) << "\n";
  llvm::dbgs() << "  Load src is: " << ValPrint(src()) << "\n";
  std::for_each(std::begin(part_succs_), std::end(part_succs_),
      [this, &dug, &work]
      (std::pair<DUG::PartID, DUG::DUGid> &part_pr) {
    auto part_id = part_pr.first;
    auto dug_id = part_pr.second;

    auto &nd = dug.getNode(dug_id);
    /*
    llvm::dbgs() << "    succ is: " << ValPrint(pr.second) << "\n";
    llvm::dbgs() << "    part_to_obj contains: " << "\n";
    std::for_each(std::begin(part_to_obj), std::end(part_to_obj),
      [](std::pair<DUG::DUGid, DUG::ObjID> &pr) {
      llvm::dbgs() << "      " << ValPrint(pr.second) << "\n";
    });
    */
    bool ch = nd.in().orPart(in_, dug.objToPartMap(), part_id);

    if (ch) {
      work.push(&nd);
    }
  });

  if (changed) {
    std::for_each(succ_begin(), succ_end(),
        [&dug, &work](DUG::EdgeID id) {
      auto &edge = dug.getEdge(id);
      auto &nd = dug.getNode(edge.dest());
      llvm::dbgs() << "  Pushing nd to work: " << nd.id() << "\n";
      work.push(&nd);
    });
  }
}

void DUG::StoreNode::process(DUG &dug, PtstoGraph &pts_top, Worklist &work) {
  llvm::dbgs() << "Process store start\n";
  llvm::dbgs() << "Store is: " << rep() << ": " << ValPrint(rep()) << "\n";
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
  llvm::dbgs() << "  Source is: " << src() << " : " << ValPrint(src()) << "\n";
  llvm::dbgs() << "  Dest is: " << dest() << " : " << ValPrint(dest()) << "\n";
  PtstoSet &src_pts = pts_top.at(src());
  PtstoSet &dest_pts = pts_top.at(dest());
  bool change = false;

  llvm::dbgs() << "  Initial src_pts: " << src_pts << "\n";
  llvm::dbgs() << "  Initial dest_pts: " << dest_pts << "\n";

  // If this is a strong update, remove all outgoing edges from dest
  // NOTE: This is a strong update if we are updating a single concrete location
  if (strong() && dest_pts.size() == 1) {
    // Clear all outgoing edges from pts_top(src) from out
    llvm::dbgs() << "DOING STRONG UPDATE!!!\n";
    llvm::dbgs() << "dest is: " << dest() << "\n";
    llvm::dbgs() << "in is: " << in() << "\n";

    change |= out_.orExcept(in(), *std::begin(dest_pts));

    // Add edges to out with in
    change |= out_.assign(*std::begin(dest_pts), src_pts);
  } else {
    llvm::dbgs() << "  Weak store:\n";
    llvm::dbgs() << "    Initial out: " << out_ << "\n";
    llvm::dbgs() << "    Initial in: " << in() << "\n";
    // Combine out with in
    change |= (out_ |= in());

    // Also, add the stored element(s):
    std::for_each(std::begin(dest_pts), std::end(dest_pts),
        [this, &change, &src_pts] (ObjectMap::ObjID elm) {
      change |= out_.orElement(elm, src_pts);
    });

    llvm::dbgs() << "    Final out: " << out_ << "\n";
    llvm::dbgs() << "    Final in: " << in() << "\n";
  }

  // If something changed, update all successors
  if (change) {
    llvm::dbgs() << "  Have change on node with src: " <<
      ValPrint(src()) << ", dest: " <<
      ValPrint(dest()) << "\n";
    // FIXME: Only do this for changed info?
    // For each successor partition of this store
    std::for_each(std::begin(part_succs_), std::end(part_succs_),
        [this, &work, &dug]
        (std::pair<DUG::PartID, DUG::DUGid> &part_pr) {
      auto part_id = part_pr.first;
      auto dug_id = part_pr.second;
      auto &nd = dug.getNode(dug_id);

      llvm::dbgs() << "  Checking node: " << dug_id << " or: " <<
          ValPrint(nd.extId()) << "\n";


      llvm::dbgs() << "  before in for nd is: " << nd.in() << "\n";

      // Update the input set of the successor node
      bool c = nd.in().orPart(out_, dug.objToPartMap(), part_id);

      llvm::dbgs() << "  after in for nd is: " << nd.in() << "\n";

      if (c) {
        llvm::dbgs() << "    Pushing nd to work: " << nd.id() << "\n";
        // Propigate info?
        work.push(&nd);
      }
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
      [this, &work, &dug]
      (std::pair<DUG::PartID, DUG::DUGid> &part_pr) {
    auto dug_id = part_pr.second;
    bool change = false;

    auto &nd = dug.getNode(dug_id);

    // FIXME?? Does this need to be a part_or?
    change = (nd.in() |= in());
    if (change) {
      llvm::dbgs() << "  Pushing nd to work: " << nd.id() << "\n";
      work.push(&nd);
    }
  });
}

void DUG::GlobalInitNode::process(DUG &dug, PtstoGraph &pts_top,
    Worklist &work) {
  llvm::dbgs() << "Process GlobalInit\n";

  // bool change = false;

  llvm::dbgs() << "Adding " << src() << ", or " <<
      ValPrint(src()) << " to top " << dest() << ", or " <<
      ValPrint(dest()) << "\n";
  llvm::dbgs() << "Thats a node for: " << ValPrint(rep()) <<
      "\n";

  auto &dest_pts = pts_top.at(dest());
  auto &src_pts = pts_top.at(src());

  llvm::dbgs() << "dest_pts before: " << dest_pts << "\n";
  // FIXME: also respect strong updates?
  // change =
  dest_pts |= src_pts;
  llvm::dbgs() << "dest_pts after: " << dest_pts << "\n";

  // If we updated the set, wake all of our successors
  // For each successor partition
  std::for_each(std::begin(part_succs_), std::end(part_succs_),
      [this, &work, &dug, &dest_pts]
      (std::pair<DUG::PartID, DUG::DUGid> &part_pr) {
    auto part_id = part_pr.first;
    auto dug_id = part_pr.second;
    auto &nd = dug.getNode(dug_id);
    bool c = false;

    llvm::dbgs() << "nd.in is: " << nd.in() << "\n";

    // This is a strong update, right?  We should be able to just set it...
    c = nd.in().orPart(dest_pts, dug.objToPartMap(), part_id);

    if (c) {
      llvm::dbgs() << "  Pushing part nd to work: " << nd.id() << "\n";
      work.push(&nd);
    }
  });

  std::for_each(succ_begin(), succ_end(),
      [&dug, &work](DUG::EdgeID id) {
    auto &edge = dug.getEdge(id);
    auto &nd = dug.getNode(edge.dest());
    llvm::dbgs() << "  Pushing non-part nd to work: " << nd.id() << "\n";
    work.push(&nd);
  });
}

