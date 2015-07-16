/*
 * Copyright (C) 2015 David Devecsery
 */

#include <utility>
#include <vector>

#include "include/SpecSFS.h"

#include "include/SEG.h"
#include "include/DUG.h"


void T4(DUG::ControlFlowGraph &, DUG::ControlFlowGraph &) {
  // Now, for each element in Gp_SCC, collapse an element G into that same range
}

void T2(DUG::ControlFlowGraph &) {
}

void T7(DUG::ControlFlowGraph &) {
}

void T6(DUG::ControlFlowGraph &) {
}

void T5(DUG::ControlFlowGraph &) {
}

void Ramalingam(DUG::ControlFlowGraph &G) {
  // Start by restricting G to only p-nodes, this gives is "Gp"
  // Make Gp a copy of G
  DUG::ControlFlowGraph Gp = G.convert<DUG::CFGNode, DUG::CFGEdge>();

  std::vector<DUG::CFGid> remove_list;
  std::for_each(std::begin(Gp), std::end(Gp),
      [&remove_list]
      (DUG::ControlFlowGraph::node_iter_type &pr) {
    auto &node = llvm::cast<DUG::CFGNode>(*pr.second);
    // If the node is non-preserving, remove it
    if (!node.p()) {
      remove_list.push_back(pr.first);
    }
  });

  // Remove all non-preserving nodes from Gp
  std::for_each(std::begin(remove_list), std::end(remove_list),
      [&Gp](DUG::CFGid id) {
    Gp.removeNode(id);
  });

  // Now get the SCC version of Gp
  Gp.createSCC();

  // T4 -- This transform collapses a set of strongly connected p (preserving)
  // nodes into a single node.
  T4(G, Gp);

  // T2 -- If a node is a p-node and has precisely one predecessor, it may be
  // merged with that predecessor
  T2(G);

  // For the remainder of the transformations we are concerned with calculating
  // a "Partially Equivalent Flow Graph" or a graph for which the data-flow
  // solution is only requried for some set of nodes (known henceforth as
  // r-nodes).  The set of nodes which the dataflow solution is not required is
  // a u-node, and preserving u-nodes are up-nodes

  // For T7 we will add yet an additional class of nodes, the c-node.  If
  // a node is a m (modifying) node, but the modification function is a
  // constant, it is refered to as a c-node.

  // T7 -- If the c-node transformation is to delete the incoming edges, then we
  // delete the edges from the graph.
  T7(G);

  // T6 -- applys to any set of u-nodes without a successor (aka, the set of
  // nodes has no edge from a node to a node outside of the set).  We remove
  // the set X, as well as any edges incident on them.  (Incident in graph
  // theory means the edge is connected to a vertex, either in or out).
  T6(G);

  // T5 -- merges any up-node with exactly one predecessor with its predecessor
  T5(G);
}

// Here we preform Ramalingam's algorithm from the paper "On Sparse Evaluation
// Representation" to create a SSA form of the graph.  This consists of a series
// of 5 transforms, T2,T4,T5,T6, and T7  The tramsforms are outlined in
// the paper.

// I suppose this requires knowing the set of nodes we care about... as we're
// calculating the "Partially Equivalent Flow Graph" (PEFG) representation
DUG::ControlFlowGraph
SpecSFS::computeSSA(const DUG::ControlFlowGraph &CFG) {
  // This essentially copies the CFG
  DUG::ControlFlowGraph ret = CFG.convert<DUG::CFGNode, DUG::CFGEdge>();

  Ramalingam(ret);

  return std::move(ret);
}

