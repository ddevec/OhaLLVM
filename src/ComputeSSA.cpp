/*
 * Copyright (C) 2015 David Devecsery
 */

#include <set>
#include <utility>
#include <vector>

#include "include/SpecSFS.h"

#include "include/SEG.h"
#include "include/DUG.h"


// Combine all SCCs in Xp in G
void T4(DUG::ControlFlowGraph &G, const DUG::ControlFlowGraph &Xp) {
  // For each SCC in Xp combine the nodes in G
  std::for_each(std::begin(Xp), std::end(Xp),
      [&G](const DUG::ControlFlowGraph::node_iter_type &pr) {
    // Get the rep node in G
    // Get the rep in Xp
    const DUG::CFGNode &nd = llvm::cast<DUG::CFGNode>(*pr.second);

    // Get the node to unite from G
    auto &rep_node = G.getNode<DUG::CFGNode>(nd.id());

    std::for_each(nd.rep_begin(), nd.rep_end(),
        [&G, &rep_node](DUG::CFGid rep_id) {
      // Don't unite rep with itself... thats silly
      if (rep_id != rep_node.id()) {
        rep_node.unite(G, G.getNode(rep_id));
      }
    });
  });
}

// Now, for each P-node in G1 (output from T4) with precise 1 predecessor,
//   we combine that node with its predecessor
void T2(DUG::ControlFlowGraph &G, const DUG::ControlFlowGraph &Xp) {
  // Visit Xp in topological order
  std::for_each(Xp.topo_begin(), Xp.topo_end(),
      [&G](DUG::CFGid xp_id) {
    auto &w_node = G.getNode<DUG::CFGNode>(xp_id);
    if (w_node.preds().size() == 1) {
      auto &pred_node = G.getNode<DUG::CFGNode>(*(std::begin(w_node.preds())));
      w_node.unite(G, pred_node);
    }
  });
}

void T7(DUG::ControlFlowGraph &G) {
  std::for_each(std::begin(G), std::end(G),
      [&G](DUG::ControlFlowGraph::node_iter_type &pr) {
      auto &node = llvm::cast<DUG::CFGNode>(*pr.second);

      // If its a c-node, remove all preceeding edges
      if (node.c()) {
        // Note, we're copying node.preds here... so we can delete it
        std::vector<DUG::CFGid> preds(std::begin(node.preds()),
          std::end(node.preds()));

        std::for_each(std::begin(preds), std::end(preds),
            [&G, &node](DUG::CFGid pred_id) {
          auto pr = std::make_pair(pred_id, node.id());
          G.removeEdge(pr);
        });
      }
  });
}

// Okay, now remove any u-nodes (nodes that we don't directly care about) which
// don't effect any r-nodes (nodes that we do care about)
// To do this we do a reverse topological visit of the graph from each R node,
// and mark all visited nodes as needed.  We then remove any unmarked nodes.
void T6(DUG::ControlFlowGraph &G) {
  std::set<DUG::CFGid> visited;
  // For each R node
  std::for_each(std::begin(G), std::end(G),
      [&G, &visited](DUG::ControlFlowGraph::node_iter_type &pr) {
    auto &node = llvm::cast<DUG::CFGNode>(*pr.second);
    // Mark the reverse topolocial sort of each r-node
    // Note, we don't need to visit visited r nodes
    if (node.r() &&
        visited.find(node.id()) == std::end(visited)) {
      // Do a topological search in reverse
      std::for_each(
          G.topo_rbegin(node.id()),
          G.topo_rend(node.id()),
          [&G, &visited](DUG::CFGid visit_id) {
        visited.insert(visit_id);
      });
    }
  });

  // Figure out which nodes are unused
  std::vector<DUG::CFGid> remove_list;
  std::for_each(std::begin(G), std::end(G),
      [&G, &visited, &remove_list](DUG::ControlFlowGraph::node_iter_type &pr) {
    DUG::CFGid id = pr.first;
    if (visited.find(id) == std::end(visited)) {
      remove_list.push_back(id);
    }
  });

  // Remove any nodes not marked as needed
  std::for_each(std::begin(remove_list), std::end(remove_list),
      [&G](DUG::CFGid rm_id) {
    G.removeNode(rm_id);
  });
}

// merge all up-nodes with exactly one successor with their successor
void T5(DUG::ControlFlowGraph &G) {
  // Get a topological ordering of all up-nodes
  // For each up-node in said ordering
  // Visit each node topologically
  std::vector<DUG::CFGid> unite_ids;
  std::for_each(G.topo_begin(), G.topo_end(),
      [&G, &unite_ids](DUG::CFGid topo_id) {
    auto &nd = G.getNode<DUG::CFGNode>(topo_id);
    // If the node is a up-node
    if (nd.u() && nd.p()) {
      // If the node has a unique successor:
      if (nd.succs().size() == 1) {
        // NOTE: I can't unite in the loop, it will screw with my iteration...
        // so I create a unite list to do later
        unite_ids.push_back(nd.id());
      }
    }
  });

  std::for_each(std::begin(unite_ids), std::end(unite_ids),
    [&G](DUG::CFGid unite_id) {
    auto &unite_node = G.getNode<DUG::CFGNode>(unite_id);
    assert(unite_node.succs().size() == 1);
    auto &succ_node = G.getNode<DUG::CFGNode>(*std::begin(unite_node.succs()));

    unite_node.unite(G, succ_node);
  });
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
  // NOTE: This will merge the nodes for me
  Gp.createSCC();

  // T4 -- This transform collapses a set of strongly connected p (preserving)
  // nodes into a single node.
  T4(G, Gp);

  // T2 -- If a node is a p-node and has precisely one predecessor, it may be
  // merged with that predecessor
  T2(G, Gp);

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

