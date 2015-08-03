/*
 * Copyright (C) 2015 David Devecsery
 */

#include <set>
#include <utility>
#include <vector>

#include "include/SpecSFS.h"

#include "include/SEG.h"
#include "include/ControlFlowGraph.h"


// Ramalingams {{{
// Transforms {{{
// Combine all SCCs in Xp in G
void T4(CFG::ControlFlowGraph &G, const CFG::ControlFlowGraph &Xp) {
  // For each SCC in Xp combine the nodes in G
  llvm::dbgs() << "Running T4\n";
  std::for_each(std::begin(Xp), std::end(Xp),
      [&G](const CFG::ControlFlowGraph::node_iter_type &pr) {
    // Get the rep node in G
    // Get the rep in Xp
    const CFG::Node &nd = llvm::cast<CFG::Node>(*pr.second);

    // Get the node to unite from G
    auto &rep_node = G.getNode<CFG::Node>(nd.id());

    std::for_each(nd.rep_begin(), nd.rep_end(),
        [&G, &rep_node](CFG::CFGid rep_id) {
      // Don't unite rep with itself... thats silly
      if (rep_id != rep_node.id()) {
        rep_node.unite(G, G.getNode(rep_id));
      }
    });
  });
  llvm::dbgs() << "Finished T4\n";
}

// Now, for each P-node in G1 (output from T4) with precise 1 predecessor,
//   we combine that node with its predecessor
void T2(CFG::ControlFlowGraph &G, const CFG::ControlFlowGraph &Xp) {
  // Visit Xp in topological order
  llvm::dbgs() << "Running T2\n";
  std::for_each(Xp.topo_begin(), Xp.topo_end(),
      [&G](CFG::CFGid xp_id) {
    // llvm::dbgs() << "visiting node: " << xp_id << "\n";
    auto &w_node = G.getNode<CFG::Node>(xp_id);
    // llvm::dbgs() << "preds().size() is: " << w_node.preds().size() << "\n";
    if (w_node.preds().size() == 1) {
      auto &pred_node = G.getNode<CFG::Node>(*(std::begin(w_node.preds())));
      /*
      llvm::dbgs() << "Uniting with pred: " <<
          *std::begin(w_node.preds()) << "\n";
      */
      w_node.unite(G, pred_node);
    }
  });

  llvm::dbgs() << "Finished T2\n";
}

void T7(CFG::ControlFlowGraph &G) {
  llvm::dbgs() << "Running T7\n";
  std::for_each(G.rep_begin(), G.rep_end(),
      [&G](CFG::ControlFlowGraph::node_iter_type &pr) {
      auto &node = llvm::cast<CFG::Node>(*pr.second);

      // If its a c-node, remove all preceeding edges
      if (node.c()) {
        // Note, we're copying node.preds here... so we can delete it
        std::vector<CFG::CFGid> preds(std::begin(node.preds()),
          std::end(node.preds()));

        std::for_each(std::begin(preds), std::end(preds),
            [&G, &node](CFG::CFGid pred_id) {
          auto pr = std::make_pair(pred_id, node.id());
          G.removeEdge(pr);
        });
      }
  });
  llvm::dbgs() << "Finished T7\n";
}

// Okay, now remove any u-nodes (nodes that we don't directly care about) which
// don't effect any r-nodes (nodes that we do care about)
// To do this we do a reverse topological visit of the graph from each R node,
// and mark all visited nodes as needed.  We then remove any unmarked nodes.
void T6(CFG::ControlFlowGraph &G) {
  std::set<CFG::CFGid> visited;
  // For each R node
  llvm::dbgs() << "Running T6\n";
  std::for_each(G.rep_begin(), G.rep_end(),
      [&G, &visited](CFG::ControlFlowGraph::node_iter_type &pr) {
    auto &node = llvm::cast<CFG::Node>(*pr.second);
    // Only deal with marked non-rep nodes
    // Mark the reverse topolocial sort of each r-node
    // Note, we don't need to visit visited r nodes
    if (node.r() &&
        visited.find(node.id()) == std::end(visited)) {
      // Do a topological search in reverse
      std::for_each(
          G.topo_rbegin(node.id()),
          G.topo_rend(node.id()),
          [&G, &visited](CFG::CFGid visit_id) {
        visited.insert(visit_id);
      });
    }
  });

  // Figure out which nodes are unused
  std::vector<CFG::CFGid> remove_list;
  std::for_each(G.rep_begin(), G.rep_end(),
      [&G, &visited, &remove_list](CFG::ControlFlowGraph::node_iter_type &pr) {
    CFG::CFGid id = pr.first;
    if (visited.find(id) == std::end(visited)) {
      remove_list.push_back(id);
    }
  });

  // Remove any nodes not marked as needed
  std::for_each(std::begin(remove_list), std::end(remove_list),
      [&G](CFG::CFGid rm_id) {
    G.removeNode(rm_id);
  });
  llvm::dbgs() << "Finished T6\n";
}

// merge all up-nodes with exactly one successor with their successor
void T5(CFG::ControlFlowGraph &G) {
  // Get a topological ordering of all up-nodes
  // For each up-node in said ordering
  // Visit each node topologically
  llvm::dbgs() << "Running T5\n";

  // Create a new graph, with only up-nodes
  // Start with Gup as a clone of G
  CFG::ControlFlowGraph Gup = G.convert<CFG::Node, CFG::Edge>();

  // Now, remove any non-up nodes
  std::vector<CFG::CFGid> remove_list;
  std::for_each(Gup.rep_begin(), Gup.rep_end(),
      [&remove_list](CFG::ControlFlowGraph::node_iter_type &pr) {
    auto &nd = llvm::cast<CFG::Node>(*pr.second);
    // Note any non-up node to be removed post iteration
    if (!nd.u() || !nd.p()) {
      remove_list.push_back(nd.id());
    }
  });

  assert(std::unique(std::begin(remove_list), std::end(remove_list)) ==
      std::end(remove_list));

  // Remove any non-up-nodes from Gup
  std::for_each(std::begin(remove_list), std::end(remove_list),
      [&Gup] (CFG::CFGid id) {
    Gup.removeNode(id);
  });

  // Now, visit each up-node in G in a topological order with repsect to the
  //     up-nodes -- We use Gup for this
  std::vector<CFG::CFGid> unite_ids;
  std::for_each(Gup.topo_begin(), Gup.topo_end(),
      [&G, &unite_ids](CFG::CFGid topo_id) {
    auto &nd = G.getNode<CFG::Node>(topo_id);
    // This had better be a up-node...
    assert(nd.u() && nd.p());

    // If the node has a unique successor:
    if (nd.succs().size() == 1) {
      // NOTE: I can't unite in the loop, it will screw with my iteration...
      // so I create a unite list to do later
      unite_ids.push_back(nd.id());
    }
  });

  // Now, unite any note that was denoted as being united
  std::for_each(std::begin(unite_ids), std::end(unite_ids),
    [&G](CFG::CFGid unite_id) {
    auto &unite_node = G.getNode<CFG::Node>(unite_id);
    assert(unite_node.succs().size() == 1);
    auto &succ_node = G.getNode<CFG::Node>(*std::begin(unite_node.succs()));

    unite_node.unite(G, succ_node);
  });
  llvm::dbgs() << "Finished T5\n";
}
//}}}

void Ramalingam(CFG::ControlFlowGraph &G, const ObjectMap &omap) {
  // Start by restricting G to only p-nodes, this gives is "Gp"
  // Make Gp a copy of G
  G.printDotFile("G.dot", omap);
  CFG::ControlFlowGraph Gp = G.convert<CFG::Node, CFG::Edge>();

  Gp.printDotFile("Gp_orig.dot", omap);

  std::vector<CFG::CFGid> remove_list;
  std::for_each(std::begin(Gp), std::end(Gp),
      [&remove_list]
      (CFG::ControlFlowGraph::node_iter_type &pr) {
    auto &node = llvm::cast<CFG::Node>(*pr.second);
    // If the node is non-preserving, remove it
    if (!node.p()) {
      remove_list.push_back(pr.first);
    }
  });

  // Remove all non-preserving nodes from Gp
  std::for_each(std::begin(remove_list), std::end(remove_list),
      [&Gp](CFG::CFGid id) {
    Gp.removeNode(id);
  });

  Gp.printDotFile("Gp.dot", omap);

  // Now get the SCC version of Gp
  // NOTE: This will merge the nodes for me
  Gp.createSCC();

  Gp.printDotFile("Xp.dot", omap);

  // T4 -- This transform collapses a set of strongly connected p (preserving)
  // nodes into a single node.
  T4(G, Gp);

  G.printDotFile("G4.dot", omap);

  // T2 -- If a node is a p-node and has precisely one predecessor, it may be
  // merged with that predecessor
  T2(G, Gp);

  G.printDotFile("G2.dot", omap);

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

  G.printDotFile("G7.dot", omap);

  // T6 -- applys to any set of u-nodes without a successor (aka, the set of
  // nodes has no edge from a node to a node outside of the set).  We remove
  // the set X, as well as any edges incident on them.  (Incident in graph
  // theory means the edge is connected to a vertex, either in or out).
  T6(G);

  G.printDotFile("G6.dot", omap);

  // T5 -- merges any up-node with exactly one predecessor with its predecessor
  T5(G);

  G.printDotFile("G5.dot", omap);
}
//}}}

// Here we preform Ramalingam's algorithm from the paper "On Sparse Evaluation
// Representation" to create a SSA form of the graph.  This consists of a series
// of 5 transforms, T2,T4,T5,T6, and T7  The tramsforms are outlined in
// the paper.

// I suppose this requires knowing the set of nodes we care about... as we're
// calculating the "Partially Equivalent Flow Graph" (PEFG) representation
CFG::ControlFlowGraph
SpecSFS::computeSSA(const CFG::ControlFlowGraph &cfg) {
  // This essentially copies the CFG
  ObjectMap omap;
  CFG::ControlFlowGraph ret = cfg.convert<CFG::Node, CFG::Edge>();

  Ramalingam(ret, omap);

  return std::move(ret);
}

