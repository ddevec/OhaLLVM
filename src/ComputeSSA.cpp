/*
 * Copyright (C) 2015 David Devecsery
 */
// #define SPECSFS_DEBUG

#include <algorithm>
#include <set>
#include <utility>
#include <vector>

#include "include/SpecSFS.h"

#include "include/Debug.h"

#include "include/SEG.h"
#include "include/ControlFlowGraph.h"


// Ramalingams {{{
// Transforms {{{
// Combine all SCCs in Xp in G
void T4(SEG &G, const SEG &Xp) {
  PerfTimerPrinter X(dbg, "T4");
  // For each SCC in Xp combine the nodes in G
  dout("Running T4\n");
  // Do this by iterating G
  std::for_each(std::begin(G), std::end(G),
      [&G, &Xp](const CFG::ControlFlowGraph::node_iter_type &pnode) {
    // Get the node in G
    auto &nd = cast<CFG::Node>(*pnode);

    dout("  Evaluating Node: " << nd.id() << "\n");

    // Now, get the rep from Xp
    auto pxp_rep = Xp.tryGetNode<CFG::Node>(nd.id());
    // auto &xp_rep = Xp.getNode<CFG::Node>(nd.id());

    if (pxp_rep != nullptr) {
      auto &xp_rep = *pxp_rep;
      dout("    Xp node has rep: " << xp_rep.id() << "\n");
      // If the rep from xp has a different ID than G:
      if (xp_rep.id() != nd.id()) {
        // Get the G node that should be rep, and unite the two
        auto &g_rep = G.getNode(xp_rep.id());

        // Remove the edge from rep to nd, as we're about to unite them
        G.removePred(nd.id(), xp_rep.id());
        // And any edges the other way!
        G.removePred(xp_rep.id(), nd.id());

        dout("!!  Running unite rep: " << xp_rep.id() << "\n");
        g_rep.unite(G, nd);
      }
    }
  });

  dout("Finished T4\n");
}

// Now, for each P-node in G1 (output from T4) with precisely 1 predecessor,
//   we combine that node with its predecessor
void T2(SEG &G, SEG &Xp) {
  PerfTimerPrinter X(dbg, "T2");
  // Visit Xp in topological order
  dout("Running T2\n");
  std::for_each(Xp.topo_begin(), Xp.topo_end(),
      [&G, &Xp](CFG::NodeID xp_id) {
    dout("visiting node: " << xp_id << "\n");
    auto &w_node = G.getNode<CFG::Node>(xp_id);

    bool multi_preds = false;
    SEG::NodeID saved_pred = SEG::NodeID::invalid();

    for (auto pred_id : w_node.preds()) {
      dout("  visiting raw_pred: " << pred_id << "\n");
      auto &pred_node = G.getNode<CFG::Node>(pred_id);
      dout("  visiting pred: " << pred_node.id() << "\n");

      if (saved_pred == SEG::NodeID::invalid()) {
        saved_pred = pred_node.id();
      } else if (saved_pred != pred_node.id()) {
        multi_preds = true;
        break;
      }
    }

    // We don't unite if the node has more than 1 pred
    // We don't unite if we're our own predecessor
    if (!multi_preds && saved_pred != SEG::NodeID::invalid()
        && saved_pred != w_node.id()) {
      auto &pred_node = G.getNode<CFG::Node>(saved_pred);

      // Remove the edge from pred to w before we unite
      G.removePred(w_node.id(), pred_node.id());

      dout("!!Uniting: " << pred_node.id() << ", "
          << w_node.id() << "\n");
      pred_node.unite(G, w_node);
    }
  });

  dout("Finished T2\n");
}

void T7(SEG &G) {
  PerfTimerPrinter X(dbg, "T7");
  dout("Running T7\n");
  std::for_each(std::begin(G), std::end(G),
      [&G](CFG::ControlFlowGraph::node_iter_type &pnode) {
      if (pnode != nullptr) {
        auto &node = cast<CFG::Node>(*pnode);

        // If its a c-node, remove all preceding edges
        if (node.c()) {
          // Note, we're copying node.preds here... so we can delete it
          std::vector<CFG::NodeID> preds(std::begin(node.preds()),
            std::end(node.preds()));

          std::for_each(std::begin(preds), std::end(preds),
              [&G, &node](CFG::NodeID pred_id) {
            G.removePred(node.id(), pred_id);
          });
        }
      }
  });
  dout("Finished T7\n");
}

// Okay, now remove any u-nodes (nodes that we don't directly care about) which
// don't effect any r-nodes (nodes that we do care about)
// To do this we do a reverse topological visit of the graph from each R node,
// and mark all visited nodes as needed.  We then remove any unmarked nodes.
static void T6_visit(SEG &G, CFG::Node &node, std::vector<int8_t> &visit_info) {
  // If this node hasn't been visited
  assert(node.id().val() < node_info.size());
  auto visited = visit_info[node.id().val()];
  if (visited == 0) {
    visit_info[node.id().val()] = 1;

    for (auto pred_id : node.preds()) {
      auto &pred = G.getNode<CFG::Node>(pred_id);
      T6_visit(G, pred, visit_info);
    }
  }
}

void T6(SEG &G) {
  PerfTimerPrinter X(dbg, "T6");
  dout("Running T6\n");
  std::vector<int8_t> visit_info(G.getNumNodes(), 0);
  // For each R node
  std::for_each(std::begin(G), std::end(G),
      [&G, &visit_info]
      (CFG::ControlFlowGraph::node_iter_type &pnode) {
    auto &node = cast<CFG::Node>(*pnode);

    // Mark this node and its preds, iff
    //   It is an r node
    //   It has not been marked
    if (node.r() &&
        !visit_info[node.id().val()]) {
      T6_visit(G, node, visit_info);
    }
  });

  // remove any unmarked nodes
  // Remove any nodes not marked as needed
  for (size_t i = 0; i < visit_info.size(); i++) {
    SEG::NodeID id(i);

    uint8_t visited = visit_info[i];

    if (visited == 0) {
      auto pnode = G.tryGetNode(id);

      if (pnode && pnode->id() == id) {
        G.tryRemoveNode(id);
      }
    }
  }
  dout("Finished T6\n");
}

// merge all up-nodes with exactly one successor with their successor
void T5(SEG &G) {
  PerfTimerPrinter X(dbg, "T5");
  dout("Running T5\n");

  // Get a topological ordering of all up-nodes
  // For each up-node in said ordering
  // Create a new graph, with only up-nodes
  // Start with Gup as a clone of G

  CFG::ControlFlowGraph Gup = G.clone<CFG::Node>();

  // Now, remove any non-up nodes
  std::for_each(std::begin(G), std::end(G),
      [&Gup](CFG::ControlFlowGraph::node_iter_type &pnode) {
    auto &node = cast<CFG::Node>(*pnode);

    // remove any non-up nodes
    if (!node.u() || !node.p()) {
      dout("Gup Removing: " << node.id() << "\n");
      Gup.removeNode(node.id());
    }
  });

  // Now, visit each up-node in G in a topological order with repsect to the
  //     up-nodes -- We use Gup for this
  std::for_each(Gup.topo_begin(), Gup.topo_end(),
      [&G](CFG::NodeID topo_id) {
    auto &nd = G.getNode<CFG::Node>(topo_id);
    // This had better be a up-node...
    assert(nd.isRep());
    assert(nd.u() && nd.p());
    dout("visiting node: " << topo_id << "\n");

    bool multi_succs = false;
    SEG::NodeID saved_succ = SEG::NodeID::invalid();

    for (auto succ_id : nd.succs()) {
      dout("  visiting raw_succ: " << succ_id << "\n");
      auto &succ_node = G.getNode<CFG::Node>(succ_id);
      dout("  visiting succ: " << succ_node.id() << "\n");

      if (saved_succ == SEG::NodeID::invalid()) {
        saved_succ = succ_node.id();
      } else if (saved_succ != succ_node.id()) {
        multi_succs = true;
        break;
      }
    }

    // We don't unite if the node has more than 1 pred
    // We don't unite if we're our own predecessor
    if (!multi_succs && saved_succ != nd.id()) {
      auto &succ_node = G.getNode<CFG::Node>(saved_succ);

      dout("!!Uniting: " << succ_node.id() << ", "
          << nd.id() << "\n");
      G.removeSucc(nd.id(), succ_node.id());
      G.removePred(succ_node.id(), nd.id());
      succ_node.unite(G, nd);
    }
  });

  dout("Finished T5\n");
}
//}}}

SEG createGp(const SEG &G) {
  PerfTimerPrinter X(dbg, "Gp");
  SEG ret = G.clone<CFG::Node>();

  // if_debug(ret.printDotFile("Gp_orig.dot", *g_omap));

  // Iterate each node in G (which is a clone of Gp)
  // If the node is non-P, remove it
  std::for_each(std::begin(G), std::end(G),
      [&ret] (const SEG::node_iter_type &pnode) {
    auto &node = cast<CFG::Node>(*pnode);
    // If the node is non-preserving, remove it
    if (!node.p()) {
      ret.removeNode(node.id());
    }
  });

  return std::move(ret);
}

void Ramalingam(SEG &G) {
  // Start by restricting G to only p-nodes, this gives is "Gp"
  // Make Gp a copy of G
  // if_debug(G.printDotFile("G.dot", *g_omap));

  SEG Gp = createGp(G);

  // if_debug(Gp.printDotFile("Gp.dot", *g_omap));

  // Now get the SCC version of Gp
  // NOTE: This will merge the nodes for me
  // We must clean edges before creating the SCC...
  {
    PerfTimerPrinter X(dbg, "Create SCC");
    dout("  Creating SCC\n");
    Gp.createSCC();
    dout("Gp Done\n");
  }

  // if_debug(Gp.printDotFile("Xp.dot", *g_omap));

  // T4 -- This transform collapses a set of strongly connected p (preserving)
  // nodes into a single node.
  T4(G, Gp);

  // if_debug(G.printDotFile("G4.dot", *g_omap));

  // Similar to sfs's rm_undef -- but no removal of r nodes
  {
    PerfTimerPrinter X(dbg, "cleanGraph");
    G.cleanGraph();
  }

  // T2 -- If a node is a p-node and has precisely one predecessor, it may be
  // merged with that predecessor
  T2(G, Gp);

  // if_debug(G.printDotFile("G2.dot", *g_omap));

  // For the remainder of the transformations we are concerned with calculating
  // a "Partially Equivalent Flow Graph" or a graph for which the data-flow
  // solution is only requried for some set of nodes (known henceforth as
  // r-nodes).  The set of nodes which the dataflow solution is not required is
  // a u-node, and preserving u-nodes are up-nodes

  // NOTE: We actually don't do T7, that is accounted for when we identify
  // objects (the alloc nodes are C nodes, which have no incoming edges)

  // For T7 we will add yet an additional class of nodes, the c-node.  If
  // a node is a m (modifying) node, but the modification function is a
  // constant, it is refered to as a c-node.

  // T7 -- If the c-node transformation is to delete the incoming edges, then we
  // delete the edges from the graph.
  // T7(G);

  // if_debug(G.printDotFile("G7.dot", *g_omap));

  // T6 -- applys to any set of u-nodes without a successor (aka, the set of
  // nodes has no edge from a node to a node outside of the set).  We remove
  // the set X, as well as any edges incident on them.  (Incident in graph
  // theory means the edge is connected to a vertex, either in or out).
  T6(G);

  // if_debug(G.printDotFile("G6.dot", *g_omap));

  // NOTE: T5 requires succ edges, we'll add them now:
  {
    PerfTimerPrinter X(dbg, "add succs");
    std::for_each(std::begin(G), std::end(G),
        [&G] (CFG::ControlFlowGraph::node_iter_type &pnode) {
      auto &preds = pnode->preds();
      auto succ_id = pnode->id();
      std::for_each(std::begin(preds), std::end(preds),
          [&G, &succ_id] (CFG::CFGid pred_id) {
        G.addSucc(pred_id, succ_id);
      });
    });
  }

  // T5 -- merges any up-node with exactly one predecessor with its predecessor
  T5(G);

  // if_debug(G.printDotFile("G5.dot", *g_omap));
}
//}}}

// Don't include SpecSFS stuff in unit test framework... I should clean all of
// these up later and compartmentalize more...
#ifndef SPECSFS_IS_TEST

// Here we preform Ramalingam's algorithm from the paper "On Sparse Evaluation
// Representation" to create a SSA form of the graph.  This consists of a series
// of 5 transforms, T2,T4,T5,T6, and T7  The tramsforms are outlined in
// the paper.

// I suppose this requires knowing the set of nodes we care about... as we're
// calculating the "Partially Equivalent Flow Graph" (PEFG) representation
void
SpecSFS::computeSSA(CFG::ControlFlowGraph &ret) {
  /*
  dbg << "pre-Ramalingam: ret contains cfg ids:";
  std::for_each(ret.node_map_begin(), ret.node_map_end(),
      [] (std::pair<const CFG::CFGid, CFG::NodeID> &node_pair) {
      dbg << " " << node_pair.first;
  });
  dbg << "\n";

  dbg << "Initial nodeset is:\n";
  std::for_each(std::begin(ret), std::end(ret),
      [] (CFG::ControlFlowGraph::node_iter_type &pnode) {
    dbg << "  node " << pnode->id() << ": ";
    extern ObjectMap &g_omap;
    pnode->print_label(dbg, g_omap);
    dbg << "\n";
  });
  */

  Ramalingam(ret);

  /*
  dbg << "post-Ramalingam: ret contains cfg ids:";
  std::for_each(ret.node_map_begin(), ret.node_map_end(),
      [] (std::pair<const CFG::CFGid, CFG::NodeID> &node_pair) {
      dbg << " " << node_pair.first;
  });
  dbg << "\n";
  */
}
#endif

