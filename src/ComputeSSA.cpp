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
static auto should_visit_default = [] (const SEG::Node &) -> bool {
  return true;
};

static auto scc_visit_default = [] (const SEG::Node &) { };

// NOTE: a topo order can be achieved by visiting each node on post_unite
template<typename should_visit = decltype(should_visit_default),
  typename scc_visit = decltype(scc_visit_default)>
class RunTarjans {
 public:
    static const int32_t IndexInvalid = -1;

    explicit RunTarjans(SEG &G,
        should_visit do_visit = should_visit_default,
        scc_visit do_scc_visit = scc_visit_default) :
        should_visit_(do_visit), scc_visit_(do_scc_visit),
        seg_(G), nodeData_(G.getNumNodes()) {
      for (auto &pnode : G) {
        auto &node = *pnode;
        auto &node_data = getData(node.id());
        // If this is both a unvisited node, and we should visit it
        if (node_data.index == IndexInvalid && should_visit_(node)) {
          tarjan_visit(node);
        }
      }
    }

 private:
    struct TarjanData {
      int32_t index = IndexInvalid;
      int32_t lowlink = IndexInvalid;
      bool onStack = false;
    };

    struct TarjanData &getData(SEG::NodeID id) {
      assert(id != SEG::NodeID::invalid());
      assert(id.val() < nodeData_.size());
      return nodeData_[id.val()];
    }

    void tarjan_visit(SEG::Node &node) {
      auto &node_data = getData(node.id());
      assert(!node_data.onStack);
      assert(node_data.index == IndexInvalid);
      node_data.index = nextIndex_;
      node_data.lowlink = nextIndex_;
      nextIndex_++;

      nodeStack_.push_back(node.id());
      node_data.onStack = true;

      for (auto pred_id : node.preds()) {
        auto &pred_node = seg_.getNode(pred_id);
        // If this node should be visited (allows us to exclude some nodes, like
        //   needed in Ramalingam's T4 transform)
        if (should_visit_(pred_node)) {
          auto &pred_data = getData(pred_node.id());
          if (pred_data.index == IndexInvalid) {
            tarjan_visit(pred_node);
            node_data.lowlink = std::min(pred_data.lowlink, node_data.lowlink);
          } else if (pred_data.onStack) {
            node_data.lowlink = std::min(node_data.lowlink, pred_data.index);
          }
        }
      }

      if (node_data.lowlink == node_data.index) {
        while (true) {
          auto merge_id = nodeStack_.back();
          nodeStack_.pop_back();
          auto &merge_node = seg_.getNode(merge_id);
          auto &merge_data = getData(merge_node.id());
          merge_data.onStack = false;

          if (merge_id == node.id()) {
            break;
          }

          node.unite(seg_, merge_node);
        }

        scc_visit_(node);
      }
    }

    // Visit fcns...
    should_visit &should_visit_;
    scc_visit &scc_visit_;

    SEG &seg_;

    int32_t nextIndex_ = 0;
    std::vector<SEG::NodeID> nodeStack_;
    std::vector<TarjanData> nodeData_;
};

void T4(SEG &G, std::vector<SEG::NodeID> &topo_order) {
  // PerfTimerPrinter X(dbg, "T4");
  dout("Running T4\n");

  auto p_only = [] (const SEG::Node &nd) -> bool {
      auto &node = cast<CFG::Node>(nd);
      return node.p();
  };

  auto save_topo = [&topo_order] (SEG::Node &nd) {
    topo_order.push_back(nd.id());
  };

  RunTarjans<decltype(p_only), decltype(save_topo)> (G, p_only, save_topo);

  dout("Finished T4\n");
}

// Now, for each P-node in G1 (output from T4) with precisely 1 predecessor,
//   we combine that node with its predecessor
void T2(SEG &G, const std::vector<SEG::NodeID> &topo_order) {
  // PerfTimerPrinter X(dbg, "T2");
  // Visit Xp in topological order
  dout("Running T2\n");
  for (auto topo_id : topo_order) {
    dout("visiting node: " << xp_id << "\n");
    auto &w_node = G.getNode<CFG::Node>(topo_id);

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
  }

  dout("Finished T2\n");
}

void T7(SEG &G) {
  // PerfTimerPrinter X(dbg, "T7");
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
  assert(node.id().val() < static_cast<int32_t>(visit_info.size()));
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
  // PerfTimerPrinter X(dbg, "T6");
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
  // PerfTimerPrinter X(dbg, "T5");
  dout("Running T5\n");

  auto up_nodes = [](SEG::Node &nd) -> bool {
    auto &node = cast<CFG::Node>(nd);
    return (node.p() && node.u());
  };

  auto t5_visit = [&G](SEG::Node &seg_nd) {
    auto &nd = cast<CFG::Node>(seg_nd);
    // This had better be a up-node...
    assert(nd.isRep());
    assert(nd.u() && nd.p());
    dout("visiting node: " << nd.id() << "\n");

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
  };

  // Do topo visit:
  // NOTE: Since The graph is guaranteed to be in normal form w/ respect to T4
  //   it cannot have a cycle of p nodes, so tarjans will just visit the set of
  //   p-nodes in topo-order
  RunTarjans<decltype(up_nodes), decltype(t5_visit)>(G, up_nodes, t5_visit);


  // Now, visit each up-node in G in a topological order with repsect to the
  //     up-nodes -- We use Gup for this
  /*
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
  */

  dout("Finished T5\n");
}
//}}}

void Ramalingam(SEG &G) {
  // Start by restricting G to only p-nodes, this gives is "Gp"
  // Make Gp a copy of G
  // if_debug(G.printDotFile("G.dot", *g_omap));

  // if_debug(Gp.printDotFile("Xp.dot", *g_omap));

  // Limmits lifetime of topo_order
  {
    std::vector<SEG::NodeID> topo_order;
    // T4 -- This transform collapses a set of strongly connected p (preserving)
    //   nodes into a single node.
    // Populates topo_order
    T4(G, topo_order);

    // if_debug(G.printDotFile("G4.dot", *g_omap));

    // Similar to sfs's rm_undef -- but no removal of r nodes
    G.cleanGraph();

    // T2 -- If a node is a p-node and has precisely one predecessor, it may be
    // merged with that predecessor
    T2(G, topo_order);
  }

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
    // PerfTimerPrinter X(dbg, "add succs");
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

