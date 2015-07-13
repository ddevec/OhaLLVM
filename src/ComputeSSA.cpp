/*
 * Copyright (C) 2015 David Devecsery
 */

#include <vector>

#include "include/SpecSFS.h"

#include "include/SEG.h"
#include "include/DUG.h"

struct PEFGData;
typedef SEG<DUG::CFGid, DUG::CFGid, PEFGData> PEFG;
typedef PEFG::Node PEFGNode;

class PEFGData {
 public:
    bool p() const {
      return m_;
    }

    bool m() const {
      return !m_;
    }

    bool r() const {
      return r_;
    }

    bool u() const {
      return !r_;
    }

    bool c() const {
      return c_;
    }

    template<typename cmrNode>
    void unite(const cmrNode &n) {
      // If they were the m-node and they were a c-node then we are a
      //     c-node now
      c_ |= n.c();
      m_ |= n.m();
      r_ |= n.r();
    }

    void setM() {
      m_ = true;
    }

    void setR() {
      r_ = true;
    }

    void setC() {
      c_ = true;
    }

 private:
    // Private variables {{{
    // To identify p/m nodes (see computeSSA comments)
    bool m_ = false;
    // To identify r/u nodes (see computeSSA comments)
    bool r_ = false;
    // To identify constant nodes (see computeSSA comments)
    bool c_ = false;
    //}}}
};

void T4(PEFG &) {
}

void T2(PEFG &) {
}

void T7(PEFG &) {
}

void T6(PEFG &) {
}

void T5(PEFG &) {
}

void Ramalingam(PEFG &G) {
  // T4 -- This transform collapses a set of strongly connected p (preserving)
  // nodes into a single node.
  T4(G);

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
// calculating the "Partially Equivalent Flow Graph" representation
bool SpecSFS::computeSSA(DUG &,
    const std::vector<DUG::CFGEdge> &) {
  /*
  auto converter = [&graph](DUG::CFGid id){
    return id;
  };

  auto init_fcn = [&graph](PEFGNode &) { };

  auto add_node = [&graph](const DUG::CFGEdge &con,
      PEFGNode &src, PEFGNode &dest) {
    // Get the DU nodes from the graph
    DUG::CFGNode &du_dest = graph.getCFGNode(con.dest());
    DUG::CFGNode &du_src = graph.getCFGNode(con.src());

    // Populate our graph with p-nodes
    if (!du_dest.m() && !du_src.m()) {
      src.addSucc(dest);
      dest.addPred(src);
      dest.data().unite(src);
    }
  };

  PEFG G(std::begin(def_use), std::end(def_use),
      converter, init_fcn, add_node);

  Ramalingam(G);
  */

  return false;
}

