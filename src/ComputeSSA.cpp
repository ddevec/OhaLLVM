
#include "include/SpecSFS.h"


// Here we preform Ramalingam's algorithm from the paper "On Sparse Evaluation
// Representation" to create a SSA form of the graph.  This consists of a series
// of 5 transforms, T2,T4,T5,T6, and T7  The tramsforms are outlined in the paper.

// I suppose this requires knowing the set of nodes we care about... as we're
// calculating the "Partially Equivalent Flow Graph" representation
bool SpecSFS::computeSSA(SEG &graph) {
  // T4 -- This transform collapses a set of strongly connected p (preserving) nodes
  // into a single node.
  T4(graph);

  // T2 -- If a node is a p-node and has precisely one predecessor, it may be merged
  // with that predecessor
  T2(graph);

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
  T7(graph);

  // T6 -- applys to any set of u-nodes without a successor (aka, the set of nodes
  // has no edge from a node to a node outside of the set).  We remove the set
  // X, as well as any edges incident on them.  (Incident in graph theory means
  // the edge is connected to a vertex, either in or out).
  T6(graph);

  // T5 -- merges any up-node with exactly one predecessor with its predecessor
  T5(graph);
  
  return false;
}

