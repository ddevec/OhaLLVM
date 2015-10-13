/*
 * Copyright (C) 2015 David Devecsery
 */

#include <cstdint>
#include <cstdlib>

#include <iostream>
#include <map>

#include "include/SEG.h"

static void test_assert(bool check, std::string msg) {
  if (!check) {
    std::cerr << "ERROR: " << msg << std::endl;
    exit(EXIT_FAILURE);
  }
}

class Node : public SEG::Node {
 public:
    Node(SEG::NodeID node_id) :
      SEG::Node(NodeKind::CFGNode, node_id) { }
};

int main(void) {
  /* Testing SCC in seg, we're going to make a simple graph:
   *       a
   *       |
   *       V
   *       b
   *      / ^
   *     v   \
   *     c-->d
   *
   * And calculate its scc:
   *   a->{b,c,d}
   */

  // First create the graph:
  SEG graph;

  // test1
  auto a = graph.addNode<Node>();
  auto b = graph.addNode<Node>();
  auto c = graph.addNode<Node>();
  auto d = graph.addNode<Node>();

  // a predecesses b
  graph.addPred(b, a);
  // b predecesses c
  graph.addPred(c, b);
  // d predecesses c
  graph.addPred(d, c);
  // d predecesses b
  graph.addPred(b, d);

  // Convert to an SCC
  graph.createSCC();

  // Check out the graph, make sure it works
  auto a_rep = graph.getNode(a).id();
  auto b_rep = graph.getNode(b).id();
  auto c_rep = graph.getNode(c).id();
  auto d_rep = graph.getNode(d).id();

  test_assert(b_rep == c_rep, "B and C not merged");
  test_assert(c_rep == d_rep, "C and D not merged");
  test_assert(a_rep != b_rep, "A and B merged incorrectly");

  return EXIT_SUCCESS;
}

