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
  // Testing SCC in seg, we're going to recreate the wikipedia graph on the SCC
  //    page

  // First create the graph:
  SEG graph;

  // test1
  auto a = graph.addNode<Node>();
  auto b = graph.addNode<Node>();
  auto c = graph.addNode<Node>();
  auto d = graph.addNode<Node>();
  auto e = graph.addNode<Node>();
  auto f = graph.addNode<Node>();
  auto g = graph.addNode<Node>();
  auto h = graph.addNode<Node>();

  graph.addPred(a, e);
  graph.addPred(b, a);
  graph.addPred(e, b);
  graph.addPred(f, b);
  graph.addPred(f, e);
  graph.addPred(f, g);
  graph.addPred(g, f);
  graph.addPred(g, c);
  graph.addPred(g, h);
  graph.addPred(c, b);
  graph.addPred(c, d);
  graph.addPred(d, c);
  graph.addPred(d, h);
  graph.addPred(h, d);

  // Convert to an SCC
  graph.createSCC();

  // Check out the graph, make sure it works
  auto a_rep = graph.getNode(a).id();
  auto b_rep = graph.getNode(b).id();
  auto c_rep = graph.getNode(c).id();
  auto d_rep = graph.getNode(d).id();
  auto e_rep = graph.getNode(e).id();
  auto f_rep = graph.getNode(f).id();
  auto g_rep = graph.getNode(g).id();
  auto h_rep = graph.getNode(h).id();

  test_assert(a_rep == e_rep, "A and E not merged");
  test_assert(a_rep == b_rep, "A and B not merged");
  test_assert(f_rep == g_rep, "B and F not merged");
  test_assert(c_rep == d_rep, "C and D not merged");
  test_assert(c_rep == h_rep, "C and H not merged");

  test_assert(a_rep != f_rep, "A and F incorrectly merged");
  test_assert(a_rep != h_rep, "A and H incorrectly merged");
  test_assert(f_rep != h_rep, "F and H incorrectly merged");

  return EXIT_SUCCESS;
}

