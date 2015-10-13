/*
 * Copyright (C) 2015 David Devecsery
 */

#include <cstdint>
#include <cstdlib>

#include <iostream>
#include <map>

#include "include/Debug.h"

#include "include/ControlFlowGraph.h"
#include "include/SEG.h"

extern void T4(SEG &G, const SEG &Xp);
extern void T2(SEG &G, SEG &Xp);
extern void T7(SEG &G);
extern void T6(SEG &G);
extern void T5(SEG &G);
extern void Ramalingam(SEG &G);
extern SEG createGp(const SEG &G);

static void test_assert(bool check, std::string msg) {
  if (!check) {
    std::cerr << "ERROR: " << msg << std::endl;
    exit(EXIT_FAILURE);
  }
}

int main(void) {
  /* Testing Gp creation
   * Nodes with captial letters are M nodes!
   *       A
   *       |
   *       V
   *       b<--
   *      /|  |
   *     v V  |
   *    d  C<-|---g (onlyconnects to C)
   *     \ |  |
   *      VV  |
   *       e---
   *       |
   *       V
   *       f
   *
   * Note: letter -> id#
   * A->0
   * b->1
   * C->2
   * d->3
   * e->4
   * f->5
   */

  // First create the graph:
  SEG G;

  // test1
  auto a = G.addNode<CFG::Node>();
  auto b = G.addNode<CFG::Node>();
  auto c = G.addNode<CFG::Node>();
  auto d = G.addNode<CFG::Node>();
  auto e = G.addNode<CFG::Node>();
  auto f = G.addNode<CFG::Node>();
  auto g = G.addNode<CFG::Node>();

  // Fill in M info
  {
    auto &a_node = G.getNode<CFG::Node>(a);
    auto &c_node = G.getNode<CFG::Node>(c);
    auto &f_node = G.getNode<CFG::Node>(f);
    a_node.setM();
    a_node.setR();
    c_node.setM();
    c_node.setR();

    f_node.setR();
  }

  // b's backedges
  G.addPred(b, a);
  G.addPred(b, e);
  // c's backedges
  G.addPred(c, b);
  // d's backedges
  G.addPred(d, b);
  // e's backedges
  G.addPred(e, d);
  G.addPred(e, c);
  // f's backedges
  G.addPred(f, e);

  G.addPred(c, g);

  // gimme Gp
  SEG Gp = createGp(G);

  // Then turn that into Xp:
  Gp.createSCC();

  /* NOTE: Gp looks like this:
   *   b
   *  / ^
   * V   \
   * e-->d   g
   */
  // Now, create the SCC of Gp:
  //  {b, e, d} are all one node
  //
  //  g

  // Now apply T4 on G
  // NOTE: TestCreateGp has already tested the creation of Gp
  T4(G, Gp);
  // G now looks like this: (tested in TestT4)
  //   A
  //   |   ----
  //   V   v  |
  // {b,e,d}->C<-g
  //   |
  //   V
  //   f
  //   
  
  // Now, we run T2
  // We expect the output to look like this:
  //   A
  //   |     ----
  //   V     V  |
  // {b,e,d,f}->C<-g
  T2(G, Gp);
  
  // We're double checking t2 for good measure
  // First, check that the correct nodes were united, and the correct nodes
  // remain distinct
  auto &a_node = G.getNode(a);
  auto &b_node = G.getNode(b);
  auto &c_node = G.getNode(c);
  auto &d_node = G.getNode(d);
  auto &e_node = G.getNode(e);
  auto &f_node = G.getNode(f);
  auto &g_node = G.getNode(g);

  // Ensure the b,d,e,f have been merged
  test_assert(b_node == d_node, "B and D not merged");
  test_assert(d_node == e_node, "D and E not merged");
  test_assert(b_node == f_node, "B and F not merged");
  // Also ensure the other nodes were not merged
  test_assert(a_node != b_node, "A and B incorrectly merged");
  test_assert(a_node != c_node, "A and C incorrectly merged");
  test_assert(a_node != g_node, "A and G incorrectly merged");
  test_assert(b_node != c_node, "B and C incorrectly merged");
  test_assert(b_node != g_node, "B and G incorrectly merged");
  test_assert(c_node != g_node, "C and G incorrectly merged");

  // Now, check the edges:
  // Verify correct preds
  bool c_found = false;
  bool a_found = false;
  for (auto pred_id : b_node.preds()) {
    auto &pred_node = G.getNode(pred_id);
    if (pred_node == c_node) {
      c_found = true;
    } else if (pred_node == a_node) {
      a_found = true;
    } else {
      test_assert(false, "Node {B,E,D,F} has bad Pred");
    }
  }
  test_assert(c_found, "Node {B,E,D,F} doesn't have pred C");
  test_assert(a_found, "Node {B,E,D,F} doesn't have pred A");

  test_assert(a_node.preds().size() == 0, "Node A shouldn't have preds");

  bool b_found = false;
  bool g_found = false;
  for (auto pred_id : c_node.preds()) {
    auto &pred_node = G.getNode(pred_id);
    if (pred_node == g_node) {
      b_found = true;
    } else if (pred_node == b_node) {
      g_found = true;
    } else {
    test_assert(false, "Node C has bad Pred");
    }
  }
  test_assert(b_found, "Node C doesn't have pred B");
  test_assert(g_found, "Node C doesn't have pred G");

  return EXIT_SUCCESS;
}

