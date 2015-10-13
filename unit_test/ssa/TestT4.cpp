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
   *    d  C  |
   *     \ |  |
   *      VV  |
   *       e---
   *       |
   *       V
   *       F
   *
   * Note: letter -> id#
   * A->0
   * b->1
   * C->2
   * d->3
   * e->4
   * F->5
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

  // Fill in M info
  {
    auto &a_node = G.getNode<CFG::Node>(a);
    auto &c_node = G.getNode<CFG::Node>(c);
    a_node.setM();
    c_node.setM();
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

  // gimme Gp
  SEG Gp = createGp(G);

  // Then turn that into Xp:
  Gp.createSCC();

  /* NOTE: Gp looks like this:
   *   b
   *  / ^
   * V   \
   * e-->d
   */
  // Now, create the SCC of Gp:
  //  {b, e, d} are all one node

  // Now apply T4 on G
  // NOTE: TestCreateGp has already tested the creation of Gp
  T4(G, Gp);

  // Now, verify Gp is valid:
  // We expect a graph that looks like this:
  //   A
  //   |   ----
  //   V   v  |
  // {b,e,d}->C
  //   |
  //   V
  //   F
  //   
  
  
  // First, check that the correct nodes were united, and the correct nodes
  // remain distinct
  auto &a_node = G.getNode(a);
  auto &b_node = G.getNode(b);
  auto &c_node = G.getNode(c);
  auto &d_node = G.getNode(d);
  auto &e_node = G.getNode(e);
  auto &f_node = G.getNode(f);

  // Ensure the bde have been merged
  test_assert(b_node == d_node, "B and D not merged");
  test_assert(d_node == e_node, "D and E not merged");
  // Also ensure the other nodes were not merged
  test_assert(a_node != b_node, "B and A incorrectly merged");
  test_assert(a_node != c_node, "B and A incorrectly merged");
  test_assert(a_node != f_node, "B and A incorrectly merged");
  test_assert(b_node != c_node, "B and A incorrectly merged");
  test_assert(b_node != f_node, "B and A incorrectly merged");

  // Now, check the edges:
  // Verify correct preds
  for (auto pred_id : b_node.preds()) {
    auto &pred_node = G.getNode(pred_id);
    test_assert(pred_node == a_node ||
        pred_node == c_node, "Node {B,E,D} has bad Pred");
  }

  test_assert(a_node.preds().size() == 0, "Node A shouldn't have preds");

  for (auto pred_id : c_node.preds()) {
    auto &pred_node = G.getNode(pred_id);
    test_assert(pred_node == b_node, "Node C has bad Pred");
  }

  for (auto pred_id : f_node.preds()) {
    auto &pred_node = G.getNode(pred_id);
    test_assert(pred_node == b_node, "Node E has bad Pred");
  }

  return EXIT_SUCCESS;
}

