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

  auto &a_node = G.getNode<CFG::Node>(a);
  auto &c_node = G.getNode<CFG::Node>(c);
  auto &f_node = G.getNode<CFG::Node>(f);
  a_node.setM();
  c_node.setM();
  f_node.setM();

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

  // Check the creation of Gp

  // First, verify the nodes that should be dead:
  auto a_null = Gp.tryGetNode(a);
  auto c_null = Gp.tryGetNode(c);
  auto f_null = Gp.tryGetNode(f);
  test_assert(a_null == nullptr, "A was not removed from Gp");
  test_assert(c_null == nullptr, "C was not removed from Gp");
  test_assert(f_null == nullptr, "F was not removed from Gp");

  // Now, make sure that the other nodes are all fine and dandy
  auto b_node = Gp.getNode(b);
  auto d_node = Gp.getNode(d);
  auto e_node = Gp.getNode(e);

  auto b_rep = b_node.id();
  auto d_rep = d_node.id();
  auto e_rep = e_node.id();

  // Verify correct preds
  for (auto pred_id : b_node.preds()) {
    auto ppred_node = Gp.tryGetNode(pred_id);
    if (ppred_node != nullptr) {
      auto pred_rep = ppred_node->id();
      test_assert(pred_rep == e_rep, "Node B has bad Pred");
    }
  }

  for (auto pred_id : d_node.preds()) {
    auto ppred_node = Gp.tryGetNode(pred_id);
    if (ppred_node != nullptr) {
      auto pred_rep = ppred_node->id();
      test_assert(pred_rep == b_rep, "Node D has bad Pred");
    }
  }

  for (auto pred_id : e_node.preds()) {
    auto ppred_node = Gp.tryGetNode(pred_id);
    if (ppred_node != nullptr) {
      auto pred_rep = ppred_node->id();
      test_assert(pred_rep == d_rep, "Node E has bad Pred");
    }
  }

  return EXIT_SUCCESS;
}

