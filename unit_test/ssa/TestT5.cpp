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
   *       h-------
   *       |      |
   *       V      |
   *       b<--   ||---i
   *      /|  |   ||   |
   *     v V  |   VV   V
   *    d  C--|-->g<---J
   *     \ |  |   ^
   *      VV  |   |
   *       e---   |
   *       |      |
   *       V      |
   *       f-------
   *
   * Note: letter -> id#
   * A->0
   * b->1
   * C->2
   * d->3
   * e->4
   * f->5
   * g->6
   * h->7
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
  auto h = G.addNode<CFG::Node>();
  auto i = G.addNode<CFG::Node>();
  auto j = G.addNode<CFG::Node>();
  auto k = G.addNode<CFG::Node>();

  // Fill in M info
  {
    auto &a_node = G.getNode<CFG::Node>(a);
    auto &c_node = G.getNode<CFG::Node>(c);
    auto &f_node = G.getNode<CFG::Node>(f);
    auto &j_node = G.getNode<CFG::Node>(j);
    auto &k_node = G.getNode<CFG::Node>(k);
    a_node.setM();
    a_node.setR();
    c_node.setM();
    c_node.setR();

    f_node.setR();

    j_node.setR();
    j_node.setM();

    k_node.setR();
    k_node.setM();
  }

  // b's backedges
  G.addPred(b, h);
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

  // g's backedges
  G.addPred(g, c);
  G.addPred(g, f);
  G.addPred(g, h);
  G.addPred(g, i);
  G.addPred(g, j);
  G.addPred(g, k);

  // h's backedges
  G.addPred(h, a);

  // i and J...
  G.addPred(i, j);
  G.addPred(i, k);

  // gimme Gp
  SEG Gp = createGp(G);

  // Then turn that into Xp:
  Gp.createSCC();

  /* NOTE: Gp looks like this:
   *   b
   *  / ^
   * V   \
   * e-->d   g  h
   */
  // Now, create the SCC of Gp:
  //  {b, e, d} are all one node
  //
  //  g  h 

  // Now apply T4 on G
  // NOTE: TestCreateGp has already tested the creation of Gp
  T4(G, Gp);
  // G now looks like this: (tested in TestT4)
  //   A
  //   |
  //   V
  //   h----------
  //   |   ----  ||----|
  //   V   v  |  VV    |
  // {b,e,d}->C<-g<-i<>j
  //   |         ^
  //   V         |
  //   f----------
  //   
  
  // Now, we run T2
  // We expect the output to look like this:
  //   A
  //   |
  //   V
  //   h------------
  //   |     ----  ||----|
  //   V     V  |  VV    |
  // {b,e,d,f}->C<-g<-i<>j
  //        |      ^
  //        --------
  T2(G, Gp);

  // Now, test T6
  T6(G);
  // This should remove g:
  //   A
  //   |
  //   V
  //   h
  //   |     ----
  //   V     V  |
  // {b,e,d,f}->C   i<>J

  // Add successor info to the graph (required by T5)
  std::for_each(std::begin(G), std::end(G),
      [&G] (CFG::ControlFlowGraph::node_iter_type &pnode) {
    auto &preds = pnode->preds();
    auto succ_id = pnode->id();
    std::for_each(std::begin(preds), std::end(preds),
        [&G, &succ_id] (CFG::CFGid pred_id) {
      G.addSucc(pred_id, succ_id);
    });
  });

  T5(G);
  // This should h into bedf:
  //   A
  //   |     ----
  //   V     V  |
  // {h,b,e,d,f}->C  {i,J}
  
  // We're double checking t2 for good measure
  // First, check that the correct nodes were united, and the correct nodes
  // remain distinct
  auto &a_node = G.getNode(a);
  auto &b_node = G.getNode(b);
  auto &c_node = G.getNode(c);
  auto &d_node = G.getNode(d);
  auto &e_node = G.getNode(e);
  auto &f_node = G.getNode(f);
  auto &i_node = G.getNode(i);
  auto &j_node = G.getNode(j);

  test_assert(G.tryGetNode(g) == nullptr, "G node not deleted");

  test_assert(i_node == j_node, "I and J merged");

  // Ensure the b,d,e,f have been merged
  test_assert(b_node == d_node, "B and D not merged");
  test_assert(b_node == e_node, "B and E not merged");
  test_assert(b_node == f_node, "B and F not merged");
  // Also ensure the other nodes were not merged
  test_assert(a_node != b_node, "A and B incorrectly merged");
  test_assert(a_node != c_node, "A and C incorrectly merged");
  test_assert(b_node != c_node, "B and C incorrectly merged");

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
  for (auto pred_id : c_node.preds()) {
    auto &pred_node = G.getNode(pred_id);
    if (pred_node == b_node) {
      b_found = true;
    } else {
    test_assert(false, "Node C has bad Pred");
    }
  }
  test_assert(b_found, "Node C doesn't have pred B");

  bool i_found = false;
  for (auto pred_id : i_node.preds()) {
    auto &pred_node = G.getNode(pred_id);
    if (pred_node == i_node) {
      i_found = true;
    } else {
      test_assert(false, "Node I has bad Pred");
    }
  }
  test_assert(i_found, "Node I doesn't have pred I");

  return EXIT_SUCCESS;
}

