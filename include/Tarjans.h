/*
 * Copyright (C) 2015 David Devecsery
 */
#ifndef __INCLUDE_TARJANS_H
#define __INCLUDE_TARJANS_H

#include <vector>

#include "include/SEG.h"

class should_visit_default {
 public:
  bool operator()(const SEG::Node &) const {
    return true;
  }
};

class scc_visit_default {
 public:
  void operator()(const SEG::Node &) const {
  }
};

// NOTE: a topo order can be achieved by visiting each node on post_unite
template<typename should_visit = should_visit_default,
  typename scc_visit = scc_visit_default>
class RunTarjans {
//{{{
 public:
  static const int32_t IndexInvalid = -1;

  explicit RunTarjans(SEG &G,
      should_visit do_visit = should_visit_default(),
      scc_visit do_scc_visit = scc_visit_default()) :
      should_visit_(do_visit), scc_visit_(do_scc_visit),
      seg_(G), nodeData_(G.getNumNodes()) {
    for (auto &pnode : G) {
      assert(pnode != nullptr);
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
    assert(id.val() >= 0);
    assert(static_cast<size_t>(id.val()) < nodeData_.size());
    return nodeData_.at(id.val());
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

    std::vector<SEG::NodeID> pred_list(std::begin(node.preds()),
        std::end(node.preds()));
    for (auto pred_id : pred_list) {
      auto ppred_node = seg_.tryGetNode(pred_id);
      if (ppred_node == nullptr) {
        continue;
      }

      auto &pred_node = *ppred_node;

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

        /*
        if (node.id().val() == 21438 ||
            merge_node.id().val() == 21438) {
          llvm::dbgs() << "Tarjan Merge: " << node.id() << " <- "
            << merge_node.id() << "\n";
          if (merge_node.id().val() < 200000) {
            llvm::dbgs() << "  node is: " <<
              FullValPrint(ObjectMap::ObjID(merge_node.id().val()))
              << "\n";
          }
        }

        if (node.id().val() == 10223 ||
            merge_node.id().val() == 10223) {
          llvm::dbgs() << "Tarjan Merge: " << node.id() << " <- "
            << merge_node.id() << "\n";
          if (merge_node.id().val() < 200000) {
            llvm::dbgs() << "  node is: " <<
              FullValPrint(ObjectMap::ObjID(merge_node.id().val()))
              << "\n";
          }
        }
        */
        /*
        if (node.id().val() == 13089 ||
            merge_node.id().val() == 13089) {
          llvm::dbgs() << "Tarjan Merge: " << node.id() << " <- "
            << merge_node.id() << "\n";
          if (merge_node.id().val() < 200000) {
            llvm::dbgs() << "  node is: " <<
              FullValPrint(ObjectMap::ObjID(merge_node.id().val()))
              << "\n";
          }
        }
        if (node.id().val() == 210537 ||
            merge_node.id().val() == 210537) {
          llvm::dbgs() << "Tarjan Merge: " << node.id() << " <- "
            << merge_node.id() << "\n";
          if (merge_node.id().val() < 200000) {
            llvm::dbgs() << "  node is: " <<
              FullValPrint(ObjectMap::ObjID(merge_node.id().val()))
              << "\n";
          }
        }
        */
        /*
        if (node.id().val() == 13089 ||
            merge_node.id().val() == 13089) {
          llvm::dbgs() << "Tarjan Merge: " << node.id() << " <- "
            << merge_node.id() << "\n";
          if (merge_node.id().val() < 200000) {
            llvm::dbgs() << "  node is: " <<
              FullValPrint(ObjectMap::ObjID(merge_node.id().val()))
              << "\n";
          }
        }

        if (node.id().val() == 205810 ||
            merge_node.id().val() == 205810) {
          llvm::dbgs() << "Tarjan Merge: " << node.id() << " <- "
            << merge_node.id() << "\n";
        }
        */

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
  //}}}
};

#endif  // __INCLUDE_TARJANS_H
