/*
 * Copyright (C) 2015 David Devecsery
 */
#ifndef INCLUDE_RUNTARJANS_H_
#define INCLUDE_RUNTARJANS_H_

#include <vector>
#include <algorithm>

extern size_t check_val;

template<typename node_type>
class __should_visit_default {
 public:
  bool operator()(const node_type &) const {
    return true;
  }
};

template<typename node_type, typename id_type>
class __scc_visit_default {
 public:
  void operator()(const node_type &, id_type) const {
  }
};

// NOTE: a topo order can be achieved by visiting each node on post_unite
template<typename Graph, typename scc_visit,
  typename should_visit>
class DoRunTarjans {
//{{{
 public:
  static const int32_t IndexInvalid = -1;
  typedef typename Graph::Id Id;
  typedef typename Graph::Node Node;

  DoRunTarjans(Graph &G,
      scc_visit do_scc_visit, should_visit do_visit) :
      should_visit_(do_visit), scc_visit_(do_scc_visit),
      graph_(G), nodeData_(G.size()) {
    for (Id id(0); id < Id(G.size()); id++) {
      // Only consider reps
      if (G.getRep(id) != id) {
        continue;
      }

      auto &node = G.getNode(id);
      auto &node_data = getData(id);
      // If this is both a unvisited node, and we should visit it
      if (node_data.index == IndexInvalid && should_visit_(node)) {
        tarjan_visit(node, id);
      }
    }
  }

 private:
  struct TarjanData {
    int32_t index = IndexInvalid;
    int32_t lowlink = IndexInvalid;
    bool onStack = false;
  };

  struct TarjanData &getData(Id id) {
    assert(id != Id::invalid());
    assert(id.val() >= 0);
    assert(static_cast<size_t>(id.val()) < nodeData_.size());
    return nodeData_.at(id.val());
  }

  void tarjan_visit(Node &node, Id node_id) {
    auto &node_data = getData(node_id);
    assert(!node_data.onStack);
    assert(node_data.index == IndexInvalid);
    node_data.index = nextIndex_;
    node_data.lowlink = nextIndex_;
    nextIndex_++;

    nodeStack_.push_back(node_id);
    node_data.onStack = true;

    std::vector<Id> pred_list(std::begin(node.preds()),
        std::end(node.preds()));
    for (auto pred_id : pred_list) {
      auto pred_rep = graph_.getRep(pred_id);
      auto &pred_node = graph_.getNode(pred_rep);

      // If this node should be visited (allows us to exclude some nodes, like
      //   needed in Ramalingam's T4 transform)
      if (should_visit_(pred_node)) {
        auto &pred_data = getData(pred_rep);
        if (pred_data.index == IndexInvalid) {
          tarjan_visit(pred_node, pred_rep);
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
        auto &merge_data = getData(merge_id);
        merge_data.onStack = false;

        if (merge_id == node_id) {
          break;
        }

        // node.unite(seg_, merge_node);
        graph_.merge(merge_id, node_id);

        if (static_cast<size_t>(merge_id) == check_val ||
            static_cast<size_t>(node_id) == check_val) {
          llvm::dbgs() << "  tarjan merge: " << merge_id << " and "
              << node_id << "\n";
        }

        // Must re-get node, as we just merged...
        // scc_visit_(graph_.getNode(merge_id), merge_id);
      }

      // Must re-get node, as we just merged...
      scc_visit_(graph_.getNode(node_id), node_id);
    }
  }

  // Visit fcns...
  should_visit &should_visit_;
  scc_visit &scc_visit_;

  Graph &graph_;

  int32_t nextIndex_ = 0;
  std::vector<Id> nodeStack_;
  std::vector<TarjanData> nodeData_;
  //}}}
};

template <typename Graph,
         typename scc_visit = __scc_visit_default<typename Graph::Node,
             typename Graph::Id>,
         typename should_visit = __should_visit_default<typename Graph::Node>>
void run_tarjans(Graph &g,
    scc_visit &scc,
    should_visit &should) {
  DoRunTarjans<Graph, scc_visit, should_visit> X(g, scc, should);
}

template <typename Graph,
         typename scc_visit = __scc_visit_default<typename Graph::Node,
             typename Graph::Id>,
         typename should_visit = __should_visit_default<typename Graph::Node>>
void run_tarjans(Graph &g,
    scc_visit &scc) {
  DoRunTarjans<Graph, scc_visit, should_visit> X(g, scc, should_visit());
}

template <typename Graph,
         typename scc_visit = __scc_visit_default<typename Graph::Node,
             typename Graph::Id>,
         typename should_visit = __should_visit_default<typename Graph::Node>>
void run_tarjans(Graph &g) {
  DoRunTarjans<Graph, scc_visit, should_visit> X(g, scc_visit(),
      should_visit());
}

#endif  // INCLUDE_RUNTARJANS_H_
