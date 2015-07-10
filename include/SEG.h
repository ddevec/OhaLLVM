/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_SEG_H_
#define INCLUDE_SEG_H_

#include <cstdint>

#include <algorithm>
#include <functional>
#include <limits>
#include <map>
#include <queue>
#include <set>
#include <stack>
#include <utility>
#include <vector>

#include "include/util.h"
#include "include/DUG.h"


// Class representing the Sparse Evaluation Graph used for Ramalingams
// (ComputeSSA)
// This class is actually used at several different levels, with different id
// mappings, so its templated to be generic for that (for example with
// ObjID->ObjID in 1:1 mapping, or PEid->ObjID)
struct NodeEmpty {
  void unite(NodeEmpty &) { }
};
template <typename srcIdType, typename destIdType,
         typename node_data = NodeEmpty>
class SEG {
  //{{{
 public:
    class Node {
      //{{{
     public:
        // Constructor
        // With constraint(s?) the node is based off of
        Node(uint32_t nodenum, destIdType id);

        // No copy, yes move {{{
        Node(const Node &) = default;
        // Required for emplace...
        Node(Node &&) = default;

        // We don't allow assignment operators, only explicit cloning?
        Node &operator=(const Node &) = delete;
        Node &operator=(Node &&) = default;
        //}}}

        // Equality stuff {{{
        bool operator==(const Node &n) {
          return nodenum_ == n.nodenum_;
        }

        bool operator<(const Node &n) {
          return nodenum_ < n.nodenum_;
        }

        friend bool operator<(const std::reference_wrapper<Node> n1, const
            std::reference_wrapper<Node> n2) {
          return n1.get() < n2.get();
        }
        //}}}

        // Accessors {{{
        std::set<std::reference_wrapper<Node>> &preds() {
          return preds_;
        }

        const std::set<std::reference_wrapper<Node>> &preds() const {
          return preds_;
        }

        std::set<std::reference_wrapper<Node>> &succs() {
          return succs_;
        }

        const std::set<std::reference_wrapper<Node>> &succs() const {
          return succs_;
        }

        node_data &data() {
          return data_;
        }

        const node_data &data() const {
          return data_;
        }

        destIdType id() const {
          return id_;
        }

        const std::set<srcIdType> &objIds() const {
          return objIds_;
        }
        //}}}

        // Modifiers {{{
        void addSucc(Node &n) {
          succs_.insert(n);
        }

        void addPred(Node &n) {
          preds_.insert(n);
        }

        void addObj(srcIdType id) {
          objIds_.insert(id);
        }
        //}}}

        // Unite/clone (used for SCC) {{{
        // Unite -- Used with SCC, returns a new node which is the unification
        //   of all of these nodes
        void unite(const Node &n);
        //}}}

     private:
        // For dfs traversal
        friend class SEG<srcIdType, destIdType, node_data>;

        // Private data {{{
        // Used to determine the node's unique id
        int nodenum_;

        // We hold references to our pred and successor nodes
        std::set<std::reference_wrapper<Node>> preds_;
        std::set<std::reference_wrapper<Node>> succs_;

        // The id for this node
        destIdType id_;

        // Data must be move constructible!
        static_assert(std::is_move_constructible<node_data>::value,
            "The node_data must be move constructible");
        node_data data_;

        // Ids of the nodes represented by this SEGNode
        std::set<srcIdType> objIds_;

        // Used for DFS traversal
        int32_t dfsNumPred_ = std::numeric_limits<int32_t>::max();
        int32_t dfsNumSucc_ = std::numeric_limits<int32_t>::max();
        //}}}

        // Private helpers {{{
        void calcDFS(bool dfs_succ, int32_t dfs,
            std::set<std::reference_wrapper<Node>> &visited);
        //}}}
      //}}}
    };

    // Extra data associated with each node when calculating SCC via Tarjan's
    struct SCCWrap {
      //{{{
      static const int32_t invalidIndex = std::numeric_limits<int32_t>::min();

      explicit SCCWrap(Node &n) : nd(n) { }

      bool operator==(const SCCWrap &wrap) const {
        return wrap.nd == nd;
      }

      bool operator<=(const SCCWrap &wrap) const {
        return wrap.nd <= nd;
      }

      bool indexInvalid() {
        return index == invalidIndex;
      }

      int32_t index = indexInvalid;
      int32_t lowlevel = indexInvalid;
      bool onStack = false;

      const Node &nd;
      //}}}
    };

    // Constructor {{{
    // Inputs:
    //    begin, end -- start/end iterators for a range of ids to add
    //    converter -- Function to convert from the input id type to srcIdType
    //    init_fcn -- Function called when nodes are created, takes Node &
    //    add_node -- Function called when a constraint is added for a node
    //      This function is responsible for updating up node_data for this
    //      constraint, and setting up pred()/succ() of each node, relative to
    //      this constraint
    //        arguments:
    //          InputIter::reference &con
    //          Node &src
    //          Node &dest
    template<typename InputIter, typename objToID,
      typename initializer, typename adder>
    SEG(InputIter st, InputIter en,
        objToID &converter, initializer &init_fcn, adder &add_node);
    //}}}

    // Iterators {{{
    // Typedefs {{{
    typedef typename std::map<destIdType, Node>::iterator node_iterator;
    typedef typename std::map<destIdType, Node>::const_iterator
      const_node_iterator;

    typedef typename std::vector<std::reference_wrapper<Node>>::iterator
      dfs_iterator;
    typedef typename std::vector<std::reference_wrapper<Node>>::const_iterator
      const_dfs_iterator;

    typedef typename std::vector<std::reference_wrapper<Node>>::iterator
      scc_iterator;
    typedef typename std::vector<std::reference_wrapper<Node>>::const_iterator
      const_scc_iterator;
    //}}}

    // Node iteration (pair<id, node>) {{{
    node_iterator begin() {
      return std::begin(nodes_);
    }

    node_iterator end() {
      return std::end(nodes_);
    }

    const_node_iterator begin() const {
      return std::begin(nodes_);
    }

    const_node_iterator end() const {
      return std::end(nodes_);
    }

    const_node_iterator cbegin() const {
      return nodes_.cbegin();
    }

    const_node_iterator cend() const {
      return nodes_.cend();
    }
    //}}}

    // dfs iterators (succ and pred) {{{
    dfs_iterator dfs_succ_begin() {
      if (!haveDFSSucc_) {
        fillDFSSucc();
      }
      return std::begin(dfsSucc_);
    }

    dfs_iterator dfs_succ_end() {
      if (!haveDFSSucc_) {
        fillDFSSucc();
      }
      assert(haveDFSSucc_);
      return std::end(dfsSucc_);
    }

    const_dfs_iterator dfs_succ_begin() const {
      assert(haveDFSSucc_);
      return std::begin(dfsSucc_);
    }

    const_dfs_iterator dfs_succ_end() const {
      assert(haveDFSSucc_);
      return std::end(dfsSucc_);
    }

    const_dfs_iterator dfs_succ_cbegin() const {
      assert(haveDFSSucc_);
      return dfsSucc_.cbegin();
    }

    const_dfs_iterator dfs_succ_cend() const {
      if (!haveDFSSucc_) {
        fillDFSSucc();
      }
      return dfsSucc_.cend();
    }

    dfs_iterator dfs_pred_begin() {
      if (!haveDFSPred_) {
        fillDFSPred();
      }
      return std::begin(dfsPred_);
    }

    dfs_iterator dfs_pred_end() {
      if (!haveDFSPred_) {
        fillDFSPred();
      }
      return std::end(dfsPred_);
    }

    const_dfs_iterator dfs_pred_begin() const {
      assert(haveDFSPred_);
      return std::begin(dfsPred_);
    }

    const_dfs_iterator dfs_pred_end() const {
      assert(haveDFSPred_);
      return std::end(dfsPred_);
    }

    const_dfs_iterator dfs_pred_cbegin() const {
      assert(haveDFSPred_);
      return dfsPred_.cbegin();
    }

    const_dfs_iterator dfs_pred_cend() const {
      assert(haveDFSPred_);
      return dfsPred_.cend();
    }
    //}}}

    // SCC iterators {{{
    scc_iterator scc_begin() {
      if (!haveSCC_) {
        fillSCC();
      }
      return std::begin(SCC_);
    }

    scc_iterator scc_end() {
      if (!haveSCC_) {
        fillSCC();
      }
      return std::end(SCC_);
    }

    const_scc_iterator scc_begin() const {
      assert(haveSCC_);
      return std::begin(SCC_);
    }

    const_scc_iterator scc_end() const {
      assert(haveSCC_);
      return std::end(SCC_);
    }

    const_scc_iterator scc_cbegin() const {
      assert(haveSCC_);
      return SCC_.cbegin();
    }

    const_scc_iterator scc_cend() const {
      assert(haveSCC_);
      return SCC_.cend();
    }
    //}}}
    //}}}

    // Accessors {{{
    Node &getNode(destIdType id) {
      return nodes_[id];
    }

    const Node &getNode(destIdType id) const {
      return nodes_[id];
    }

    Node &getNodeObj(srcIdType id) {
      return objToNode_[id];
    }

    const Node &getNodeObj(srcIdType id) const {
      return objToNode_[id];
    }
    //}}}

 private:
    // Private variables {{{
    // Holds all of the nodes
    std::map<destIdType, Node> nodes_;
    std::map<srcIdType, std::reference_wrapper<Node>> objToNode_;
    std::vector<std::reference_wrapper<Node>> dfsPred_;
    std::vector<std::reference_wrapper<Node>> dfsSucc_;
    std::vector<Node> SCC_;

    // Required for dfs (dfs is calculated on visit)
    bool haveDFSPred_ = false;
    bool haveDFSSucc_ = false;
    bool haveSCC_ = false;

    UniqueIdentifier<uint32_t> nodeNum_;
    //}}}

    // Private helpers {{{
    void fillDFSPred();
    void fillDFSSucc();
    // Tarjan's SCC algorithm to detect strongly connected components
    void fillSCC_strongconnect(SCCWrap &nd, int &index,
        std::stack<std::reference_wrapper<SCCWrap>> &st);
    void fillSCC();

    void addObjMapping(srcIdType src_obj, Node &nd);

    template<typename initializer>
    Node &getOrCreateNode(destIdType id, initializer &init);
    //}}}
  //}}}
};

// Impl helpers {{{
template <typename srcIdType, typename destIdType, typename node_data>
void SEG<srcIdType, destIdType, node_data>::addObjMapping(
    srcIdType src_obj, Node &nd) {
  // This obj key shouldn't be in the mapping, or it should map to this node
  objToNode_.emplace(src_obj, nd);
  nd.addObj(src_obj);
}
//}}}

// SEG Impl {{{
// Node impl {{{
// Constructor {{{

template <typename srcIdType, typename destIdType, typename node_data>
SEG<srcIdType, destIdType, node_data>::Node::Node(
    uint32_t nodenum, destIdType id) :
  nodenum_(nodenum), id_(id) { }
//}}}

// Visit helper {{{
template <typename srcIdType, typename destIdType, typename node_data>
void SEG<srcIdType, destIdType, node_data>::Node::calcDFS(bool dfs_succ,
    int32_t dfs, std::set<std::reference_wrapper<Node>> &visited) {
  // Also do dfs bookkeeping while we're at it
  auto &dfsNum = dfs_succ ? dfsNumSucc_ : dfsNumPred_;


  if (dfsNum < dfs) {
    dfsNum = dfs;

    visited.insert(*this);

    auto &next = dfs_succ ? succs() : preds();

    for (Node &node : next) {
      // Only visit a node we haven't already visited
      if (visited.count(node) == 0) {
        node.calcDFS(dfs_succ, dfs+1, visited);
      }
    }
  }
}
//}}}

// SCC Helpers {{{
template <typename srcIdType, typename destIdType, typename node_data>
void SEG<srcIdType, destIdType, node_data>::Node::unite(const Node &n) {
  // Merge in the preds and successors
  preds().insert(std::begin(n.preds()), std::end(n.preds()));
  succs().insert(std::begin(n.succs()), std::end(n.succs()));

  // Merge in the data
  data().unite(n.data());

  objIds_.insert(std::begin(n.objIds_), std::end(n.objIds_));

  // NOTE: We ignore dfsNumPred_ and dfsNumSucc_ because we've already
  //     collected SCCs...
}
//}}}
//}}}

// Constructor {{{
template <typename srcIdType, typename destIdType, typename node_data>
template<typename InputIter, typename objToID,
  typename initializer, typename adder>
SEG<srcIdType, destIdType, node_data>::SEG(InputIter st, InputIter en,
    objToID &converter, initializer &init_fcn, adder &add_node) {
  // Okay, we visit each node, and call the initializer on it...
  // We also populate our graphs...
  std::for_each(st, en,
      [this, &converter, &init_fcn, &add_node]
      (typename InputIter::reference con) {
    srcIdType src_obj = con.src();
    srcIdType dest_obj = con.dest();

    destIdType src_id = converter(src_obj);
    destIdType dest_id = converter(dest_obj);

    Node &src = getOrCreateNode(src_id, init_fcn);
    Node &dest = getOrCreateNode(dest_id, init_fcn);

    addObjMapping(src_obj, src);
    addObjMapping(dest_obj, dest);

    add_node(con, src, dest);
  });
}
//}}}

// Private helpers {{{
template <typename srcIdType, typename destIdType, typename node_data>
template <typename initializer>
typename SEG<srcIdType, destIdType, node_data>::Node &
SEG<srcIdType, destIdType, node_data>::getOrCreateNode(
    destIdType id, initializer &init) {
  auto it = nodes_.find(id);

  if (it == std::end(nodes_)) {
    auto ret = nodes_.emplace(id, Node(nodeNum_.next(), id));
    // This had better have inserted
    assert(ret.second);
    init(ret.first->second);
    return ret.first->second;
  } else {
    return it->second;
  }
}

// Visit functions {{{
// Use Tarjan's method to calculate SCCs for this graph
template <typename srcIdType, typename destIdType, typename node_data>
void SEG<srcIdType, destIdType, node_data>::fillSCC_strongconnect(
    SCCWrap &nd,
    int &index,
    std::stack<std::reference_wrapper<SCCWrap>> &st) {
  nd.index = index;
  nd.lowlink = index;
  index++;

  st.push(nd);
  nd.onStack = true;

  for (Node &succ : nd.succs()) {
    if (succ.index == nd.indexInvalid()) {
      fillSCC_strongconnect(succ, index, st);
      nd.lowlink = std::min(nd.lowlink, succ.lowlink);
    } else if (succ.onStack) {
      nd.lowlink = std::min(nd.lowlink, succ.index);
    }
  }

  // If nd is a root node
  if (nd.lowlink == nd.index) {
    // Copy nd into scc, as our scc root
    SCC_.emplace_back(nd);
    Node &rep = SCC_.at(SCC_.size()-1);

    while (true) {
      SCCWrap &grp = st.top();
      st.pop();

      // Unite all of the SCCs with the one we just made
      rep.nd.unite(grp.nd);

      if (grp == rep) {
        break;
      }
    }
  }
}

template <typename srcIdType, typename destIdType, typename node_data>
void SEG<srcIdType, destIdType, node_data>::fillSCC() {
  int index = 0;

  std::stack<std::reference_wrapper<SCCWrap>> st;

  std::for_each(cbegin(), cend(),
      [&index, &st] (const std::pair<const srcIdType, const Node> &pr) {
    strongconnect(SCCWrap(pr.second), index, st);
  });
}

// Calculate a valid DFS traversal order
template <typename srcIdType, typename destIdType, typename node_data>
void SEG<srcIdType, destIdType, node_data>::fillDFSSucc() {
  // Okay, visit each node w/ dfs info
  std::for_each(begin(), end(),
      [] (std::pair<const srcIdType, Node> &pr) {
    std::set<std::reference_wrapper<Node>> visited;
    Node &node = pr.second;
    node.calcDFS(true, 0, visited);
  });

  // Fill out our dfs traversal list, based on the node numbers
  // dfsSucc_.insert(begin(), end());
  for (auto &pair : *this) {
    dfsSucc_.push_back(pair.second);
  }
  std::sort(std::begin(dfsSucc_), std::end(dfsSucc_),
    [] (const Node &n1, const Node &n2) {
      n1.dfsNumSucc_ < n2.dfsNumSucc_;
    });
  haveDFSSucc_ = true;
}

template <typename srcIdType, typename destIdType, typename node_data>
void SEG<srcIdType, destIdType, node_data>::fillDFSPred() {
  // Okay, visit each node w/ dfs info
  std::for_each(begin(), end(),
      [] (std::pair<const srcIdType, Node> &pr) {
    std::set<std::reference_wrapper<Node>> visited;
    Node &node = pr.second;
    node.calcDFS(false, 0, visited);
  });

  // Fill out our dfs traversal list, based on the node numbers
  // dfsPred_.insert(begin(), end());
  for (auto &pair : *this) {
    dfsPred_.push_back(pair.second);
  }

  std::sort(std::begin(dfsPred_), std::end(dfsPred_),
    [] (const Node &n1, const Node &n2) -> bool {
      return n1.dfsNumPred_ < n2.dfsNumPred_;
    });
  haveDFSPred_ = true;
}
//}}}
//}}}
//}}}

#endif  // INCLUDE_SEG_H_
