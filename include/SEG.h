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
#include <utility>
#include <vector>

#include "include/util.h"
#include "include/DUG.h"


// Class representing the Sparse Evaluation Graph used for Ramalingams
// (ComputeSSA)
// This class is actually used at several different levels, with different id
// mappings, so its templated to be generic for that (for example with
// ObjID->ObjID in 1:1 mapping, or PEid->ObjID)
struct NodeEmpty { };
template <typename idType, typename objToID, typename node_data = NodeEmpty>
class SEG {
  //{{{
 public:
    class Node {
      //{{{
     public:
        // Constructor
        // With constraint(s?) the node is based off of
        Node(uint32_t nodenum, idType id);

        // No move/copy {{{
        Node(const Node &) = delete;
        // Required for emplace...
        Node(Node &&) = default;

        Node &operator=(const Node &) = delete;
        Node &operator=(Node &&) = delete;
        //}}}

        // Equality stuff {{{
        bool operator==(const Node &n) {
          return nodenum_ == n.nodenum_;
        }

        bool operator<(const Node &n) {
          return nodenum_ < n.nodenum_;
        }
        //}}}

        // accessors {{{
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

        idType id() const {
          return id_;
        }

        const std::set<DUG::ObjID> &objIds() const {
          return objIds_;
        }

        void addObj(DUG::ObjID id) {
          objIds_.insert(id);
        }
        //}}}

     private:
        // For dfs traversal
        friend class SEG<idType, objToID, node_data>;

        // Private data {{{
        // We hold references to our pred and successor nodes
        std::set<std::reference_wrapper<Node>> preds_;
        std::set<std::reference_wrapper<Node>> succs_;

        // The id for this node
        idType id_;

        // Data must be move constructible!
        static_assert(std::is_move_constructible<node_data>::value,
            "The node_data must be move constructible");
        node_data data_;

        // Ids of the nodes represented by this SEGNode
        std::set<DUG::ObjID> objIds_;

        // Used for DFS traversal
        int32_t dfsNumPred_ = std::numeric_limits<int32_t>::max();
        int32_t dfsNumSucc_ = std::numeric_limits<int32_t>::max();

        // Used to determine the node's unique id
        int nodenum_;
        //}}}

        // Private helpers {{{
        template<typename visit_fcn>
        void visit(visit_fcn &fcn, bool do_dfs, int32_t dfs_num);
        //}}}
      //}}}
    };

    // Constructor
    // Inputs:
    //    id_begin, id_end -- start/end iterators for a range of ids to add
    //    converter -- Function to convert from the input id type to DUG::ObjIDs
    //    graph -- The DUG theses nodes reside in
    //    init_fcn -- Function called when nodes are created, takes Node &
    //    add_node -- Function called when a constraint is added for a node
    //      This function is responsible for updating up node_data for this
    //      constraint, and setting up pred()/succ() of each node, relative to
    //      this constraint
    //        arguments:
    //          Node &src
    //          Node &dest
    //          const Constraint &con
    template<typename initializer, typename adder>
    SEG(objToID &converter, const DUG &graph, initializer &init_fcn,
        adder &add_node);

    // Iterators {{{
    typedef std::vector<Node>::iterator node_iterator;
    typedef std::vector<Node>::const_iterator const_node_iterator;

    typedef std::vector<std::reference_wrapper<Node>>::iterator dfs_iterator;
    typedef std::vector<std::reference_wrapper<Node>>::const_iterator
      const_dfs_iterator;

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

    dfs_iterator dfs_succ_begin() {
      if (!haveDFSSucc) {
        fillDFSSucc();
      }
      return std::begin(dfsSucc_);
    }

    dfs_iterator dfs_succ_end() {
      if (!haveDFSSucc) {
        fillDFSSucc();
      }
      return std::end(dfsSucc_);
    }

    const_dfs_iterator dfs_succ_begin() const {
      if (!haveDFSSucc) {
        fillDFSSucc();
      }
      return std::begin(dfsSucc_);
    }

    const_dfs_iterator dfs_succ_end() const {
      if (!haveDFSSucc) {
        fillDFSSucc();
      }
      return std::end(dfsSucc_);
    }

    const_dfs_iterator dfs_succ_cbegin() const {
      if (!haveDFSSucc) {
        fillDFSSucc();
      }
      return dfsSucc_.cbegin();
    }

    const_dfs_iterator dfs_succ_cend() const {
      if (!haveDFSSucc) {
        fillDFSSucc();
      }
      return dfsSucc_.cend();
    }

    dfs_iterator dfs_pred_begin() {
      if (!haveDFSPred) {
        fillDFSPred();
      }
      return std::begin(dfsPred_);
    }

    dfs_iterator dfs_pred_end() {
      if (!haveDFSPred) {
        fillDFSPred();
      }
      return std::end(dfsPred_);
    }

    const_dfs_iterator dfs_pred_begin() const {
      if (!haveDFSPred) {
        fillDFSPred();
      }
      return std::begin(dfsPred_);
    }

    const_dfs_iterator dfs_pred_end() const {
      if (!haveDFSPred) {
        fillDFSpred();
      }
      return std::end(dfsPred_);
    }

    const_dfs_iterator dfs_pred_cbegin() const {
      if (!haveDFSPred) {
        fillDFSPred();
      }
      return dfsPred_.cbegin();
    }

    const_dfs_iterator dfs_pred_cend() const {
      if (!haveDFSPred) {
        fillDFSpred();
      }
      return dfsPred_.cend();
    }
    //}}}

    // Accessors {{{
    Node &getNode(idType id) {
      return nodes[id];
    }

    const Node &getNode(idType id) const {
      return nodes[id];
    }

    Node &getNode(DUG::ObjID id) {
      return objToNode_[id];
    }

    const Node &getNode(DUG::ObjID id) const {
      return objToNode_[id];
    }
    //}}}

 private:
    // Private variables {{{
    // Holds all of the nodes
    std::map<idType, Node> nodes_;
    std::map<DUG::ObjID, std::reference_wrapper<Node>> objToNode_;
    std::vector<std::reference_wrapper<Node>> dfsPred_;
    std::vector<std::reference_wrapper<Node>> dfsSucc_;

    // Required for dfs (dfs is calculated on visit)
    bool haveDFSPred_ = false;
    bool haveDFSSucc_ = false;

    UniqueIdentifier<uint32_t> nodeNum_;
    //}}}

    // Private helpers {{{
    void fillDFSPred();
    void fillDFSSucc();

    template<typename initializer>
    void getOrCreateNode(typeID id, initializer &init);
    //}}}
  //}}}
};

// Impl helpers {{{
template <typename typeID, typename o, typename n>
void addObjMapping(
    std::map<DUG::ObjID, std::reference_wrapper<SEG<typeID, o, n>::Node>> &mp,
    DUG::ObjID src_obj,
    SEG::<typeId, o, n>::Node &nd) {
  // This obj key shouldn't be in the mapping, or it should map to this node
  assert((auto it = mp.find(src_obj) == std::end(mp)) || it->second == nd);
  mp.insert(std::make_pair(obj, nd));
  nd.addObj(obj);
}
//}}}

// SEG Impl {{{
// Node impl {{{
// Constructor {{{
Node(uint32_t nodenum, idType id) :
  nodenum_(nodenum), id_(id) { }
//}}}

// Visit helper {{{
template <typename idType, typename objToID, typename node_data>
void SEG<idType, objToID, node_data>::Node::calcDFS(bool dfs_succ,
    int32_t dfs, std::set(std::reference_wrapper<Node>> &visited) {
  // Also do dfs bookkeeping while we're at it
  auto &dfsNum = dfs_succ ? dfsNumSucc_ : dfsNumPred_;


  if (dfsNum < dfs) {
    dfsNum = dfs;

    visited.insert(*this);

    auto &next = dfs_succ ? succ() : preds();

    for (auto node : next) {
      // Only visit a node we haven't already visited
      if (visited.count(node) == 0) {
        node.calcDFS(succ, dfs+1, visited);
      }
    }
  }
}
//}}}
//}}}

// Constructor {{{
template <typename idType, typename objToID, typename node_data>
template<typename initializer, typename adder>
SEG<idType, objToID, node_data>::SEG(objToID &converter,
    const DUG &graph, initializer &init_fcn, adder &add_node) {
  // Okay, we visit each node, and call the initializer on it...
  // We also populate our graphs...
  std::for_each(graph.constraints_cbegin(), graph.constraints_cend(),
      [this, &converter, &graph, &init_fcn](const Constraint &con) {
    // Okay
    DUG::ObjID src_obj = con.src();
    DUG::ObjID dest_obj = con.dest();
    idType src_id = converter(src);
    idType dst_id = converter(src);

    Node &src = getOrCreateNode(id, initializer);
    Node &dest = getOrCreateNode(id, initializer);

    addObjMapping(objToNode_, src_obj, src);
    addObjMapping(objToNode_, dest_obj, dest);

    add_node(con, src, dest);
  });
}
//}}}

// Private helpers {{{
template <typename idType, typename objToID, typename node_data>
template <typename initializer>
SEG<idType, objToID, node_data>::Node &
SEG<idType, objToID, node_data>::getOrCreateNode(idType id, initializer &init) {
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
template <typename idType, typename objToID, typename node_data>
void SEG<idType, objToID, node_data>::fillDFSSucc() {
  // Okay, visit each node w/ dfs info
  std::for_each(begin(), end(),
      [] (Node &n) {
    std::set<std::reference_wrapper<Node>> visited;
    n.calcDFS(true, 0, visited);
  });

  // Fill out our dfs traversal list, based on the node numbers
  dfsSucc_.insert(begin(), end());
  std::sort(std::begin(dfsSucc_), std::end(dfsSucc_),
    [] (const Node &n1, const Node &n2) {
      n1.dfsNumSucc_ < n2.dfsNumSucc_;
    });
  haveDFSSucc_ = true;
}

template <typename idType, typename objToID, typename node_data>
void SEG<idType, objToID, node_data>::fillDFSPred() {
  // Okay, visit each node w/ dfs info
  std::for_each(begin(), end(),
      [] (Node &n) {
    std::set<std::reference_wrapper<Node>> visited;
    n.calcDFS(false, 0, visited);
  });

  // Fill out our dfs traversal list, based on the node numbers
  dfsPred_.insert(begin(), end());
  std::sort(std::begin(dfsPred_), std::end(dfsPred_),
    [] (const Node &n1, const Node &n2) {
      n1.dfsNumPred_ < n2.dfsNumPred_;
    });
  haveDFSPred_ = true;
}
//}}}
//}}}
//}}}


/* -- Specialization for Ramalingam's, needs to go in those nodes
        bool p() const {
          return p_;
        }

        bool m() const {
          return !p_;
        }

        bool r() const {
          return r_;
        }

        bool u() const {
          return !r_;
        }

        bool c() const {
          return c_;
        }

        // Private variables {{{
        // To identify p/m nodes (see computeSSA comments)
        bool p_;
        // To identify r/u nodes (see computeSSA comments)
        bool r_;
        // To identify constant nodes (see computeSSA comments)
        bool c_;
*/
#endif  // INCLUDE_SEG_H_