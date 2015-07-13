/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_SEG_H_
#define INCLUDE_SEG_H_

#include <cstdint>

#include <algorithm>
#include <fstream>
#include <functional>
#include <iostream>
#include <limits>
#include <map>
#include <queue>
#include <set>
#include <stack>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "include/util.h"
#include "include/ObjectMap.h"

#include "llvm/Support/raw_os_ostream.h"

// Static functions used by SEG DOT printing {{{
template<typename idT>
static std::string idToString(idT id) {
  auto val = id.val();

  if (val == 0) {
    return "a";
  }

  int len = 0;

  auto val_bkp = val;
  while (val_bkp != 0) {
    ++len;
    val_bkp /= 10;
  }

  std::string ret(len, 'a');

  for (int i = 0; i < len; i++) {
    char digit = val % 10;
    val /= 10;

    ret.replace(i, 1, 1, 'a' + digit);
  }

  return ret;
}

static void printDotHeader(llvm::raw_ostream &ofil) {
  ofil << "digraph graphname {\n";
}

static void printDotFooter(llvm::raw_ostream &ofil) {
  // We use endl here, so the file will force flush
  ofil << "}" << "\n";
}
//}}}

// Class representing the Sparse Evaluation Graph used for Ramalingams
// (ComputeSSA)
// This class is actually used at several different levels, with different id
// mappings, so its templated to be generic for that (for example with
// ObjID->ObjID in 1:1 mapping, or PEid->ObjID)
struct SEGNodeEmpty {
  void unite(SEGNodeEmpty &) { }
};

template<typename id_type>
class SEGEdgeEmpty {
 public:
    id_type src() const {
      return src_;
    }

    id_type dest() const {
      return dest_;
    }

 private:
    id_type src_;
    id_type dest_;
};

template <typename id_type,
         typename node_data = SEGNodeEmpty,
         typename edge_type = SEGEdgeEmpty<id_type>>
class SEG {
  //{{{
 public:
    class Node {
      //{{{
     public:
        // Constructor
        // With constraint(s?) the node is based off of
        Node(uint32_t nodenum, id_type id);

        template<typename old_node>
        Node(uint32_t nodenum, old_node conversion);

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
        struct hasher {
          std::size_t operator()(const Node &nd) const {
            return std::hash<int32_t>()(nd.nodenum_);
          }
        };

        std::set<id_type> &preds() {
          return preds_;
        }

        const std::set<id_type> &preds() const {
          return preds_;
        }

        std::set<id_type> &succs() {
          return succs_;
        }

        const std::set<id_type> &succs() const {
          return succs_;
        }

        node_data &data() {
          return data_;
        }

        const node_data &data() const {
          return data_;
        }

        id_type id() const {
          return id_;
        }

        const std::set<id_type> &objIds() const {
          return objIds_;
        }
        //}}}

        // Modifiers {{{
        void addSucc(id_type id) {
          succs_.insert(id);
        }

        void addPred(id_type id) {
          preds_.insert(id);
        }

        void addObj(id_type id) {
          objIds_.insert(id);
        }
        //}}}

        // Unite/clone (used for SCC) {{{
        // Unite -- Used with SCC, returns a new node which is the unification
        //   of all of these nodes
        void unite(const Node &n);
        //}}}

        // Dot print support {{{
        void print_label(llvm::raw_ostream &ofil,
            const ObjectMap &omap) const {
          data().print_label(ofil, id(), omap);
        }
        //}}}

     private:
        // For dfs traversal
        friend class SEG<id_type, node_data, edge_type>;

        // Private data {{{
        // Used to determine the node's unique id
        int nodenum_;

        // We hold references to our pred and successor nodes
        std::set<id_type> preds_;
        std::set<id_type> succs_;

        // The id for this node
        id_type id_;

        // Data must be move constructible!
        static_assert(std::is_move_constructible<node_data>::value,
            "The node_data must be move constructible");
        node_data data_;

        // Ids of the nodes represented by this SEGNode
        std::set<id_type> objIds_;

        // Used for DFS traversal
        int32_t dfsNumPred_ = std::numeric_limits<int32_t>::max();
        int32_t dfsNumSucc_ = std::numeric_limits<int32_t>::max();
        //}}}

        // Private helpers {{{
        void calcDFS(SEG<id_type, node_data, edge_type> &graph,
            bool dfs_succ, int32_t dfs,
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

    // Constructors {{{
    SEG() = default;

    // Constructors to transform between two SEGs
    template <typename old_node_data, typename old_edge_type>
    SEG(const SEG<id_type, old_node_data, old_edge_type> &);

    template <typename old_id_type, typename old_node_data, typename
      old_edge_type, typename id_converter>
    SEG(const SEG<old_id_type, old_node_data, old_edge_type> &,
        id_converter &convert);

    // Copy/move {{{
    SEG(const SEG &) = default;
    SEG(SEG &&) = default;

    SEG &operator=(const SEG &) = default;
    SEG &operator=(SEG &&) = default;
    //}}}
    //}}}

    // Iterators {{{
    // Typedefs {{{
    typedef std::unordered_map<id_type, Node, typename id_type::hasher> NodeMap;
    typedef typename NodeMap::iterator node_iterator;
    typedef typename NodeMap::const_iterator
      const_node_iterator;

    typedef typename std::vector<id_type>::iterator
      dfs_iterator;
    typedef typename std::vector<id_type>::const_iterator
      const_dfs_iterator;

    typedef typename std::vector<id_type>::iterator
      scc_iterator;
    typedef typename std::vector<id_type>::const_iterator
      const_scc_iterator;

    typedef std::map<std::pair<id_type, id_type>, edge_type> EdgeMap;
    typedef typename EdgeMap::iterator edge_iterator;
    typedef typename EdgeMap::const_iterator const_edge_iterator;
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

    // Edge34 iteration {{{
    edge_iterator edges_begin() {
      return std::begin(edges_);
    }

    edge_iterator edges_end() {
      return std::end(edges_);
    }

    const_edge_iterator edges_begin() const {
      return std::begin(edges_);
    }

    const_edge_iterator edges_end() const {
      return std::end(edges_);
    }

    const_edge_iterator edges_cbegin() const {
      return edges_.cbegin();
    }

    const_edge_iterator edges_cend() const {
      return edges_.cend();
    }
    //}}}

    //}}}

    // Modifiers {{{
    // Default contructs new node
    Node &createNode(id_type id) {
      auto pr = nodes_.emplace(std::piecewise_construct,
          std::forward_as_tuple(id),
          std::forward_as_tuple(nodeNum_.next(), id));
      // We must have added it
      assert(pr.second);

      return pr.first->second;
    }

    // Adds edge between two nodes
    template <typename... va_args>
    void addEdge(id_type src, id_type dest, va_args&... args) {
      edges_.emplace(std::piecewise_construct,
          std::forward_as_tuple(src, dest),
          std::forward_as_tuple(src, dest, args...));
    }

    void removeEdge(std::pair<id_type, id_type> edge_id) {
      edges_.erase(edge_id);
    }
    //}}}

    // Accessors {{{
    Node &getNode(id_type id) {
      return getOrCreateNode(id);
      // return nodes_.at(id);
    }

    const Node &getNode(id_type id) const {
      return nodes_.at(id);
    }

    const edge_type &getEdge(std::pair<id_type, id_type> &ids) const {
      return edges_.at(ids);
    }

    SEG getSCC() const;
    //}}}

    // Debug functions {{{
    void printDotFile(const std::string &filename,
        const ObjectMap &omap) const {
      std::ofstream ostm(filename, std::ofstream::out);
      llvm::raw_os_ostream ofil(ostm);
      printDotHeader(ofil);
      std::for_each(begin(), end(),
          [&ofil, &omap](const std::pair<const id_type, Node> &pr) {
        const Node &n = pr.second;
        std::string idNode = idToString(n.id());

        ofil << "  " << idNode << " [label=\"";
        n.print_label(ofil, omap);
        ofil << "\"" << " shape=box" << "];\n";
      });

      std::for_each(edges_begin(), edges_end(),
          [&ofil, &omap]
          (const std::pair<const std::pair<id_type, id_type>, edge_type> &pr) {
        std::string idNode1 = idToString(pr.first.first);
        std::string idNode2 = idToString(pr.first.second);

        ofil << "  " << idNode1 << " -> " << idNode2 <<
          " [label=\"";
        pr.second.print_label(ofil, omap);
        ofil << "\"];\n";
      });
      printDotFooter(ofil);
    }
    //}}}

 private:
    // Private variables {{{
    // Holds all of the nodes
    std::unordered_map<id_type, Node, typename id_type::hasher> nodes_;
    // Used to determine dfs orderings
    std::vector<id_type> dfsPred_;
    std::vector<id_type> dfsSucc_;

    // Holds edge data
    std::map<std::pair<id_type, id_type>, edge_type> edges_;

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
    void sccStrongconnect(SCCWrap &nd, int &index,
        std::stack<std::reference_wrapper<SCCWrap>> &st, SEG &ret) const;

    Node &getOrCreateNode(id_type id);
    //}}}
  //}}}
};

// SEG Impl {{{
// Node impl {{{
// Constructor {{{
template <typename id_type, typename node_data, typename edge_type>
SEG<id_type, node_data, edge_type>::Node::Node(
    uint32_t nodenum, id_type id) :
  nodenum_(nodenum), id_(id) { }

template <typename id_type, typename node_data, typename edge_type>
template <typename old_node_type>
SEG<id_type, node_data, edge_type>::Node::Node(
    uint32_t nodenum, old_node_type conversion) :
  nodenum_(nodenum), preds_(conversion.preds()), succs_(conversion.succs()),
  id_(conversion.id()), data_(conversion.data()) { }
  // NOTE: We don't copy objIds_ so we can redo SCCs
//}}}

// Visit helper {{{
template <typename id_type, typename node_data, typename edge_type>
void SEG<id_type, node_data, edge_type>::Node::calcDFS(
    SEG<id_type, node_data, edge_type> &graph, bool dfs_succ,
    int32_t dfs, std::set<std::reference_wrapper<Node>> &visited) {
  // Also do dfs bookkeeping while we're at it
  auto &dfsNum = dfs_succ ? dfsNumSucc_ : dfsNumPred_;


  if (dfsNum < dfs) {
    dfsNum = dfs;

    visited.insert(*this);

    auto &next = dfs_succ ? succs() : preds();

    for (id_type node_id : next) {
      Node &node = graph.getNode(node_id);
      // Only visit a node we haven't already visited
      if (visited.count(node) == 0) {
        node.calcDFS(graph, dfs_succ, dfs+1, visited);
      }
    }
  }
}
//}}}

// SCC Helpers {{{
template <typename id_type, typename node_data, typename edge_type>
void SEG<id_type, node_data, edge_type>::Node::unite(const Node &n) {
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

// SEG Constructors {{{
template <typename id_type, typename node_data, typename edge_type>
template <typename old_node_data, typename old_edge_type>
SEG<id_type, node_data, edge_type>::SEG(
    const SEG<id_type, old_node_data, old_edge_type> &base) {
  typedef SEG<id_type, old_node_data, old_edge_type> base_seg_type;
  typedef typename base_seg_type::Node base_node_type;
  typedef std::pair<const std::pair<id_type, id_type>, old_edge_type>
    pair_iter_type;
  // For each node in their nodes, insert into our nodes
  // Handling the nodenum will be a bit tricky?
  std::for_each(std::begin(base), std::end(base),
      [this](const std::pair<const id_type, base_node_type> &pr) {
    // Okay... now recreate the nodes:
    nodes_.emplace(std::piecewise_construct, std::make_tuple(pr.first),
      std::make_tuple(nodeNum_.next(), pr.second));
  });

  // For each edge in our edges, insert into their edges
  std::for_each(base.edges_begin(), base.edges_end(),
      [this] (const pair_iter_type &pr) {
    edges_.emplace(std::piecewise_construct, std::make_tuple(pr.first),
      std::make_tuple(this, pr.second));
  });
}



//}}}

// Private helpers {{{
template <typename id_type, typename node_data, typename edge_type>
typename SEG<id_type, node_data, edge_type>::Node &
SEG<id_type, node_data, edge_type>::getOrCreateNode(id_type id) {
  auto it = nodes_.find(id);

  if (it == std::end(nodes_)) {
    auto ret = nodes_.emplace(id, Node(nodeNum_.next(), id));
    // This had better have inserted
    assert(ret.second);
    return ret.first->second;
  } else {
    return it->second;
  }
}

// Visit functions {{{
// Use Tarjan's method to calculate SCCs for this graph
template <typename id_type, typename node_data, typename edge_type>
void SEG<id_type, node_data, edge_type>::sccStrongconnect(
    SCCWrap &nd,
    int &index,
    std::stack<std::reference_wrapper<SCCWrap>> &st,
    SEG &ret) const {
  nd.index = index;
  nd.lowlink = index;
  index++;

  st.push(nd);
  nd.onStack = true;

  for (Node &succ : nd.succs()) {
    if (succ.index == nd.indexInvalid()) {
      sccStrongconnect(succ, index, st);
      nd.lowlink = std::min(nd.lowlink, succ.lowlink);
    } else if (succ.onStack) {
      nd.lowlink = std::min(nd.lowlink, succ.index);
    }
  }

  // If nd is a root node
  if (nd.lowlink == nd.index) {
    // Copy nd into scc, as our scc root
    Node &rep = nd.nd;

    while (true) {
      SCCWrap &grp = st.top();
      st.pop();

      // Unite all of the SCCs with the one we just made
      rep.nd.unite(grp.nd);

      if (grp == nd.nd) {
        break;
      }
    }
  }
}

template <typename id_type, typename node_data, typename edge_type>
SEG<id_type, node_data, edge_type>
SEG<id_type, node_data, edge_type>::getSCC() const {
  // Create a clone of "this"?
  SEG ret(*this);

  int index = 0;

  std::stack<std::reference_wrapper<SCCWrap>> st;

  std::for_each(ret.cbegin(), ret.cend(),
      [&index, &st, &ret] (const std::pair<const id_type, const Node> &pr) {
    sccStrongconnect(SCCWrap(pr.second), index, st, ret);
  });
}

// Calculate a valid DFS traversal order
template <typename id_type, typename node_data, typename edge_type>
void SEG<id_type, node_data, edge_type>::fillDFSSucc() {
  // Okay, visit each node w/ dfs info
  std::for_each(begin(), end(),
      [] (std::pair<const id_type, Node> &pr) {
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

template <typename id_type, typename node_data, typename edge_type>
void SEG<id_type, node_data, edge_type>::fillDFSPred() {
  // Okay, visit each node w/ dfs info
  std::for_each(begin(), end(),
      [this] (std::pair<const id_type, Node> &pr) {
    std::set<std::reference_wrapper<Node>> visited;
    Node &node = pr.second;
    node.calcDFS(*this, false, 0, visited);
  });

  // Fill out our dfs traversal list, based on the node numbers
  // dfsPred_.insert(begin(), end());
  for (auto &pair : *this) {
    dfsPred_.push_back(pair.second.id());
  }

  std::sort(std::begin(dfsPred_), std::end(dfsPred_),
    [this] (id_type id1, id_type id2) -> bool {
      Node &n1 = getNode(id1);
      Node &n2 = getNode(id2);
      return n1.dfsNumPred_ < n2.dfsNumPred_;
    });
  haveDFSPred_ = true;
}
//}}}
//}}}
//}}}

#endif  // INCLUDE_SEG_H_
