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

#include "llvm/Function.h"
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


template<typename id_type>
struct id_converter_default {
  //{{{
  id_type operator()(id_type in) {
    return in;
  }
  //}}}
};

// Forward decl for graph!
template<typename id_type>
class SEG;

// Enum For llvm RTTI {{{
enum class NodeKind {
  ConstraintNode,
  HUNode,
  Unify,
  SEGNodeGroup,
  SCC,
  CFGNode,
  SCCEnd,
  UnifyEnd
};

enum class EdgeKind {
  Constraint,
  CFGEdge
};
//}}}

template<typename id_type>
class SEGEdge {
  //{{{
 public:
    SEGEdge(EdgeKind kind, id_type src, id_type dest) :
        kind_(kind), src_(src), dest_(dest) { }

    id_type src() const {
      return src_;
    }

    id_type dest() const {
      return dest_;
    }

    // By default print nothing
    virtual void print_label(llvm::raw_ostream &,
        const ObjectMap &) const { }

    EdgeKind getKind() const {
      return kind_;
    }

 protected:
    EdgeKind kind_;

    id_type src_;
    id_type dest_;
  //}}}
};


template<typename id_type>
class SEGNode {
  //{{{
 public:
    // Constructors {{{
    SEGNode(NodeKind kind, int32_t nodenum, id_type id) : kind_(kind),
      nodenum_(nodenum), id_(id) { }

    SEGNode(NodeKind kind, int32_t nodenum, id_type id,
          const SEGNode<id_type> &n) :
        SEGNode(kind, nodenum, id, n, id_converter_default<id_type>()) { }

    // Transforms from one node type to another.
    template<typename old_id_type, typename id_converter>
    SEGNode(NodeKind kind, int32_t nodenum, id_type id,
          const SEGNode<old_id_type> &n, id_converter convert) :
        kind_(kind), nodenum_(nodenum), id_(id) {
      // Also update preds/succs
      for (auto &old_id : n.preds()) {
        // FIXME: Handle ptr to self?
        id_type new_id = convert(old_id);
        if (new_id != id_) {
          preds_.insert(new_id);
        }
      }

      for (auto &old_id : n.succs()) {
        // FIXME: Handle ptr to self?
        id_type new_id = convert(old_id);
        if (new_id != id_) {
          succs_.insert(new_id);
        }
      }
    }

    SEGNode(const SEGNode &) = default;
    SEGNode(SEGNode &&) = default;

    SEGNode &operator=(const SEGNode &) = default;
    SEGNode &operator=(SEGNode &&) = default;
    //}}}

    // Comparison operators {{{
    bool operator==(const SEGNode &n) {
      return nodenum_ == n.nodenum_;
    }

    bool operator<(const SEGNode &n) {
      return nodenum_ < n.nodenum_;
    }

    friend bool operator<(const std::reference_wrapper<SEGNode> &n1,
        const std::reference_wrapper<SEGNode> &n2) {
      return n1.get().nodenum_ < n2.get().nodenum_;
    }
    //}}}

    // Accessors {{{
    /*
    struct hasher {
      std::size_t operator()(const SEGNode &nd) const {
        return std::hash<int32_t>(nd.id());
      }
    };
    */
    // For llvm RTTI
    NodeKind getKind() const {
      return kind_;
    }

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

    id_type id() const {
      return id_;
    }
    //}}}

    // Modifiers {{{
    void addSucc(id_type id) {
      succs_.insert(id);
    }

    void addPred(id_type id) {
      preds_.insert(id);
    }
    //}}}

    // Dot print support {{{
    virtual void print_label(llvm::raw_ostream &,
        const ObjectMap &) const { }
    //}}}

 private:
    // For dfs traversal
    friend class SEG<id_type>;


    // Private data {{{
    // For llvm RTTI
    const NodeKind kind_;

    // Used to determine the node's unique id
    int nodenum_;

    // The id for this node
    id_type id_;

    // Used for DFS traversal
    int32_t dfsNumPred_ = std::numeric_limits<int32_t>::max();
    int32_t dfsNumSucc_ = std::numeric_limits<int32_t>::max();
    //}}}

    // Private helpers {{{
    void calcDFS(SEG<id_type> &graph,
        bool dfs_succ, int32_t dfs,
        std::set<std::reference_wrapper<SEGNode>> &visited);
    //}}}

 protected:
    // Protected data {{{
    // We hold references to our pred and successor nodes
    std::set<id_type> preds_;
    std::set<id_type> succs_;
    //}}}
  //}}}
};

template<typename id_type>
class UnifyNode : public SEGNode<id_type> {
  // {{{
 public:
    // Constructors {{{
    UnifyNode(NodeKind kind, int32_t nodenum, id_type id) :
      SEGNode<id_type>(kind, nodenum, id) {
        reps_.insert(id);
      }

    template <typename old_id_type, typename id_converter>
    UnifyNode(NodeKind kind, int32_t nodenum, id_type id,
          const SEGNode<old_id_type> &n, id_converter convert) :
        SEGNode<id_type>(kind, nodenum, id, n, convert) {
      reps_.insert(convert(n.id()));

      if (auto pold_node = llvm::dyn_cast<UnifyNode<old_id_type>>(&n)) {
        auto &old_node = *pold_node;
        std::for_each(old_node.rep_begin(), old_node.rep_end(),
            [this, &convert](old_id_type old_id) {
          reps_.insert(convert(old_id));
        });
      }
    }

    UnifyNode(const UnifyNode &) = default;
    UnifyNode(UnifyNode &&) = default;

    UnifyNode &operator=(const UnifyNode &) = default;
    UnifyNode &operator=(UnifyNode &&) = default;
    //}}}

    // Actual unite functionality {{{
    virtual void unite(SEGNode<id_type> &n) {
      SEGNode<id_type>::preds().insert(std::begin(n.preds()),
          std::end(n.preds()));
      SEGNode<id_type>::succs().insert(std::begin(n.succs()),
          std::end(n.succs()));

      reps_.insert(n.id());
    }
    //}}}

    // For llvm RTTI {{{
    static bool classof(const SEGNode<id_type> *node) {
      return node->getKind() >= NodeKind::Unify &&
          node->getKind() < NodeKind::UnifyEnd;
    }
    //}}}

    // Iterating the set of united nodes {{{
    typedef typename std::set<id_type>::iterator rep_iterator;
    typedef typename std::set<id_type>::const_iterator const_rep_iterator;

    rep_iterator rep_begin() {
      return std::begin(reps_);
    }

    rep_iterator rep_end() {
      return std::end(reps_);
    }

    const_rep_iterator rep_begin() const {
      return std::begin(reps_);
    }

    const_rep_iterator rep_end() const {
      return std::end(reps_);
    }

    const_rep_iterator rep_cbegin() const {
      return reps_.cbegin();
    }

    const_rep_iterator rep_cend() const {
      return reps_.cend();
    }
    //}}}

 private:
    // Private data for supporting unification {{{
    std::set<id_type> reps_;
    //}}}
  //}}}
};

template<typename id_type>
class SCCNode : public UnifyNode<id_type> {
  //{{{
 public:
    static const int32_t invalidIndex = std::numeric_limits<int32_t>::min();

    // Constructors {{{
    SCCNode(NodeKind kind, int32_t nodenum, id_type id) :
      UnifyNode<id_type>(kind, nodenum, id) { }

    template <typename old_id_type, typename id_converter>
    SCCNode(NodeKind kind, int32_t nodenum, id_type id,
        const SEGNode<old_id_type> &n, id_converter convert) :
      UnifyNode<id_type>(kind, nodenum, id, n, convert) { }


    SCCNode(const SCCNode &) = default;
    SCCNode(SCCNode &&) = default;

    SCCNode &operator=(const SCCNode &) = default;
    SCCNode &operator=(SCCNode &&) = default;
    //}}}

    // Accessors {{{
    bool indexInvalid() {
      return index_ == invalidIndex;
    }

    int32_t index() {
      return index_;
    }

    int32_t lowlink() {
      return lowlink_;
    }

    bool onStack() {
      return onStack_;
    }
    //}}}

    // Modifiers {{{
    void setIndex(int32_t index) {
      index_ = index;
    }

    void setLowlink(int32_t lowlink) {
      lowlink_ = lowlink;
    }

    void setOnStack(bool onStack) {
      onStack_ = onStack;
    }
    //}}}

    // For LLVM RTTI {{{
    static bool classof(const SEGNode<id_type> *node) {
      return node->getKind() >= NodeKind::SCC &&
        node->getKind() < NodeKind::SCCEnd;
    }
    //}}}

 private:
    // Private variables (used for Tarjan's SCC) {{{
    int32_t index_ = invalidIndex;
    int32_t lowlink_ = invalidIndex;
    bool onStack_ = false;
    //}}}
  //}}}
};

template <typename id_type>
class SEG {
  //{{{
 public:
    // Constructors {{{
    // Copy/move {{{
    SEG(const SEG &) = delete;
    SEG(SEG &&) = default;

    SEG &operator=(const SEG &) = delete;
    SEG &operator=(SEG &&) = default;
    //}}}
    //
    //}}}

    // Iterators {{{
    // Typedefs {{{
    /*
    typedef std::unordered_map<id_type, std::unique_ptr<SEGNode<id_type>>, typename SEGNode<id_type>::hasher>  // NOLINT
      NodeMap;
    */
    typedef std::map<id_type, std::unique_ptr<SEGNode<id_type>>>
      NodeMap;
    typedef std::pair<const id_type, std::unique_ptr<SEGNode<id_type>>>
      node_iter_type;
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

    typedef std::map<std::pair<id_type, id_type>, std::unique_ptr<SEGEdge<id_type>>>  // NOLINT
      EdgeMap;
    typedef std::pair<const std::pair<id_type, id_type>, std::unique_ptr<SEGEdge<id_type>>> // NOLINT
      edge_iter_type;
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

    // Edge iteration {{{
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

    // Constructors to transform between two SEGs
    SEG() = default;

    template <typename node_type, typename edge_type>
    SEG<id_type> convert() const;

    template <typename node_type, typename edge_type,
              typename new_id_type, typename id_converter>
    SEG<new_id_type> convert(id_converter id_convert) const;

    // contructs new node of node_type and inserts it into our node list
    template <typename node_type, typename... va_args>
    SEGNode<id_type> &addNode(id_type id, va_args&... args) {
      auto ret = nodes_.emplace(std::piecewise_construct,
          std::forward_as_tuple(id),
          std::forward_as_tuple(
            std::unique_ptr<SEGNode<id_type>>(
              new node_type(nodeNum_.next(), id, args...))));
      // This had better have inserted
      assert(ret.second);

      return *ret.first->second;
    }

    // Adds edge of edge_type between two nodes
    template <typename edge_type, typename... va_args>
    void addEdge(id_type src, id_type dest, va_args&... args) {
      // Ensure that a node exists for each edge point..
      getNode(src);
      getNode(dest);
      edges_.emplace(std::piecewise_construct,
          std::forward_as_tuple(src, dest),
          std::forward_as_tuple(
            std::unique_ptr<SEGEdge<id_type>>(
              new edge_type(src, dest, args...))));
    }

    void removeEdge(std::pair<id_type, id_type> edge_id) {
      edges_.erase(edge_id);

      // Also remove info from node:
      SEGNode<id_type> &src = *nodes_.at(edge_id.first);
      SEGNode<id_type> &dest = *nodes_.at(edge_id.second);

      // Remove the pointer from src
      auto src_it = src.succs().find(edge_id.second);
      assert(src_it != std::end(src.succs()));
      src.succs().erase(src_it);

      // Remove the pointer from dest
      auto dest_it = dest.preds().find(edge_id.first);
      assert(dest_it != std::end(dest.preds()));
      dest.preds().erase(dest_it);
    }

    void removeNode(id_type id) {
      auto &node = getNode(id);

      // Remove all edges to this node
      // We need a temp vecotr, as we can't remove while iterating...
      std::vector<std::pair<id_type, id_type>> remove_edges;

      auto &preds = node.preds();
      std::for_each(std::begin(preds), std::end(preds),
          [&remove_edges, id](id_type pred_id) {
        remove_edges.emplace_back(pred_id, id);
      });

      // Remove all edges from this node
      auto &succs = node.succs();
      std::for_each(std::begin(succs), std::end(succs),
          [&remove_edges, id](id_type succ_id) {
        remove_edges.emplace_back(id, succ_id);
      });

      for (auto &edge : remove_edges) {
        removeEdge(edge);
      }

      // Delete the node
      nodes_.erase(id);

      // Need to recalcualte DFS info
      haveDFSPred_ = false;
      haveDFSSucc_ = false;
    }
    //}}}

    // Accessors {{{

    // Gets the node, or creates it if it doesn't exist.  Creation uses the
    // default constructor for the node type
    template<typename node_type>
    SEGNode<id_type> &getOrCreateNode(id_type id);

    // Finds a node (allows the node not to exist)
    const_node_iterator findNode(id_type id) const {
      return nodes_.find(id);
    }

    // Gets the node
    SEGNode<id_type> &getNode(id_type id) {
      return *nodes_.at(id);
    }

    const SEGNode<id_type> &getNode(id_type id) const {
      return *nodes_.at(id);
    }

    const SEGEdge<id_type> &getEdge(std::pair<id_type, id_type> &ids) const {
      return *edges_.at(ids);
    }

    const_edge_iterator findEdge(std::pair<id_type, id_type> &id) const {
      return edges_.find(id);
    }

    void createSCC();
    //}}}

    // Debug functions {{{
    void printDotFile(const std::string &filename,
        const ObjectMap &omap) const {
      std::ofstream ostm(filename, std::ofstream::out);
      llvm::raw_os_ostream ofil(ostm);
      printDotHeader(ofil);
      std::for_each(begin(), end(),
          [&ofil, &omap]
          (const node_iter_type &pr) {
        const SEGNode<id_type> &n = *pr.second;
        std::string idNode = idToString(n.id());

        ofil << "  " << idNode << " [label=\"";
        n.print_label(ofil, omap);
        ofil << "\"" << " shape=box" << "];\n";
      });

      std::for_each(edges_begin(), edges_end(),
          [&ofil, &omap]
          (const edge_iter_type &pr) {
        std::string idNode1 = idToString(pr.first.first);
        std::string idNode2 = idToString(pr.first.second);

        ofil << "  " << idNode1 << " -> " << idNode2 <<
          " [label=\"";
        pr.second->print_label(ofil, omap);
        ofil << "\"];\n";
      });
      printDotFooter(ofil);
    }
    //}}}

 private:
    // Private variables {{{
    // Holds all of the nodes
    NodeMap nodes_;

    // Used to determine dfs orderings
    std::vector<id_type> dfsPred_;
    std::vector<id_type> dfsSucc_;

    // Holds edge data
    EdgeMap edges_;

    std::function<SEGNode<id_type> *(uint32_t, id_type)> nodeAlloc_;

    // Required for dfs (dfs is calculated on visit)
    bool haveDFSPred_ = false;
    bool haveDFSSucc_ = false;

    UniqueIdentifier<uint32_t> nodeNum_;
    //}}}

    // Private helpers {{{
    std::unique_ptr<SEGNode<id_type>> *allocNode(id_type id) {
      return std::unique_ptr<SEGNode<id_type>>(allocNode_(nodeNum_.next(), id));
    }

    std::unique_ptr<SEGEdge<id_type>> *allocEdge() {
      return std::unique_ptr<SEGEdge<id_type>>(allocEdge_(this));
    }

    void fillDFSPred();
    void fillDFSSucc();
    // Tarjan's SCC algorithm to detect strongly connected components
    void sccStrongconnect(SCCNode<id_type> &nd, int &index,
        std::stack<std::reference_wrapper<SCCNode<id_type>>> &st,
        SEG &ret) const;
    //}}}
  //}}}
};

// SEG Impl {{{
// Node impl {{{
// Visit helper {{{
template <typename id_type>
void SEGNode<id_type>::calcDFS(
    SEG<id_type> &graph, bool dfs_succ,
    int32_t dfs, std::set<std::reference_wrapper<SEGNode<id_type>>> &visited) {
  // Also do dfs bookkeeping while we're at it
  auto &dfsNum = dfs_succ ? dfsNumSucc_ : dfsNumPred_;


  if (dfsNum < dfs) {
    dfsNum = dfs;

    visited.insert(*this);

    auto &next = dfs_succ ? succs() : preds();

    for (id_type node_id : next) {
      SEGNode &node = graph.getNode(node_id);
      // Only visit a node we haven't already visited
      if (visited.count(node) == 0) {
        node.calcDFS(graph, dfs_succ, dfs+1, visited);
      }
    }
  }
}
//}}}
//}}}

// SEG converters {{{
template <typename id_type>
template <typename node_type, typename edge_type>
SEG<id_type> SEG<id_type>::convert() const {
  return convert<node_type, edge_type, id_type>
    (id_converter_default<id_type>());
}

template <typename id_type>
template <typename node_type, typename edge_type,
         typename new_id_type, typename id_converter>
SEG<new_id_type> SEG<id_type>::convert(id_converter id_convert) const {
  SEG<new_id_type> ret;

  std::for_each(cbegin(), cend(),
      [this, &id_convert, &ret]
      (const node_iter_type &pr) {
    new_id_type new_id = id_convert(pr.first);
    auto node_it = ret.findNode(new_id);

    // If this is a new id
    if (node_it == std::end(ret)) {
      ret.addNode<node_type>(new_id, *pr.second, id_convert);
    // Otherwise, this id has been merged
    } else {
      // ???
      SEGNode<new_id_type> &nd = *node_it->second;
      assert(llvm::isa<UnifyNode<new_id_type>>(nd));
      node_type tmp_node(nodeNum_.invalid(), new_id,
        *pr.second, id_convert);

      llvm::cast<UnifyNode<new_id_type>>(nd).unite(tmp_node);
    }
  });

  std::for_each(edges_cbegin(), edges_cend(),
      [this, &id_convert, &ret]
      (const edge_iter_type &pr) {
    std::pair<new_id_type, new_id_type> new_id =
        std::make_pair(id_convert(pr.first.first), id_convert(pr.first.second));
    auto edge_it = ret.findEdge(new_id);

    if (edge_it == ret.edges_cend()) {
      ret.addEdge<edge_type>(new_id.first, new_id.second,
        *pr.second, ret, id_convert);
    } else {
      // ??? Ignore duplicate edges?
      llvm::dbgs() << "WARNING: Ignoring duplicate edge!!!\n";
    }
  });

  return std::move(ret);
}
//}}}

// Private helpers {{{
template <typename id_type>
template <typename node_type>
SEGNode<id_type> &
SEG<id_type>::getOrCreateNode(id_type id) {
  auto it = nodes_.find(id);

  if (it == std::end(nodes_)) {
    return addNode(id);
  } else {
    return it->second;
  }
}

// Visit functions {{{
// Use Tarjan's method to calculate SCCs for this graph
template <typename id_type>
void SEG<id_type>::sccStrongconnect(
    SCCNode<id_type> &nd, int &index,
    std::stack<std::reference_wrapper<SCCNode<id_type>>> &st,
    SEG &ret) const {
  nd.setIndex(index);
  nd.setLowlink(index);
  index++;

  st.push(nd);
  nd.setOnStack(true);

  for (id_type succ_id : nd.succs()) {
    auto &succ = llvm::cast<SCCNode<id_type>>(ret.getNode(succ_id));
    if (succ.index() == nd.indexInvalid()) {
      sccStrongconnect(succ, index, st, ret);
      nd.setLowlink(std::min(nd.lowlink(), succ.lowlink()));
    } else if (succ.onStack()) {
      nd.setLowlink(std::min(nd.lowlink(), succ.index()));
    }
  }

  // If nd is a root node
  if (nd.lowlink() == nd.index()) {
    // Copy nd into scc, as our scc root
    SCCNode<id_type> &rep = nd;

    while (true) {
      SCCNode<id_type> &grp = st.top();
      st.pop();

      // Unite all of the SCCs with the one we just made
      rep.unite(grp);

      if (grp == nd) {
        break;
      }
    }
  }
}

template <typename id_type>
void SEG<id_type>::createSCC() {
  int index = 0;

  std::stack<std::reference_wrapper<SCCNode<id_type>>> st;

  std::for_each(begin(), end(),
      [this, &index, &st]
      (node_iter_type &pr) {
    auto &nd = llvm::cast<SCCNode<id_type>>(*pr.second);
    sccStrongconnect(nd, index, st, *this);
  });
}

// Calculate a valid DFS traversal order
template <typename id_type>
void SEG<id_type>::fillDFSSucc() {
  // Okay, visit each node w/ dfs info
  std::for_each(begin(), end(),
      [this] (node_iter_type &pr) {
    std::set<std::reference_wrapper<SEGNode<id_type>>> visited;
    auto &node = *pr.second;
    node.calcDFS(*this, true, 0, visited);
  });

  // Fill out our dfs traversal list, based on the node numbers
  // dfsSucc_.insert(begin(), end());
  for (auto &pair : *this) {
    dfsSucc_.push_back(pair.second->id());
  }
  std::sort(std::begin(dfsSucc_), std::end(dfsSucc_),
    [this] (id_type id1, id_type id2) -> bool {
      const SEGNode<id_type> &n1 = getNode(id1);
      const SEGNode<id_type> &n2 = getNode(id2);
      return n1.dfsNumSucc_ < n2.dfsNumSucc_;
    });
  haveDFSSucc_ = true;
}

template <typename id_type>
void SEG<id_type>::fillDFSPred() {
  // Okay, visit each node w/ dfs info
  std::for_each(begin(), end(),
      [this] (node_iter_type &pr) {
    std::set<std::reference_wrapper<SEGNode<id_type>>> visited;
    auto &node = *pr.second;
    node.calcDFS(*this, false, 0, visited);
  });

  // Fill out our dfs traversal list, based on the node numbers
  // dfsPred_.insert(begin(), end());
  for (auto &pair : *this) {
    dfsPred_.push_back(pair.second->id());
  }

  std::sort(std::begin(dfsPred_), std::end(dfsPred_),
    [this] (id_type id1, id_type id2) -> bool {
      const SEGNode<id_type> &n1 = getNode(id1);
      const SEGNode<id_type> &n2 = getNode(id2);
      return n1.dfsNumPred_ < n2.dfsNumPred_;
    });
  haveDFSPred_ = true;
}
//}}}
//}}}
//}}}

#endif  // INCLUDE_SEG_H_
