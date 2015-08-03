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
#include <iterator>
#include <limits>
#include <list>
#include <map>
#include <memory>
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
  DUGNode,
  AllocNode,
  LoadNode,
  StoreNode,
  CopyNode,
  PhiNode,
  DUGNodeEnd,
  Unify,
  HUNode,
  ConstraintNode,
  SCC,
  CFGNode,
  SCCEnd,
  UnifyEnd
};

enum class EdgeKind {
  Constraint,
  DUG,
  CFGEdge,
  HUEdge
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

    static bool classof(const SEGEdge<id_type> *) {
      return true;
    }

    void retarget(std::pair<id_type, id_type> &new_edge) {
      src_ = new_edge.first;
      dest_ = new_edge.second;
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

    // LLVM RTTI support {{{
    static bool classof(const SEGNode<id_type> *) {
      return true;
    }
    //}}}

    // Modifiers {{{
    void addSucc(id_type id) {
      succs_.insert(id);
    }

    void addPred(id_type id) {
      preds_.insert(id);
    }

    // Merges two nodes together, called on convert when two old_id's convert
    // into a single new_id
    virtual void merge(const SEGNode<id_type> &nd) {
      auto &succs = nd.succs();
      auto &preds = nd.preds();
      succs_.insert(std::begin(succs), std::end(succs));
      preds_.insert(std::begin(preds), std::end(preds));
    }
    //}}}

    // Dot print support {{{
    virtual void print_label(llvm::raw_ostream &,
        const ObjectMap &) const { }
    //}}}

 private:
    // Private data {{{
    // For llvm RTTI
    const NodeKind kind_;

    // Used to determine the node's unique id
    int nodenum_;

    // The id for this node
    id_type id_;
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
    virtual void unite(SEG<id_type> &graph, SEGNode<id_type> &n) {
      // Retarget all edges pointing towards n
      std::vector<id_type> preds(std::begin(n.preds()), std::end(n.preds()));
      std::for_each(std::begin(preds), std::end(preds),
          [this, &graph, &n](id_type pred_id) {
        auto old_id = std::make_pair(pred_id, n.id());
        auto new_id = std::make_pair(pred_id, SEGNode<id_type>::id());

        // properly handle ptr to self
        if (pred_id == n.id()) {
          new_id.first = new_id.second;
        }
        // If the old edge wasn't a pointer to self, and the new edge is a
        // pointer to self, don't retarget it, just remove it
        if (old_id.first != old_id.second && new_id.first == new_id.second) {
          graph.removeEdge(old_id);
        } else {
          graph.retargetEdge(old_id, new_id);
        }
      });

      // And all edges from n
      std::vector<id_type> succs(std::begin(n.succs()), std::end(n.succs()));
      std::for_each(std::begin(succs), std::end(succs),
          [this, &graph, &n](id_type succ_id) {
        auto old_id = std::make_pair(n.id(), succ_id);
        auto new_id = std::make_pair(SEGNode<id_type>::id(), succ_id);

        // If the old edge wasn't a pointer to self, and the new edge is a
        // pointer to self, don't retarget it, just remove it
        if (old_id.first != old_id.second && new_id.first == new_id.second) {
          graph.removeEdge(old_id);
        } else {
          graph.retargetEdge(old_id, new_id);
        }
      });

      // Also replace the graph's index to n with our pointer
      if (auto pun = llvm::dyn_cast<UnifyNode<id_type>>(&n)) {
        auto &un = *pun;

        std::vector<id_type> rep(un.rep_begin(), un.rep_end());
        std::for_each(std::begin(rep), std::end(rep),
            [this, &graph](id_type rep_id) {
          graph.retargetId(rep_id, SEGNode<id_type>::id());

          // Add all rep ids to our "reps"
          reps_.insert(rep_id);
        });
      } else {
        graph.retargetId(n.id(), SEGNode<id_type>::id());
        // Add n.id to our "reps"
        reps_.insert(n.id());
      }
    }
    //}}}

    // merge functionality {{{
    void merge(const SEGNode<id_type> &nd) override {
      if (auto pun = llvm::dyn_cast<UnifyNode<id_type>>(&nd)) {
        auto &un = *pun;

        reps_.insert(un.rep_begin(), un.rep_end());
      }
      SEGNode<id_type>::merge(nd);
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

    void unite(SEG<id_type> &graph, SEGNode<id_type> &node) override {
      // Just forward... we've already computed SCC, or our data is invalid
      //   anyway
      UnifyNode<id_type>::unite(graph, node);
    }

    // merge functionality
    void merge(const SEGNode<id_type> &nd) override {
      UnifyNode<id_type>::merge(nd);
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
    typedef std::unordered_map<id_type, std::shared_ptr<SEGNode<id_type>>, typename SEGNode<id_type>::hasher>  // NOLINT
      NodeMap;
    */
    typedef std::map<id_type, std::shared_ptr<SEGNode<id_type>>>
      NodeMap;
    typedef std::pair<const id_type, std::shared_ptr<SEGNode<id_type>>>
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

    // Iterator Types {{{
    class topo_iterator {
      //{{{
     public:
        // Stuff to make it stl compatible {{{
        typedef std::bidirectional_iterator_tag iterator_category;
        typedef typename std::list<id_type>::value_type value_type;
        typedef typename std::list<id_type>::difference_type difference_type;
        typedef typename std::list<id_type>::pointer pointer;
        typedef typename std::list<id_type>::reference reference;
        //}}}

        // Constructors {{{
        // No arguments returns end()
        topo_iterator() = default;

        topo_iterator(const topo_iterator &) = default;
        topo_iterator(topo_iterator &&) = default;

        topo_iterator &operator=(const topo_iterator &) = default;
        topo_iterator &operator=(topo_iterator &&) = default;

        // With node, does reverse topo iteration for the node
        topo_iterator(const SEG<id_type> &graph, id_type start_node,
              bool reverse = false) :
            end_(false), begin_(true),
            L_(std::make_shared<std::list<id_type>>()) {
          std::set<id_type> mark;

          // Generate L
          auto &nd = graph.getNode(start_node);
          visit(graph, mark, nd, reverse);

          if (std::begin(*L_) == std::end(*L_)) {
            end_ = true;
            begin_ = false;
          }
          itr_ = std::begin(*L_);
        }

        // Without a node does iteration for the graph
        explicit topo_iterator(const SEG<id_type> &graph,
              bool reverse = false) :
            end_(false),
            begin_(true),
            L_(std::make_shared<std::list<id_type>>()) {
          std::set<id_type> mark;
          // llvm::dbgs() << "topo iterator create\n";

          std::for_each(std::begin(graph), std::end(graph),
              [this, &graph, &mark, reverse] (const node_iter_type &pr) {
            auto &node = *pr.second;
            visit(graph, mark, node, reverse, true);
          });

          /* NOTE: This assertion doesn't work, because nodes can be
           *    unified, and multieple G entries may point towards the same
           *    Node, which should only be visited once on a topological
           *    traversal
          llvm::dbgs() << "topo size is: " << L_->size() << "\n";
          llvm::dbgs() << "graph size is: " << graph.getNumNodes() << "\n";
          assert(L_->size() == graph.getNumNodes());
          */
          if (std::begin(*L_) == std::end(*L_)) {
            end_ = true;
            begin_ = false;
          }
          itr_ = std::begin(*L_);
        }
        //}}}

        // accessors {{{
        bool operator==(const topo_iterator &it) const {
          if (begin_ || it.begin_) {
            if (begin_ && it.begin_) {
              return true;
            }
            return false;
          }

          if (end_ || it.end_) {
            if (end_ && it.end_) {
              return true;
            }
            return false;
          }

          return (itr_ == it.itr_);
        }
        bool operator!=(const topo_iterator &it) const {
          return !operator==(it);
        }

        id_type operator*() const {
          return itr_.operator*();
        }

        id_type operator->() const {
          return itr_.operator->();
        }

        topo_iterator &operator--() {
          --itr_;
          end_ = (itr_ == std::end(*L_));
          begin_ = (itr_ == std::begin(*L_));

          return *this;
        }

        topo_iterator operator--(int) {
          topo_iterator tmp(*this);
          --itr_;
          end_ = (itr_ == std::end(*L_));
          begin_ = (itr_ == std::begin(*L_));

          return std::move(tmp);
        }

        topo_iterator &operator++() {
          ++itr_;
          end_ = (itr_ == std::end(*L_));
          begin_ = (itr_ == std::begin(*L_));

          return *this;
        }

        topo_iterator operator++(int) {
          topo_iterator tmp(*this);
          ++itr_;
          end_ = (itr_ == std::end(*L_));
          begin_ = (itr_ == std::begin(*L_));

          return std::move(tmp);
        }
        //}}}

     private:
        // Private functions {{{
        void visit(const SEG<id_type> &graph, std::set<id_type> &mark,
            const SEGNode<id_type> &node, bool reverse, bool print = false) {
          // ddevec -- TODO: Check for cycles???
          if (mark.count(node.id()) == 0) {
            // For cycles...
            mark.insert(node.id());

            std::for_each(std::begin(node.succs()), std::end(node.succs()),
                [this, &graph, &mark, reverse, print](id_type id) {
              visit(graph, mark, graph.getNode(id), reverse);
            });

            if (reverse) {
              L_->push_back(node.id());
            } else {
              L_->push_front(node.id());
            }
          }
        }
        //}}}

        // Private data {{{
        bool end_ = true;
        bool begin_ = false;

        // The lsit we calculate we need to iterate over
        std::shared_ptr<std::list<id_type>> L_;

        // Our actual iterator
        typename std::list<id_type>::iterator itr_;
        //}}}
      //}}}
    };

    class rep_iterator {
      //{{{
     public:
        // Stuff to make it stl compatible {{{
        typedef std::forward_iterator_tag iterator_category;
        typedef typename node_iterator::value_type value_type;
        typedef typename node_iterator::difference_type difference_type;
        typedef typename node_iterator::pointer pointer;
        typedef typename node_iterator::reference reference;
        //}}}

        // Constructor {{{
        explicit rep_iterator(SEG<id_type> &G, bool begin) :
            itr_((begin) ? std::begin(G) : std::end(G)),
            eitr_(std::end(G)) {
          if (begin) {
            advance_to_rep(false);
          }
        }
        //}}}

        // Operators {{{
        bool operator==(const rep_iterator &it) const {
          return (itr_ == it.itr_);
        }

        bool operator!=(const rep_iterator &it) const {
          return !operator==(it);
        }

        reference operator*() const {
          return itr_.operator*();
        }

        reference operator->() const {
          return itr_.operator->();
        }

        rep_iterator &operator++() {
          advance_to_rep();

          return *this;
        }

        rep_iterator operator++(int) {
          rep_iterator tmp(*this);
          advance_to_rep();

          return std::move(tmp);
        }
        //}}}

     private:
        // Private functions {{{
        void advance_to_rep(bool advance_first = true) {
          if (advance_first && itr_ != eitr_) {
            ++itr_;
          }

          while (itr_ != eitr_) {
            auto nd = llvm::cast<UnifyNode<id_type>>(*itr_->second);

            // If this node actually represents itself...
            if (nd.id() == itr_->first) {
              break;
            }
            ++itr_;
          }
        }
        //}}}

        // Private data {{{
        node_iterator itr_;
        node_iterator eitr_;
        //}}}
      //}}}
    };

    class const_rep_iterator {
      //{{{
     public:
        // Stuff to make it stl compatible {{{
        typedef std::forward_iterator_tag iterator_category;
        typedef typename const_node_iterator::value_type value_type;
        typedef typename const_node_iterator::difference_type difference_type;
        typedef typename const_node_iterator::pointer pointer;
        typedef typename const_node_iterator::reference reference;
        //}}}

        // Constructor {{{
        explicit const_rep_iterator(const SEG<id_type> &G, bool begin) :
            itr_((begin) ? std::begin(G) : std::end(G)),
            eitr_(std::end(G)) {
          if (begin) {
            advance_to_rep(false);
          }
        }
        //}}}

        // Operators {{{
        bool operator==(const const_rep_iterator &it) const {
          return (itr_ == it.itr_);
        }

        bool operator!=(const const_rep_iterator &it) const {
          return !operator==(it);
        }

        reference operator*() const {
          return itr_.operator*();
        }

        reference operator->() const {
          return itr_.operator->();
        }

        const_rep_iterator &operator++() {
          advance_to_rep();

          return *this;
        }

        const_rep_iterator operator++(int) {
          rep_iterator tmp(*this);
          advance_to_rep();

          return std::move(tmp);
        }
        //}}}

     private:
        // Private functions {{{
        void advance_to_rep(bool advance_first = true) {
          if (advance_first && itr_ != eitr_) {
            ++itr_;
          }

          while (itr_ != eitr_) {
            auto nd = llvm::cast<UnifyNode<id_type>>(*itr_->second);

            // If this node actually represents itself...
            if (nd.id() == itr_->first) {
              break;
            }
            ++itr_;
          }
        }
        //}}}

        // Private data {{{
        const_node_iterator itr_;
        const_node_iterator eitr_;
        //}}}
      //}}}
    };
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

    // Topo iteration {{{
    typedef topo_iterator reverse_topo_iterator;
    topo_iterator topo_begin() const {
      return topo_iterator(*this);
    }

    topo_iterator topo_end() const {
      return topo_iterator();
    }

    topo_iterator topo_begin(id_type id) const {
      return topo_iterator(*this, id);
    }

    topo_iterator topo_end(id_type) const {
      return topo_iterator();
    }

    reverse_topo_iterator topo_rbegin() const {
      return topo_iterator(*this, true);
    }

    reverse_topo_iterator topo_rend() const {
      return topo_iterator();
    }

    reverse_topo_iterator topo_rbegin(id_type id) const {
      return topo_iterator(*this, id, true);
    }

    reverse_topo_iterator topo_rend(id_type) const {
      return topo_iterator();
    }
    //}}}

    // Rep iteration {{{
    const_rep_iterator rep_cbegin() const {
      return const_rep_iterator(*this, true);
    }

    const_rep_iterator rep_cend() const {
      return const_rep_iterator(*this, false);
    }

    const_rep_iterator rep_begin() const {
      return const_rep_iterator(*this, true);
    }

    const_rep_iterator rep_end() const {
      return const_rep_iterator(*this, false);
    }

    rep_iterator rep_begin() {
      return rep_iterator(*this, true);
    }

    rep_iterator rep_end() {
      return rep_iterator(*this, false);
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
    // Converters to transform between two SEGs {{{
    SEG() = default;

    template <typename node_type, typename edge_type>
    SEG<id_type> convert() const;

    template <typename node_type, typename edge_type,
              typename new_id_type,
              typename base_node_type = SEGNode<id_type>,
              typename base_edge_type = SEGEdge<id_type>,
              typename id_converter>
    SEG<new_id_type> convert(id_converter id_convert) const;
    //}}}

    // Edge Manipulation {{{
    // Adds edge of edge_type between two nodes
    template <typename edge_type, typename... va_args>
    void addEdge(id_type src, id_type dest, va_args&... args) {
      // Ensure that a node exists for each edge point..
      auto &src_node = getNode(src);
      auto &dest_node = getNode(dest);
      edges_.emplace(std::piecewise_construct,
          std::forward_as_tuple(src, dest),
          std::forward_as_tuple(
            std::unique_ptr<SEGEdge<id_type>>(
              new edge_type(src, dest, args...))));

      // FIXME: I need to handle inserting edges with the same key multiple
      // times... although I really don't want two equivalent edges.... ugh
      /*
      if (!ret.second) {
        llvm::dbgs() << "edge is: ( " << src << ", " << dest << " )\n";

        llvm::dbgs() << "edges are:";
        for (auto &edge : edges_) {
          llvm::dbgs() << " ( " << edge.first.first << ", "
            << edge.first.second << " )";
        }
        llvm::dbgs() << "\n";
      }
      assert(ret.second);
      */

      // Add succ/pred info for src/dest
      src_node.succs().insert(dest);
      dest_node.preds().insert(src);
    }


    void removeEdge(std::pair<id_type, id_type> edge_id) {
      size_t success = edges_.erase(edge_id);
      assert(success == 1);

      // Also remove info from node:
      /*
      llvm::dbgs() << "edge_id is: ( " << edge_id.first << ", " <<
        edge_id.second << " )\n";
      */
      SEGNode<id_type> &src = *nodes_.at(edge_id.first);
      SEGNode<id_type> &dest = *nodes_.at(edge_id.second);

      /*
      llvm::dbgs() << "succs is:";
      for (auto id : src.succs()) {
        llvm::dbgs() << " " << id;
      }
      llvm::dbgs() << "\n";
      */

      // Remove the pointer from src
      auto src_it = src.succs().find(edge_id.second);
      assert(src_it != std::end(src.succs()));
      src.succs().erase(src_it);

      // Remove the pointer from dest
      auto dest_it = dest.preds().find(edge_id.first);
      assert(dest_it != std::end(dest.preds()));
      dest.preds().erase(dest_it);
    }

    void retargetEdge(std::pair<id_type, id_type> &old_id,
        std::pair<id_type, id_type> &new_id) {
      // Remove the old edge
      /*
      llvm::dbgs() << "Retargeting (" << old_id.first << ", " << old_id.second
        << ") to (" << new_id.first << ", " << new_id.second << ")\n";
      */
      auto it = edges_.find(old_id);
      assert(it != std::end(edges_));

      auto pedge = std::move(it->second);

      // Update edge src/dest
      auto &edge = *pedge;
      edge.retarget(new_id);

      // Remove the edge
      edges_.erase(it);

      // Add the new edge
      edges_.emplace(new_id, std::move(pedge));

      // Also adjust the edges within the nodes:
      auto &old_src = getNode(old_id.first);
      auto &old_dest = getNode(old_id.second);

      // Remove the preds/succs
      old_src.succs().erase(old_id.second);
      old_dest.preds().erase(old_id.first);

      auto &new_src = getNode(new_id.first);
      auto &new_dest = getNode(new_id.second);

      // Add the preds/succs
      new_src.succs().insert(new_id.second);
      new_dest.preds().insert(new_id.first);
    }
    //}}}

    // Node Manipulation {{{
    // contructs new node of node_type and inserts it into our node list
    template <typename node_type, typename... va_args>
    SEGNode<id_type> &addNode(id_type id, va_args&... args) {
      auto ret = nodes_.emplace(std::piecewise_construct,
          std::forward_as_tuple(id),
          std::forward_as_tuple(
            std::shared_ptr<SEGNode<id_type>>(
              new node_type(nodeNum_.next(), id, args...))));
      // This had better have inserted
      assert(ret.second);

      return *ret.first->second;
    }

    void removeNode(id_type id) {
      auto &node = getNode(id);

      // Remove all edges to this node
      // We need a temp vecotr, as we can't remove while iterating...
      std::vector<std::pair<id_type, id_type>> remove_edges;

      auto &preds = node.preds();
      std::for_each(std::begin(preds), std::end(preds),
          [&remove_edges, id](id_type pred_id) {
        llvm::dbgs() << "Adding pred edge: (" << pred_id << ", "
            << id << ")\n";
        remove_edges.emplace_back(pred_id, id);
      });

      // Remove all edges from this node
      auto &succs = node.succs();
      std::for_each(std::begin(succs), std::end(succs),
          [&remove_edges, id](id_type succ_id) {
        llvm::dbgs() << "Adding succ edge: (" << id << ", "
            << succ_id << ")\n";
        remove_edges.emplace_back(id, succ_id);
      });

      // Remove duplicates
      std::sort(std::begin(remove_edges), std::end(remove_edges));
      auto it = std::unique(std::begin(remove_edges), std::end(remove_edges));
      remove_edges.erase(it, std::end(remove_edges));

      for (auto &edge : remove_edges) {
        llvm::dbgs() << "Removing edge: (" << edge.first << ", "
          << edge.second << ")\n";
        removeEdge(edge);
      }

      // Delete the node
      nodes_.erase(id);
    }

    // For use by unification operations only...
    void retargetId(id_type old_id, id_type new_id) {
      auto pnode = nodes_.at(new_id);

      auto old_it = nodes_.find(old_id);

      // NOTE: This assertion could legally happen when doing a replace on
      //   convert
      // assert(old_it != std::end(nodes_));
      if (old_it != std::end(nodes_)) {
        old_it->second = pnode;
      }
    }
    //}}}
    //}}}

    // Accessors {{{

    // Gets the node, or creates it if it doesn't exist.  Creation uses the
    // default constructor for the node type
    template<typename node_type>
    SEGNode<id_type> &getOrCreateNode(id_type id);

    size_t getNumNodes() const {
      return nodes_.size();
    }

    size_t getNumEdges() const {
      return edges_.size();
    }

    // Finds a node (allows the node not to exist)
    const_node_iterator findNode(id_type id) const {
      return nodes_.find(id);
    }

    // Gets the node
    template <typename node_type = SEGNode<id_type>>
    node_type &getNode(id_type id) {
      auto pnd = nodes_.at(id);

      return llvm::cast<node_type>(*pnd);
    }

    template <typename node_type = SEGNode<id_type>>
    const node_type &getNode(id_type id) const {
      return llvm::cast<node_type>(*nodes_.at(id));
    }

    template <typename edge_type = SEGEdge<id_type>>
    const edge_type &getEdge(std::pair<id_type, id_type> &ids) const {
      return llvm::cast<edge_type>(*edges_.at(ids));
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

    UniqueIdentifier<uint32_t> nodeNum_;
    //}}}

    // Private functions {{{

    // Tarjan's SCC algorithm to detect strongly connected components
    void sccStrongconnect(SCCNode<id_type> &nd, int &index,
        std::stack<std::reference_wrapper<SCCNode<id_type>>> &st,
        SEG &ret) const;
    //}}}
  //}}}
};

// SEG Impl {{{
// Node impl {{{
// SEG converters {{{
template <typename id_type>
template <typename node_type, typename edge_type>
SEG<id_type> SEG<id_type>::convert() const {
  return convert<node_type, edge_type, id_type>
    (id_converter_default<id_type>());
}

template <typename id_type>
template <typename node_type, typename edge_type,
         typename new_id_type,
         typename base_node_type,
         typename base_edge_type,
         typename id_converter>
SEG<new_id_type> SEG<id_type>::convert(id_converter id_convert) const {
  SEG<new_id_type> ret;

  std::for_each(cbegin(), cend(),
      [this, &id_convert, &ret]
      (const node_iter_type &pr) {
    new_id_type new_id = id_convert(pr.first);
    new_id_type rep_id = id_convert(pr.second->id());
    // Check if the rep for this node exists
    auto rep_it = ret.findNode(rep_id);

    // Check if this node exists
    auto node_it = ret.findNode(new_id);

    SEGNode<new_id_type> *pnode;

    // If we havent' created this rep yet, do so
    if (rep_it == std::end(ret)) {
      // Add this node at the rep location
      pnode = &ret.addNode<node_type>(rep_id,
        llvm::cast<base_node_type>(*pr.second), id_convert);
    } else {
      pnode = rep_it->second.get();
    }

    // If this is a rep that doesn't exist, re-target it
    if (new_id != rep_id && node_it == std::end(ret)) {
      ret.retargetId(new_id, rep_id);
    }

    // NOTE: We may re-merge some extra nodes here, (for example, when the rep
    //     has already been added for this node), but merge should be safe to
    //     call multiple times on the same node...
    //     merge(A, B) = C
    //     merge(C, B) = C
    //     merge(C, A) = C
    if (node_it == std::end(ret)) {
      SEGNode<new_id_type> &nd = *pnode;

      node_type tmp_node(nodeNum_.invalid(), rep_id,
        llvm::cast<base_node_type>(*pr.second), id_convert);

      nd.merge(tmp_node);
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
        llvm::cast<base_edge_type>(*pr.second), ret, id_convert);
    } else {
      // ??? Ignore duplicate edges?
      // llvm::dbgs() << "WARNING: Ignoring duplicate edge!!!\n";
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
      rep.unite(ret, grp);

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
//}}}
//}}}
//}}}

#endif  // INCLUDE_SEG_H_
