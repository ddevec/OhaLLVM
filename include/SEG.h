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
struct edge_id { };
typedef ID<edge_id, int32_t, -1> EdgeID;

template<typename id_type>
class SEG;

// Enum For llvm RTTI {{{
enum class NodeKind {
  // SEGNodes
  HUNode,

  // DUGNodes
  DUGNode,
  AllocNode,
  PartNode,
  LoadNode,
  StoreNode,
  PhiNode,
  PartNodeEnd,
  CopyNode,
  DUGNodeEnd,

  // Unify Nodes
  Unify,
  ConstraintNode,
  CFGNode,
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
    typedef typename SEG<id_type>::EdgeID EdgeID;
    typedef typename SEG<id_type>::NodeID NodeID;

    SEGEdge(EdgeKind kind, NodeID src, NodeID dest) :
        kind_(kind), src_(src), dest_(dest) { }

    NodeID src() const {
      return src_;
    }

    NodeID dest() const {
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

    virtual bool operator==(const SEGEdge<id_type> &rhs) const {
      return src() == rhs.src() && dest() == rhs.dest();
    }

    bool operator!=(const SEGEdge<id_type> &rhs) const {
      return !operator==(rhs);
    }

    virtual bool operator==(
        const std::reference_wrapper<SEGEdge<id_type>> &rhs) const {
      // Remove reference wrapper...
      return operator==(rhs.get());
    }

    virtual bool operator<(const SEGEdge<id_type> &rhs) const {
      if (src() != rhs.src()) {
        return src() < rhs.src();
      }

      return dest() <= rhs.dest();
    }

    friend bool operator<(const std::reference_wrapper<SEGEdge<id_type>> &lhs,
        const std::reference_wrapper<SEGEdge<id_type>> &rhs) {
      // Remove reference wrapper...
      return lhs.get() < rhs.get();
    }

    void retarget(std::pair<NodeID, NodeID> &new_edge) {
      src_ = new_edge.first;
      dest_ = new_edge.second;
    }

 protected:
    EdgeKind kind_;

    NodeID src_;
    NodeID dest_;
  //}}}
};


template<typename id_type>
class SEGNode {
  //{{{
 public:
    typedef typename SEG<id_type>::NodeID NodeID;
    typedef typename SEG<id_type>::EdgeID EdgeID;

    // Constructors {{{
    SEGNode(NodeKind kind, NodeID node_id, id_type ext_id) : kind_(kind),
      id_(node_id), extId_(ext_id) { }

    SEGNode(const SEGNode &) = default;
    SEGNode(SEGNode &&) = default;

    SEGNode &operator=(const SEGNode &) = default;
    SEGNode &operator=(SEGNode &&) = default;
    //}}}

    // Comparison operators {{{
    bool operator==(const SEGNode &n) {
      return id_ == n.id_;
    }

    bool operator!=(const SEGNode &n) {
      return id_ != n.id_;
    }

    bool operator<(const SEGNode &n) {
      return id_ < n.id_;
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

    std::set<EdgeID> &preds() {
      return preds_;
    }

    const std::set<EdgeID> &preds() const {
      return preds_;
    }

    std::set<EdgeID> &succs() {
      return succs_;
    }

    const std::set<EdgeID> &succs() const {
      return succs_;
    }

    id_type extId() const {
      return extId_;
    }

    NodeID id() const {
      return id_;
    }

    // Required for SEG to support UnifyNode
    bool is_rep(id_type id) const {
      return true;
    }
    //}}}

    // LLVM RTTI support {{{
    static bool classof(const SEGNode<id_type> *) {
      return true;
    }
    //}}}

    // Modifiers {{{
    bool addSucc(SEG<id_type> &seg, EdgeID id) {
      bool found = false;
      auto &edge = seg.getEdge(id);
      for (auto edge_id : succs()) {
        auto &test_edge = seg.getEdge(edge_id);

        if (edge == test_edge) {
          found = true;
          break;
        }
      }

      if (!found) {
        succs().insert(id);
      } else {
        // If we couldn't add the edge, delete it?
        seg.tryRemoveEdge(id);
      }

      return !found;
    }

    void removeDuplicatePreds(SEG<id_type> &seg) {
      std::vector<EdgeID> remove_list;
      std::set<std::reference_wrapper<SEGEdge<id_type>>> edges;
      for (auto edge_id : preds()) {
        auto ret = edges.insert(seg.getEdge(edge_id));
        if (!ret.second) {
          remove_list.push_back(edge_id);
        }
      }

      std::for_each(std::begin(remove_list), std::end(remove_list),
          [this, &seg](EdgeID rm_id) {
        // Delete the edge
        // llvm::dbgs() << "Removing duplicate pred_edge: " << rm_id << "\n";
        seg.removeEdge(rm_id);
      });
    }

    void removeDuplicateSuccs(SEG<id_type> &seg) {
      std::vector<EdgeID> remove_list;
      std::set<std::reference_wrapper<SEGEdge<id_type>>> edges;
      for (auto edge_id : succs()) {
        auto ret = edges.insert(seg.getEdge(edge_id));
        if (!ret.second) {
          remove_list.push_back(edge_id);
        }
      }

      std::for_each(std::begin(remove_list), std::end(remove_list),
          [this, &seg](EdgeID rm_id) {
        // Delete the edge
        // llvm::dbgs() << "Removing duplicate succ_edge: " << rm_id << "\n";
        seg.removeEdge(rm_id);
      });
    }

    bool addPred(SEG<id_type> &seg, EdgeID id) {
      bool found = false;
      auto &edge = seg.getEdge(id);
      for (auto edge_id : preds()) {
        auto &test_edge = seg.getEdge(edge_id);

        if (edge == test_edge) {
          found = true;
          break;
        }
      }

      if (!found) {
        preds().insert(id);
      } else {
        // If we couldn't add the edge, delete it?
        seg.tryRemoveEdge(id);
      }

      return !found;
    }

    void tryRemoveSucc(EdgeID id) {
      auto src_it = succs().find(id);
      if (src_it != std::end(succs())) {
        succs().erase(src_it);
      }
    }

    void tryRemovePred(EdgeID id) {
      auto src_it = preds().find(id);
      if (src_it != std::end(preds())) {
        preds().erase(src_it);
      }
    }

    void removeSucc(EdgeID id) {
      auto src_it = succs().find(id);
      assert(src_it != std::end(succs()));
      succs().erase(src_it);
    }

    void removePred(EdgeID id) {
      auto src_it = preds().find(id);
      assert(src_it != std::end(preds()));
      preds().erase(src_it);
    }
    //}}}

    // Iterators {{{
    typedef typename std::set<EdgeID>::iterator iterator;
    typedef typename std::set<EdgeID>::const_iterator const_iterator;

    iterator succ_begin() {
      return std::begin(succs_);
    }

    iterator succ_end() {
      return std::end(succs_);
    }

    const_iterator succ_begin() const {
      return std::begin(succs_);
    }

    const_iterator succ_end() const {
      return std::end(succs_);
    }

    const_iterator succ_cbegin() const {
      return succs_.cbegin();
    }

    const_iterator succ_cend() const {
      return succs_.cend();
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
    NodeID id_;

    // The id for this node
    id_type extId_;
    //}}}

 protected:
    // Protected data {{{
    // We hold references to our pred and successor nodes
    std::set<EdgeID> preds_;
    std::set<EdgeID> succs_;
    //}}}
  //}}}
};

template<typename id_type>
class UnifyNode : public SEGNode<id_type> {
  // {{{
 public:
    typedef typename SEG<id_type>::NodeID NodeID;
    typedef typename SEG<id_type>::EdgeID EdgeID;
    // Constructors {{{
    UnifyNode(NodeKind kind, NodeID node_id, id_type id) :
      SEGNode<id_type>(kind, node_id, id) {
        reps_.insert(id);
      }

    UnifyNode(const UnifyNode &) = default;
    UnifyNode(UnifyNode &&) = default;

    UnifyNode &operator=(const UnifyNode &) = default;
    UnifyNode &operator=(UnifyNode &&) = default;
    //}}}

    // Actual unite functionality {{{
    virtual void unite(SEG<id_type> &graph, SEGNode<id_type> &n) {
      assert(SEGNode<id_type>::operator!=(n));
      // Retarget all edges pointing towards n
      // llvm::dbgs() << "Testing preds for node: " << n.id() << "\n";
      std::vector<EdgeID> preds(std::begin(n.preds()), std::end(n.preds()));
      std::for_each(std::begin(preds), std::end(preds),
          [this, &graph, &n](EdgeID pred_edge_id) {
        auto &old_edge = graph.getEdge(pred_edge_id);
        // llvm::dbgs() << "have edge_id: " << pred_edge_id << "\n";
        NodeID pred_id = old_edge.src();
        // llvm::dbgs() << "Have pred: " << pred_id << "\n";

        auto new_edge = std::make_pair(pred_id, SEGNode<id_type>::id());

        // properly handle ptr to self
        if (pred_id == n.id()) {
          new_edge.first = new_edge.second;
        }

        /*
        llvm::dbgs() << "new_edge: (" << new_edge.first << ", " <<
            new_edge.second << ")\n";
        */

        // If the old edge wasn't a pointer to self, and the new edge is a
        // pointer to self, don't retarget it, just remove it
        if (old_edge.src() != old_edge.dest() &&
              new_edge.first == new_edge.second) {
          // llvm::dbgs() << "Removing edge\n";
          graph.removeEdge(pred_edge_id);
        } else {
          // llvm::dbgs() << "Retargeting edge (" << pred_edge_id << ")\n";
          graph.retargetEdge(pred_edge_id, new_edge);
        }
      });

      // And all edges from n
      // llvm::dbgs() << "Testing succs for node: " << n.id() << "\n";
      std::vector<EdgeID> succs(std::begin(n.succs()), std::end(n.succs()));
      std::for_each(std::begin(succs), std::end(succs),
          [this, &graph, &n](EdgeID succ_edge_id) {
        // llvm::dbgs() << "have edge_id: " << succ_edge_id << "\n";
        auto old_edge = graph.getEdge(succ_edge_id);
        NodeID succ_id = old_edge.dest();

        // llvm::dbgs() << "Have succ: " << succ_id << "\n";

        auto new_edge = std::make_pair(SEGNode<id_type>::id(), succ_id);

        /*
        llvm::dbgs() << "new_edge: (" << new_edge.first << ", " <<
            new_edge.second << ")\n";
        */

        if (succ_id == n.id()) {
          new_edge.second = new_edge.first;
        }

        // If the old edge wasn't a pointer to self, and the new edge is a
        // pointer to self, don't retarget it, just remove it
        if (old_edge.src() != old_edge.dest() &&
              new_edge.first == new_edge.second) {
          // llvm::dbgs() << "Removing edge\n";
          graph.removeEdge(succ_edge_id);
        } else {
          // llvm::dbgs() << "Retargeting edge(" << succ_edge_id << ")\n";
          graph.retargetEdge(succ_edge_id, new_edge);
        }
      });

      // Also replace the graph's index to n with our pointer
      auto &un = llvm::cast<UnifyNode<id_type>>(n);

      std::vector<id_type> rep(un.rep_begin(), un.rep_end());
      assert(rep.size() > 0);
      std::for_each(std::begin(rep), std::end(rep),
          [this, &graph](id_type rep_id) {
        graph.retargetId(rep_id, SEGNode<id_type>::id());

        // Add all rep ids to our "reps"
        reps_.insert(rep_id);
      });

      // We have to clear the node's reps, so they aren't deleted, because we
      //   just merged them!
      un.reps_.clear();
      // delete the node
      n.preds().clear();
      n.succs().clear();
      graph.removeNode(un.id());
    }
    //}}}

    // Accessors: {{{
    // Required for unify node:
    bool is_rep(id_type id) {
      return id() == id;
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
    bool del_ = false;
    //}}}
  //}}}
};

template <typename id_type>
class SEG {
  //{{{
 public:
    // Typedefs {{{
    struct node_id { };
    typedef ID<node_id, int32_t, -1> NodeID;

    struct edge_id { };
    typedef ID<edge_id, int32_t, -1> EdgeID;
    //}}}
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
    typedef std::multimap<id_type, NodeID> NodeMap;
    typedef typename NodeMap::iterator node_map_iterator;
    typedef typename NodeMap::const_iterator const_node_map_iterator;

    typedef std::unique_ptr<SEGNode<id_type>> node_iter_type;

    /*
    typedef typename std::vector<std::unique_ptr<SEGNode<id_type>>>::iterator
      node_iterator;
    typedef typename std::vector<std::unique_ptr<SEGNode<id_type>>>::const_iterator
      const_node_iterator;
    */

    typedef typename std::vector<NodeID>::iterator
      scc_iterator;
    typedef typename std::vector<NodeID>::const_iterator
      const_scc_iterator;

    typedef typename std::unique_ptr<SEGEdge<id_type>>
      edge_iter_type;
    /*
    typedef typename std::vector<std::unique_ptr<SEGEdge<id_type>>>::iterator
      edge_iterator;
    typedef typename std::vector<std::unique_ptr<SEGEdge<id_type>>>::const_iterator // NOLINT
      const_edge_iterator;
    */
    //}}}


    // Iterator Types {{{
    // Node iterator {{{
    class node_iterator {
      //{{{
     public:
        // Stuff to make it stl compatible {{{
        typedef std::bidirectional_iterator_tag iterator_category;
        typedef typename std::vector<node_iter_type>::value_type value_type;
        typedef typename std::vector<node_iter_type>::difference_type
          difference_type;
        typedef typename std::vector<node_iter_type>::pointer pointer;
        typedef typename std::vector<node_iter_type>::reference reference;
        //}}}

        // Constructors {{{
        // No arguments returns end()
        explicit node_iterator(
            typename std::vector<node_iter_type>::iterator itr,
            typename std::vector<node_iter_type>::iterator end) :
          itr_(itr), end_(end) {
            while (itr_ != end_ && *itr_ == nullptr) {
              ++itr_;
            }
        }

        node_iterator(const node_iterator &) = default;
        node_iterator(node_iterator &&) = default;

        node_iterator &operator=(const node_iterator &) = default;
        node_iterator &operator=(node_iterator &&) = default;

        // Without a node does iteration for the graph
        //}}}

        // accessors {{{
        bool operator==(const node_iterator &it) const {
          return (itr_ == it.itr_);
        }

        bool operator!=(const node_iterator &it) const {
          return !operator==(it);
        }

        reference operator*() const {
          reference ret = itr_.operator*();
          assert(ret != nullptr);
          return ret;
        }

        reference operator->() const {
          reference ret = itr_.operator->();
          assert(ret != nullptr);
          return ret;
        }

        node_iterator &operator--() {
          --itr_;
          while (itr_ != end_ && *itr_ == nullptr) {
            --itr_;
          }

          return *this;
        }

        node_iterator operator--(int) {
          node_iterator tmp(*this);
          --itr_;

          while (itr_ != end_ && *itr_ == nullptr) {
            --itr_;
          }

          return std::move(tmp);
        }

        node_iterator &operator++() {
          ++itr_;

          while (itr_ != end_ && *itr_ == nullptr) {
            ++itr_;
          }

          return *this;
        }

        node_iterator operator++(int) {
          node_iterator tmp(*this);
          ++itr_;

          while (itr_ != end_ && *itr_ == nullptr) {
            ++itr_;
          }

          return std::move(tmp);
        }
        //}}}

     private:
        // Private data {{{
        typename std::vector<node_iter_type>::iterator itr_;
        typename std::vector<node_iter_type>::iterator end_;
        //}}}
      //}}}
    };

    class const_node_iterator {
      //{{{
     public:
        // Stuff to make it stl compatible {{{
        typedef std::bidirectional_iterator_tag iterator_category;
        typedef typename std::vector<node_iter_type>::value_type value_type;
        typedef typename std::vector<node_iter_type>::difference_type
          difference_type;
        typedef typename std::vector<node_iter_type>::pointer pointer;
        typedef typename std::vector<node_iter_type>::reference reference;
        //}}}

        // Constructors {{{
        // No arguments returns end()
        explicit const_node_iterator(
            typename std::vector<node_iter_type>::const_iterator itr,
            typename std::vector<node_iter_type>::const_iterator end) :
          itr_(itr), end_(end) {
            while (itr_ != end_ && *itr_ == nullptr) {
              ++itr_;
            }
          }

        const_node_iterator(const const_node_iterator &) = default;
        const_node_iterator(const_node_iterator &&) = default;

        const_node_iterator &operator=(const const_node_iterator &) = default;
        const_node_iterator &operator=(const_node_iterator &&) = default;

        // Without a node does iteration for the graph
        //}}}

        // accessors {{{
        bool operator==(const const_node_iterator &it) const {
          return (itr_ == it.itr_);
        }
        bool operator!=(const const_node_iterator &it) const {
          return !operator==(it);
        }

        const std::unique_ptr<SEGNode<id_type>> &operator*() const {
          auto &ret = itr_.operator*();
          assert(ret != nullptr);
          return ret;
        }

        const std::unique_ptr<SEGNode<id_type>> &operator->() const {
          auto &ret = itr_.operator->();
          assert(ret != nullptr);
          return ret;
        }

        const_node_iterator &operator--() {
          --itr_;
          while (itr_ != end_ && *itr_ == nullptr) {
            --itr_;
          }

          return *this;
        }

        const_node_iterator operator--(int) {
          const_node_iterator tmp(*this);
          --itr_;

          while (itr_ != end_ && *itr_ == nullptr) {
            --itr_;
          }

          return std::move(tmp);
        }

        const_node_iterator &operator++() {
          ++itr_;

          while (itr_ != end_ && *itr_ == nullptr) {
            ++itr_;
          }

          return *this;
        }

        const_node_iterator operator++(int) {
          const_node_iterator tmp(*this);
          ++itr_;

          while (itr_ != end_ && *itr_ == nullptr) {
            ++itr_;
          }

          return std::move(tmp);
        }
        //}}}

     private:
        // Private data {{{
        typename std::vector<node_iter_type>::const_iterator itr_;
        typename std::vector<node_iter_type>::const_iterator end_;
        //}}}
      //}}}
    };
    //}}}

    // Edge iterator {{{
    class edge_iterator {
      //{{{
     public:
        // Stuff to make it stl compatible {{{
        typedef std::bidirectional_iterator_tag iterator_category;
        typedef typename std::vector<edge_iter_type>::value_type value_type;
        typedef typename std::vector<edge_iter_type>::difference_type
          difference_type;
        typedef typename std::vector<edge_iter_type>::pointer pointer;
        typedef typename std::vector<edge_iter_type>::reference reference;
        //}}}

        // Constructors {{{
        // No arguments returns end()
        explicit edge_iterator(
            typename std::vector<edge_iter_type>::iterator itr,
            typename std::vector<edge_iter_type>::iterator end) :
          itr_(itr), end_(end) {
          while (itr_ != end_ && *itr_ == nullptr) {
            ++itr_;
          }
        }

        edge_iterator(const edge_iterator &) = default;
        edge_iterator(edge_iterator &&) = default;

        edge_iterator &operator=(const edge_iterator &) = default;
        edge_iterator &operator=(edge_iterator &&) = default;

        // Without a node does iteration for the graph
        //}}}

        // accessors {{{
        bool operator==(const edge_iterator &it) const {
          return (itr_ == it.itr_);
        }

        bool operator!=(const edge_iterator &it) const {
          return !operator==(it);
        }

        reference operator*() const {
          reference ret = itr_.operator*();
          assert(ret != nullptr);
          return ret;
        }

        reference operator->() const {
          reference ret = itr_.operator->();
          assert(ret != nullptr);
          return ret;
        }

        edge_iterator &operator--() {
          --itr_;
          while (itr_ != end_ && *itr_ == nullptr) {
            --itr_;
          }

          return *this;
        }

        edge_iterator operator--(int) {
          edge_iterator tmp(*this);
          --itr_;

          while (itr_ != end_ && *itr_ == nullptr) {
            --itr_;
          }

          return std::move(tmp);
        }

        edge_iterator &operator++() {
          ++itr_;

          while (itr_ != end_ && *itr_ == nullptr) {
            ++itr_;
          }

          return *this;
        }

        edge_iterator operator++(int) {
          edge_iterator tmp(*this);
          ++itr_;

          while (itr_ != end_ && *itr_ == nullptr) {
            ++itr_;
          }

          return std::move(tmp);
        }
        //}}}

     private:
        // Private data {{{
        typename std::vector<edge_iter_type>::iterator itr_;
        typename std::vector<edge_iter_type>::iterator end_;
        //}}}
      //}}}
    };

    class const_edge_iterator {
      //{{{
     public:
        // Stuff to make it stl compatible {{{
        typedef std::bidirectional_iterator_tag iterator_category;
        typedef typename std::vector<edge_iter_type>::value_type value_type;
        typedef typename std::vector<edge_iter_type>::difference_type
          difference_type;
        typedef typename std::vector<edge_iter_type>::pointer pointer;
        typedef typename std::vector<edge_iter_type>::reference reference;
        //}}}

        // Constructors {{{
        // No arguments returns end()
        explicit const_edge_iterator(
            typename std::vector<edge_iter_type>::const_iterator itr,
            typename std::vector<edge_iter_type>::const_iterator end) :
            itr_(itr), end_(end) {
          while (itr_ != end_ && *itr_ == nullptr) {
            ++itr_;
          }
        }

        const_edge_iterator(const const_edge_iterator &) = default;
        const_edge_iterator(const_edge_iterator &&) = default;

        const_edge_iterator &operator=(const const_edge_iterator &) = default;
        const_edge_iterator &operator=(const_edge_iterator &&) = default;

        // Without a node does iteration for the graph
        //}}}

        // accessors {{{
        bool operator==(const const_edge_iterator &it) const {
          return (itr_ == it.itr_);
        }
        bool operator!=(const const_edge_iterator &it) const {
          return !operator==(it);
        }

        const std::unique_ptr<SEGEdge<id_type>> &operator*() const {
          auto &ret = itr_.operator*();
          assert(ret != nullptr);
          return ret;
        }

        const std::unique_ptr<SEGEdge<id_type>> &operator->() const {
          auto &ret = itr_.operator->();
          assert(ret != nullptr);
          return ret;
        }

        const_edge_iterator &operator--() {
          --itr_;
          while (itr_ != end_ && *itr_ == nullptr) {
            --itr_;
          }

          return *this;
        }

        const_edge_iterator operator--(int) {
          const_edge_iterator tmp(*this);
          --itr_;

          while (itr_ != end_ && *itr_ == nullptr) {
            --itr_;
          }

          return std::move(tmp);
        }

        const_edge_iterator &operator++() {
          ++itr_;

          while (itr_ != end_ && *itr_ == nullptr) {
            ++itr_;
          }

          return *this;
        }

        const_edge_iterator operator++(int) {
          const_edge_iterator tmp(*this);
          ++itr_;

          while (itr_ != end_ && *itr_ == nullptr) {
            ++itr_;
          }

          return std::move(tmp);
        }
        //}}}

     private:
        // Private data {{{
        typename std::vector<edge_iter_type>::const_iterator itr_;
        typename std::vector<edge_iter_type>::const_iterator end_;
        //}}}
      //}}}
    };
    //}}}

    class topo_iterator {
      //{{{
     public:
        // Stuff to make it stl compatible {{{
        typedef std::bidirectional_iterator_tag iterator_category;
        typedef typename std::list<NodeID>::value_type value_type;
        typedef typename std::list<NodeID>::difference_type difference_type;
        typedef typename std::list<NodeID>::pointer pointer;
        typedef typename std::list<NodeID>::reference reference;
        //}}}

        // Constructors {{{
        // No arguments returns end()
        topo_iterator() = default;

        topo_iterator(const topo_iterator &) = default;
        topo_iterator(topo_iterator &&) = default;

        topo_iterator &operator=(const topo_iterator &) = default;
        topo_iterator &operator=(topo_iterator &&) = default;

        // With node, does reverse topo iteration for the node
        topo_iterator(const SEG<id_type> &graph, NodeID start_node,
              bool reverse = false) :
            end_(false), begin_(true),
            L_(std::make_shared<std::list<NodeID>>()) {
          std::set<NodeID> mark;

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
        explicit topo_iterator(SEG<id_type> &graph,
              bool reverse = false) :
            end_(false),
            begin_(true),
            L_(std::make_shared<std::list<NodeID>>()) {
          std::set<NodeID> mark;
          // llvm::dbgs() << "topo iterator create\n";

          /*
          std::for_each(std::begin(graph), std::end(graph),
              [this, &graph, &mark, reverse] (const node_iter_type &pr) {
            auto &node = *pr.second;
            llvm::dbgs() << "visit node: " << pr.first << ", node.id(): "
                << node.id() << "\n";
            visit(graph, mark, node, reverse, true);
          });
          */


          for (auto itr = std::begin(graph), en = std::end(graph);
              itr != en; ++itr) {
            auto &node = *(*itr);

            /*
            llvm::dbgs() << "visit node: " << itr->first << ", node.id(): "
                << node.id() << "\n";
                */
            visit(graph, mark, node, reverse, true);
          }

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

        NodeID operator*() const {
          return itr_.operator*();
        }

        NodeID operator->() const {
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
        void visit(const SEG<id_type> &graph, std::set<NodeID> &mark,
            const SEGNode<id_type> &node, bool reverse, bool print = false) {
          // ddevec -- TODO: Check for cycles???
          if (mark.count(node.id()) == 0) {
            /*
            llvm::dbgs() << "Checking node: " << node.id() << "\n";
            */
            // For cycles...
            mark.insert(node.id());

            auto &succs = node.succs();
            std::for_each(std::begin(succs), std::end(succs),
                [this, &graph, &mark, reverse, print](EdgeID edge_id) {
              auto &edge = graph.getEdge(edge_id);
              visit(graph, mark, graph.getNode(edge.dest()), reverse);
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
        std::shared_ptr<std::list<NodeID>> L_;

        // Our actual iterator
        typename std::list<NodeID>::iterator itr_;
        //}}}
      //}}}
    };

    class rep_iterator {
      //{{{
     public:
        // Stuff to make it stl compatible {{{
        typedef std::forward_iterator_tag iterator_category;
        typedef typename node_map_iterator::value_type value_type;
        typedef typename node_map_iterator::difference_type difference_type;
        typedef typename node_map_iterator::pointer pointer;
        typedef typename node_map_iterator::reference reference;
        //}}}

        // Constructor {{{
        // FIXME -- map_begin?
        explicit rep_iterator(SEG<id_type> &G, bool begin) :
            G_(G), itr_((begin) ? G.map_begin() : G.map_end()),
            eitr_(G.map_end()) {
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
            auto nd = G_.getNode<UnifyNode<id_type>>(*itr_->second);

            // If this node actually represents itself...
            if (nd.id() == itr_->first) {
              break;
            }

            ++itr_;
          }
        }
        //}}}

        // Private data {{{
        SEG<id_type> &G_;
        node_map_iterator itr_;
        node_map_iterator eitr_;
        //}}}
      //}}}
    };

    class const_rep_iterator {
      //{{{
     public:
        // Stuff to make it stl compatible {{{
        typedef std::forward_iterator_tag iterator_category;
        typedef typename const_node_map_iterator::value_type value_type;
        typedef typename const_node_map_iterator::difference_type
          difference_type;
        typedef typename const_node_map_iterator::pointer pointer;
        typedef typename const_node_map_iterator::reference reference;
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
        const_node_map_iterator itr_;
        const_node_map_iterator eitr_;
        //}}}
      //}}}
    };
    //}}}

    // NodeMap iteration {{{
    node_map_iterator node_map_begin() {
      return std::begin(node_map_);
    }

    node_map_iterator node_map_end() {
      return std::end(node_map_);
    }

    const_node_map_iterator node_map_begin() const {
      return std::begin(node_map_);
    }

    const_node_map_iterator node_map_end() const {
      return std::end(node_map_);
    }

    const_node_map_iterator node_map_cbegin() const {
      return std::begin(node_map_);
    }

    const_node_map_iterator node_map_cend() const {
      return std::end(node_map_);
    }
    //}}}

    // Node iteration (pair<id, node>) {{{
    node_iterator begin() {
      return node_iterator(std::begin(nodes_), std::end(nodes_));
    }

    node_iterator end() {
      return node_iterator(std::end(nodes_), std::end(nodes_));
    }

    const_node_iterator begin() const {
      return const_node_iterator(std::begin(nodes_), std::end(nodes_));
    }

    const_node_iterator end() const {
      return const_node_iterator(std::end(nodes_), std::end(nodes_));
    }

    const_node_iterator cbegin() const {
      return const_node_iterator(std::begin(nodes_), std::end(nodes_));
    }

    const_node_iterator cend() const {
      return const_node_iterator(std::end(nodes_), std::end(nodes_));
    }
    //}}}

    // Topo iteration {{{
    typedef topo_iterator reverse_topo_iterator;
    topo_iterator topo_begin() {
      return topo_iterator(*this);
    }

    topo_iterator topo_end() {
      return topo_iterator();
    }

    topo_iterator topo_begin(id_type id) const {
      return topo_iterator(*this, id);
    }

    topo_iterator topo_end(id_type) const {
      return topo_iterator();
    }

    reverse_topo_iterator topo_rbegin() {
      return topo_iterator(*this, true);
    }

    reverse_topo_iterator topo_rend() {
      return topo_iterator();
    }

    reverse_topo_iterator topo_rbegin(NodeID id) const {
      return topo_iterator(*this, id, true);
    }

    reverse_topo_iterator topo_rend(NodeID) const {
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
      return edge_iterator(std::begin(edges_), std::end(edges_));;
    }

    edge_iterator edges_end() {
      return edge_iterator(std::end(edges_), std::end(edges_));;
    }

    const_edge_iterator edges_begin() const {
      return const_edge_iterator(std::begin(edges_), std::end(edges_));;
    }

    const_edge_iterator edges_end() const {
      return const_edge_iterator(std::end(edges_), std::end(edges_));;
    }

    const_edge_iterator edges_cbegin() const {
      return const_edge_iterator(std::begin(edges_), std::end(edges_));;
    }

    const_edge_iterator edges_cend() const {
      return const_edge_iterator(std::end(edges_), std::end(edges_));;
    }
    //}}}

    //}}}

    // Modifiers {{{
    // Converters to transform between two SEGs {{{
    SEG() = default;

    template <typename node_type, typename edge_type>
    SEG<id_type> clone() const;
    //}}}

    // Edge Manipulation {{{
    template <typename edge_type>
    EdgeID addEdge(const edge_type &edge) {
      // Ensure that a node exists for each edge point..
      edges_.emplace_back(new edge_type(edge));

      EdgeID edge_id(edges_.size() - 1);

      // FIXME: ddevec -- Don't think I actually need this, because the edge ids
      //   will be duplicated by the copy constructor of the nodes
      assert(getNode(edge.src()).succs().find(edge_id) !=
          std::end(getNode(edge.src()).succs()));
      assert(getNode(edge.dest()).preds().find(edge_id) !=
          std::end(getNode(edge.dest()).preds()));
      /*
      auto &src_node = getNode(edge.src());
      auto &dest_node = getNode(edge.dest());

      // Add succ/pred info for src/dest
      src_node.addSucc(*this, edge_id);
      dest_node.addPred(*this, edge_id);
      */

      return edge_id;
    }

    // Adds edge of edge_type between two nodes
    template <typename edge_type, typename... va_args>
    EdgeID addEdge(NodeID src, NodeID dest, va_args&... args) {
      // Ensure that a node exists for each edge point..
      auto &src_node = getNode(src);
      auto &dest_node = getNode(dest);
      edges_.emplace_back(new edge_type(src, dest, args...));

      EdgeID edge_id(edges_.size() - 1);

      // Add succ/pred info for src/dest
      bool ret = src_node.addSucc(*this, edge_id);
      if (!ret) {
        edges_.pop_back();
        return EdgeID::invalid();
      }
      ret = dest_node.addPred(*this, edge_id);
      if (!ret) {
        src_node.removeSucc(edge_id);
        edges_.pop_back();
        return EdgeID::invalid();
      }

      return edge_id;
    }

    void tryRemoveEdge(EdgeID id) {
      // Also remove info from node:
      /*
      llvm::dbgs() << "edge_id is: ( " << edge_id.first << ", " <<
        edge_id.second << " )\n";
      */
      auto &edge = getEdge(id);

      auto &src = getNode(edge.src());
      auto &dest = getNode(edge.dest());

      // Free up the memory... maybe resize the array at some point?
      // llvm::dbgs() << __LINE__ << "erasing: " << id << "\n";
      edges_.at(id.val()).reset(nullptr);

      // Remove the pointer from src
      src.tryRemoveSucc(id);

      // Remove the pointer from dest
      dest.tryRemovePred(id);
    }

    void removeEdge(EdgeID id) {
      // Also remove info from node:
      /*
      llvm::dbgs() << "edge_id is: ( " << edge_id.first << ", " <<
        edge_id.second << " )\n";
      */
      auto &edge = getEdge(id);

      auto &src = getNode(edge.src());
      auto &dest = getNode(edge.dest());

      // Free up the memory... maybe resize the array at some point?
      // llvm::dbgs() << __LINE__ << "erasing: " << id << "\n";
      edges_.at(id.val()).reset(nullptr);

      // Remove the pointer from src
      src.removeSucc(id);

      // Remove the pointer from dest
      dest.removePred(id);
    }

    void retargetEdge(EdgeID id,
        std::pair<NodeID, NodeID> &new_target) {
      // Update edge src/dest
      auto &edge = getEdge(id);
      /*
      llvm::dbgs() << "Retargeting (" << edge.src() << ", " << edge.dest()
        << ") to (" << new_target.first << ", " << new_target.second << ")\n";
        */

      // Fix up for equivalence between multiple edges?
      auto &src = getNode(edge.src());
      auto &dest = getNode(edge.dest());

      // Actually add the edge to the new source and dest
      // llvm::dbgs() << "removing succ from src: " << src.id() << "\n";
      src.removeSucc(id);
      // llvm::dbgs() << "removing pred from dest: " << dest.id() << "\n";
      dest.removePred(id);

      edge.retarget(new_target);

      auto &new_src = getNode(new_target.first);
      auto &new_dest = getNode(new_target.second);
      /*
      llvm::dbgs() << "adding succ (" << id << ") to new_src: "
        << new_src.id() << "\n";
      */
      // Only add the pred if the succ succeeded!
      if (new_src.addSucc(*this, id)) {
        /*
        llvm::dbgs() << "adding pred (" << id << ") to new_dest: "
          << new_dest.id() << "\n";
        */
        new_dest.addPred(*this, id);
      }

      // Removing duplicates?
      new_src.removeDuplicateSuccs(*this);
      new_dest.removeDuplicatePreds(*this);
    }
    //}}}

    // Node Manipulation {{{
    // contructs new node of node_type and inserts it into our node list
    template <typename node_type>
    void addNode(const node_type &nd) {
      nodes_.emplace_back(new node_type(nd));
    }

    template <typename node_type, typename... va_args>
    node_map_iterator addNode(id_type id, va_args&... args) {
      auto node_id = NodeID(nodes_.size());
      // llvm::dbgs() << "Adding node: " << node_id << "\n";
      nodes_.emplace_back(new node_type(node_id, id, args...));

      auto ret = node_map_.emplace(id, node_id);

      return ret;
    }

    void removeNode(NodeID id) {
      auto &node = getNode(id);

      // Remove all edges to this node
      // We need a temp container, as we can't remove while iterating...
      std::vector<EdgeID> remove_edges;

      auto &preds = node.preds();
      std::for_each(std::begin(preds), std::end(preds),
          [&remove_edges](EdgeID pred_id) {
        remove_edges.emplace_back(pred_id);
      });

      // Remove all edges from this node
      auto &succs = node.succs();
      std::for_each(std::begin(succs), std::end(succs),
          [&remove_edges](EdgeID succ_id) {
        remove_edges.emplace_back(succ_id);
      });

      // Remove duplicates
      std::sort(std::begin(remove_edges), std::end(remove_edges));
      auto it = std::unique(std::begin(remove_edges), std::end(remove_edges));
      remove_edges.erase(it, std::end(remove_edges));

      for (auto &edge : remove_edges) {
        /*
        llvm::dbgs() << "  Edge remove: (" << getEdge(edge).src() << ", " <<
          getEdge(edge).dest() << ")\n";
          */
        removeEdge(edge);
      }

      // llvm::dbgs() << "calling nodes_.erase on id: " << id << "\n";

      // Delete the node
      // If its a unify node, we need to mark it as deleted... because multiple
      //   ids may point to it
      if (auto pun = llvm::dyn_cast<UnifyNode<id_type>>(&node)) {
        // This should really be, for each id in rep, remove from nodes
        std::for_each(pun->rep_begin(), pun->rep_end(),
            [this](id_type id) {
          node_map_.erase(id);
        });
      } else {
        node_map_.erase(node.extId());
      }

      // llvm::dbgs() << __LINE__ << " erasing: " << node.id() << "\n";
      nodes_.at(node.id().val()).reset(nullptr);
    }

    void addMapping(id_type ext_id, NodeID mapped_node) {
      auto node_range = node_map_.equal_range(ext_id);
      if (std::distance(node_range.first, node_range.second) == 0) {
        node_map_.emplace(ext_id, mapped_node);
      } else {
        std::for_each(node_range.first, node_range.second,
            [this, &mapped_node] (std::pair<const id_type, NodeID> &pr) {
          pr.second = mapped_node;
        });
      }
    }

    // For use by unification operations only...
    void retargetId(id_type old_id, NodeID new_dest) {
      auto pr = node_map_.equal_range(old_id);

      std::for_each(pr.first, pr.second,
          [&new_dest](std::pair<const id_type, NodeID> &pr) {
        pr.second = new_dest;
      });
    }
    //}}}
    //}}}

    // Accessors {{{

    // Gets the node, or creates it if it doesn't exist.  Creation uses the
    // default constructor for the node type
    size_t getNumNodes() const {
      return nodes_.size();
    }

    size_t getNumEdges() const {
      return edges_.size();
    }

    // Finds a node (allows the node not to exist)
    const_node_map_iterator findNode(id_type id) const {
      return node_map_.find(id);
    }

    // Gets the node
    template <typename node_type = SEGNode<id_type>>
    node_type *getNodeOrNull(id_type id) {
      // We jsut get the lower one...
      auto itr = node_map_.lower_bound(id);
      if (itr->first != id) {
        return nullptr;
      }

      return &getNode<node_type>(itr->second);
    }

    std::pair<node_map_iterator, node_map_iterator>
    getNodesOrNull(id_type id) {
      auto pr = node_map_.equal_range(id);

      return pr;
    }

    std::pair<node_map_iterator, node_map_iterator>
    getNodes(id_type id) {
      auto pr = node_map_.equal_range(id);
      assert(std::distance(pr.first, pr.second) > 0);

      return pr;
    }

    std::pair<const_node_map_iterator, const_node_map_iterator>
    getNodes(id_type id) const {
      auto pr = node_map_.equal_range(id);
      assert(std::distance(pr.first, pr.second) > 0);

      return pr;
    }

    template <typename node_type = SEGNode<id_type>>
    node_type &getNode(NodeID id) {
      auto &pnd = nodes_.at(id.val());
      assert(pnd != nullptr);

      return llvm::cast<node_type>(*pnd);
    }

    template <typename node_type = SEGNode<id_type>>
    const node_type &getNode(NodeID id) const {
      auto &pnd = nodes_.at(id.val());
      assert(pnd != nullptr);

      return llvm::cast<node_type>(*pnd);
    }

    template <typename edge_type = SEGEdge<id_type>>
    const edge_type &getEdge(EdgeID edge_id) const {
      return llvm::cast<edge_type>(*edges_.at(edge_id.val()));
    }

    template <typename edge_type = SEGEdge<id_type>>
    edge_type &getEdge(EdgeID edge_id) {
      return llvm::cast<edge_type>(*edges_.at(edge_id.val()));
    }

    /*
    const_edge_iterator findEdge(std::pair<id_type, id_type> &id) const {
      return edges_.find(id);
    }
    */

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
          (const node_iter_type &pnode) {
        const SEGNode<id_type> &node = *pnode;
        std::string idNode = idToString(node.extId());

        ofil << "  " << idNode << " [label=\"";
        node.print_label(ofil, omap);
        ofil << "\"" << " shape=box" << "];\n";
      });

      /*
      std::for_each(edges_begin(), edges_end(),
      */
      int edge_id = 0;
      std::for_each(std::begin(edges_), std::end(edges_),
          [this, &ofil, &omap, &edge_id]
          (const edge_iter_type &pedge) {
        if (pedge != nullptr) {
          auto &edge = *pedge;
          /*
          llvm::dbgs() << "Getting src: " << edge.src() << " from edge: " <<
              edge_id << "\n";
              */
          std::string idNode1 = idToString(getNode(edge.src()).extId());
          std::string idNode2 = idToString(getNode(edge.dest()).extId());

          ofil << "  " << idNode1 << " -> " << idNode2 <<
            " [label=\"";
          edge.print_label(ofil, omap);
          ofil << "\"];\n";
        }
        edge_id++;
      });
      printDotFooter(ofil);
    }
    //}}}

 private:
    friend class SEGNode<id_type>;
    // Private variables {{{
    // Holds all of the nodes
    std::vector<std::unique_ptr<SEGNode<id_type>>> nodes_;

    NodeMap node_map_;

    // Holds edge data
    std::vector<std::unique_ptr<SEGEdge<id_type>>> edges_;
    //}}}

    // Private functions {{{

    // Tarjan's SCC algorithm to detect strongly connected components
    class SCCData {
      //{{{
     public:
        static const int32_t invalidIndex = std::numeric_limits<int32_t>::min();

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

     private:
        // Private variables (used for Tarjan's SCC) {{{
        int32_t index_ = invalidIndex;
        int32_t lowlink_ = invalidIndex;
        bool onStack_ = false;
        //}}}
      //}}}
    };

    bool checkEdge(EdgeID edge_id) const {
      auto &edge = getEdge(edge_id);

      // llvm::dbgs() << "getting edge: " << edge_id << "\n";

      /*
      llvm::dbgs() << "  edge: (" << edge.src() << ", "
        << edge.dest() << "\n";
        */

      auto &src_node = getNode(edge.src());
      auto &dest_node = getNode(edge.dest());

      /*
      llvm::dbgs() << "  src.succs:";
      std::for_each(std::begin(src_node.succs()), std::end(src_node.succs()),
          [](EdgeID id) {
        llvm::dbgs() << " " << id;
      });
      llvm::dbgs() << "\n";

      llvm::dbgs() << "  dest.preds:";
      std::for_each(std::begin(dest_node.preds()), std::end(dest_node.preds()),
          [](EdgeID id) {
        llvm::dbgs() << " " << id;
      });
      llvm::dbgs() << "\n";
      */

      assert(src_node.succs().find(edge_id) !=
          std::end(getNode(edge.src()).succs()));
      assert(dest_node.preds().find(edge_id) !=
          std::end(getNode(edge.dest()).preds()));
      return true;
    }

    void sccStrongconnect(std::vector<SCCData> &seg_data,
      NodeID id, int &index, std::stack<NodeID> &st, SEG &ret) const;
    //}}}
  //}}}
};

// SEG Impl {{{
// SEG clone {{{
template <typename id_type>
template <typename node_type, typename edge_type>
SEG<id_type> SEG<id_type>::clone() const {
  SEG<id_type> ret;

  // We don't use node itr, because we want to include nullptrs
  int i = 0;
  std::for_each(std::begin(nodes_), std::end(nodes_),
      [this, &ret, &i]
      (const node_iter_type &pnode) {
    if (pnode != nullptr) {
      auto &my_node = llvm::cast<node_type>(*pnode);
      ret.addNode(my_node);
    } else {
      ret.nodes_.emplace_back(nullptr);
    }
    i++;
  });

  i = 0;
  std::for_each(std::begin(edges_), std::end(edges_),
      [this, &ret, &i]
      (const edge_iter_type &pedge) {
    // llvm::dbgs() << "Cloning edge: " << i << "\n";
    // llvm::dbgs() << "pedge is: " << pedge.get() << "\n";
    if (pedge != nullptr) {
      // llvm::dbgs() << "not nullptr!\n";
      auto &my_edge = llvm::cast<edge_type>(*pedge);

      assert(checkEdge(EdgeID(i)));
      ret.addEdge(my_edge);
    } else {
      // llvm::dbgs() << "nullptr!\n";
      // Add in a nullptr, to keep the edges in sync
      ret.edges_.push_back(nullptr);
    }

    i++;
  });

  // Now, replicate node_mapping
  // Node map should be empty at this point, so I can clone it
  assert(ret.node_map_.size() == 0);
  std::for_each(node_map_.begin(), node_map_.end(),
      [this, &ret] (const std::pair<const id_type, NodeID> &pr) {
    ret.node_map_.emplace(pr.first, pr.second);
  });

  return std::move(ret);
}
//}}}

// Private helpers {{{
// SCC visit {{{
// Use Tarjan's method to calculate SCCs for this graph
// SCC wrapper

template <typename id_type>
void SEG<id_type>::sccStrongconnect(
    std::vector<SCCData> &scc_data,
    NodeID id, int &index,
    std::stack<NodeID> &st,
    SEG &ret) const {

  SCCData &data = scc_data.at(id.val());
  data.setIndex(index);
  data.setLowlink(index);
  data.setOnStack(true);
  st.push(id);

  index++;


  auto &node = getNode<UnifyNode<id_type>>(id);
  for (EdgeID succ_edge_id : node.succs()) {
    auto &succ_edge = getEdge(succ_edge_id);
    auto &succ_node = getNode(succ_edge.dest());
    auto succ_id = succ_node.id();

    auto &succ_data = scc_data.at(succ_id.val());

    if (succ_data.index() == SCCData::invalidIndex) {
      sccStrongconnect(scc_data, succ_id, index, st, ret);
      data.setLowlink(std::min(data.lowlink(), succ_data.lowlink()));
    } else if (succ_data.onStack()) {
      data.setLowlink(std::min(data.lowlink(), succ_data.index()));
    }
  }

  // If node is a root node
  // FIXME: need to de-duplicate edges...
  if (data.lowlink() == data.index()) {
    // Copy node into scc, as our scc root
    auto &rep = ret.getNode<UnifyNode<id_type>>(node.id());

    while (true) {
      auto &grp = ret.getNode<UnifyNode<id_type>>(st.top());
      st.pop();

      if (grp == rep) {
        break;
      }

      scc_data.at(grp.id().val()).setOnStack(false);

      // Unite all of the SCCs with the one we just made
      rep.unite(ret, grp);
    }
  }
}

template <typename id_type>
void SEG<id_type>::createSCC() {
  int index = 0;

  // Create SCC data for each node:
  std::vector<SCCData> data(nodes_.size());

  // Create our required stack of visited nodes
  std::stack<NodeID> st;

  std::for_each(begin(), end(),
      [this, &data, &index, &st]
      (node_iter_type &pnode) {
    if (pnode != nullptr) {
      sccStrongconnect(data, pnode->id(), index, st, *this);
    }
  });
}
//}}}
//}}}
//}}}

#endif  // INCLUDE_SEG_H_
