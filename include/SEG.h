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
#include <memory>
#include <queue>
#include <set>
#include <stack>
#include <string>
#include <utility>
#include <vector>

#include "include/Debug.h"
#include "include/util.h"

class ValueMap;

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

static void printDotHeader(dbg_ostream &ofil) {
  ofil << "digraph graphname {\n";
}

static void printDotFooter(dbg_ostream &ofil) {
  // We use endl here, so the file will force flush
  ofil << "}" << "\n";
}
//}}}

// Class representing the Sparse Evaluation Graph used for Ramalingams
// (ComputeSSA)
// This class is actually used at several different levels, with different id
// mappings, so its templated to be generic for that (for example with
// ObjID->ObjID in 1:1 mapping, or PEid->ObjID)


// Forward decl for graph!
class SEG;

// Enum For llvm RTTI {{{
enum class NodeKind {
  // DUGNodes
  DUGNode,
  AllocNode,
  ConstNode,
  PartNode,
  LoadNode,
  ConstPartNode,
  StoreNode,
  PhiNode,
  GlobalInitNode,
  PartNodeEnd,
  CopyNode,
  DUGNodeEnd,

  // Unify Nodes
  Unify,
  HUNode,
  CFGNode,
  UnifyEnd,

  OptNode,
  HVNNode,
  HCDNode,
  OptNodeEnd
};

enum class EdgeKind {
  Constraint,
  StoreConstraint,
  LoadConstraint,
  ConstraintEnd,
  DUG,
  CFGEdge,
  HUEdge
};
//}}}

class SEG {
  //{{{
 public:
    // Typedefs {{{
    struct node_id { };
    typedef util::ID<node_id, int32_t, -1> NodeID;
    //}}}

    // Constructors {{{
    // Copy/move {{{
    SEG(const SEG &) = delete;
    SEG(SEG &&) = default;

    SEG &operator=(const SEG &) = delete;
    SEG &operator=(SEG &&) = default;
    //}}}
    //}}}

    // Node class {{{
    class Node {
      //{{{
     public:
        // Constructors {{{
        Node(NodeKind kind, NodeID node_id) : kind_(kind),
          id_(node_id), rep_(node_id) { }

        Node(const Node &) = default;
        Node(Node &&) = default;

        Node &operator=(const Node &) = default;
        Node &operator=(Node &&) = default;
        //}}}

        // Comparison operators {{{
        bool operator==(const Node &n) {
          return id_ == n.id_;
        }

        bool operator!=(const Node &n) {
          return id_ != n.id_;
        }

        bool operator<(const Node &n) {
          return id_ < n.id_;
        }
        //}}}

       // Inertnal classes {{{
        class EdgeSet {
          //{{{
         public:
            EdgeSet() = default;
            explicit EdgeSet(std::vector<NodeID> v) : nodes_(std::move(v)) { }

            EdgeSet(const EdgeSet &) = default;
            EdgeSet &operator=(const EdgeSet &) = delete;
            EdgeSet(EdgeSet &&) = default;
            EdgeSet &operator=(EdgeSet &&) = default;

            void insert(NodeID id) {
              nodes_.push_back(id);
            }

            void insert(const EdgeSet &rhs) {
              nodes_.insert(std::end(nodes_),
                  std::begin(rhs.nodes_), std::end(rhs.nodes_));
            }

            void erase(NodeID id) {
              auto it = std::find(std::begin(nodes_), std::end(nodes_), id);
              if (it != std::end(nodes_)) {
                *it = nodes_.back();
                nodes_.pop_back();
              }
            }

            void clear() {
              nodes_.clear();
            }

            bool has(NodeID id) const {
              return (std::find(std::begin(nodes_), std::end(nodes_), id) !=
                  std::end(nodes_));
            }

            bool empty() const {
              return nodes_.empty();
            }

            int32_t size() const {
              return nodes_.size();
            }

            void unique(SEG &seg) {
              // Convert all ids to rep ids:
              std::vector<NodeID> new_nodes;
              for (auto id : nodes_) {
                id = seg.getRep(id);

                // Ignore invalid/deleted nodes
                if (id == NodeID::invalid()) {
                  continue;
                }

                new_nodes.push_back(id);
              }

              nodes_ = std::move(new_nodes);
              std::sort(std::begin(nodes_), std::end(nodes_));
              auto it = std::unique(std::begin(nodes_), std::end(nodes_));
              nodes_.erase(it, std::end(nodes_));
            }

            bool operator==(const EdgeSet &rhs) const {
              return (nodes_ == rhs.nodes_);
            }

            typedef std::vector<NodeID>::iterator iterator;
            typedef std::vector<NodeID>::const_iterator const_iterator;

            iterator begin() {
              return std::begin(nodes_);
            }

            iterator end() {
              return std::end(nodes_);
            }

            const_iterator begin() const {
              return std::begin(nodes_);
            }

            const_iterator end() const {
              return std::end(nodes_);
            }

            const_iterator cbegin() const {
              return std::begin(nodes_);
            }

            const_iterator cend() const {
              return std::end(nodes_);
            }

         private:
            std::vector<NodeID> nodes_;
          //}}}
        };
        //}}}

        // Accessors {{{
        /*
        struct hasher {
          std::size_t operator()(const Node &nd) const {
            return std::hash<int32_t>(nd.id());
          }
        };
        */
        // For llvm RTTI
        NodeKind getKind() const {
          return kind_;
        }

        void replacePreds(std::vector<NodeID> new_preds) {
          // This should be efficient...
          preds_ = EdgeSet(std::move(new_preds));
        }

        EdgeSet &preds() {
          return preds_;
        }

        const EdgeSet &preds() const {
          return preds_;
        }

        EdgeSet &succs() {
          return succs_;
        }

        const EdgeSet &succs() const {
          return succs_;
        }

        NodeID id() const {
          return id_;
        }
        //}}}

        // LLVM RTTI support {{{
        static bool classof(const Node *) {
          return true;
        }
        //}}}

        // Modifiers {{{
        void unique(SEG &seg) {
          preds().unique(seg);
          succs().unique(seg);
        }

        void addSucc(SEG &, NodeID id) {
          succs().insert(id);
        }

        void addPred(SEG &, NodeID id) {
          preds().insert(id);
        }

        void removeSucc(SEG &, NodeID id) {
          succs().erase(id);
        }

        void removePred(SEG &, NodeID id) {
          preds().erase(id);
        }
        //}}}

        // Iterators {{{
        typedef typename std::vector<NodeID>::iterator iterator;
        typedef typename std::vector<NodeID>::const_iterator const_iterator;

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
        virtual void print_label(dbg_ostream &,
            const ValueMap &) const { }
        //}}}

        // Actual unite functionality {{{
        virtual void unite(SEG &seg, Node &n) {
          assert(operator!=(n));
          // Retarget all edges pointing towards n
          // preds().insert(n.preds());
          // Make sure to handle pointers to self though...
          auto my_rep = seg.getRep(id());
          for (auto dest_id : n.preds()) {
            dest_id = seg.getRep(dest_id);

            // Don't add any edges from them that pointed to me
            if (dest_id != my_rep &&
                dest_id != NodeID::invalid()) {
              preds().insert(dest_id);
            }
          }

          // And all edges from n
          succs().insert(n.succs());
          for (auto dest_id : n.succs()) {
            dest_id = seg.getRep(dest_id);

            // Don't add any edges from them that pointed to me
            if (dest_id != my_rep &&
                dest_id != NodeID::invalid()) {
              succs().insert(dest_id);
            }
          }

          // We have to clear the node's reps, so they aren't deleted,
          //   because we just merged them!
          n.setRep(id());
          assert(n.rep_ != NodeID::invalid());
          n.preds().clear();
          n.succs().clear();
        }
        //}}}

        // Accessors: {{{
        // Required for unify node:
        NodeID rep() const {
          return rep_;
        }

        void setRep(NodeID new_rep) {
          rep_ = new_rep;
        }

        bool isRep() const {
          return rep_ == id();
        }
        //}}}

     private:
        // Private data {{{
        // For llvm RTTI
        const NodeKind kind_;

        // Used to determine the node's unique id
        NodeID id_;

        // Used to manage representative nodes for uniting/merging nodes
        NodeID rep_;

        //}}}

     protected:
        // Protected data {{{
        // We hold references to our pred and successor nodes
        // std::vector<NodeID> preds_;
        // std::vector<NodeID> succs_;
        EdgeSet preds_;
        EdgeSet succs_;
        //}}}
      //}}}
    };
    //}}}

    // Iterators {{{
    // Typedefs {{{
    typedef std::unique_ptr<Node> node_iter_type;

    typedef typename std::vector<NodeID>::iterator
      scc_iterator;
    typedef typename std::vector<NodeID>::const_iterator
      const_scc_iterator;

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
            while (itr_ != end_ && (*itr_ == nullptr || !(*itr_)->isRep())) {
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

        pointer operator->() const {
          auto ret = itr_.operator->();
          assert(ret != nullptr);
          return ret;
        }

        node_iterator &operator--() {
          --itr_;
          while (itr_ != end_ && (*itr_ == nullptr || !(*itr_)->isRep())) {
            --itr_;
          }

          return *this;
        }

        node_iterator operator--(int) {
          node_iterator tmp(*this);
          --itr_;

          while (itr_ != end_ && (*itr_ == nullptr || !(*itr_)->isRep())) {
            --itr_;
          }

          return tmp;
        }

        node_iterator &operator++() {
          ++itr_;

          while (itr_ != end_ && (*itr_ == nullptr || !(*itr_)->isRep())) {
            ++itr_;
          }

          return *this;
        }

        node_iterator operator++(int) {
          node_iterator tmp(*this);
          ++itr_;

          while (itr_ != end_ && (*itr_ == nullptr || !(*itr_)->isRep())) {
            ++itr_;
          }

          return tmp;
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
            while (itr_ != end_ && (*itr_ == nullptr || !(*itr_)->isRep())) {
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

        const std::unique_ptr<Node> &operator*() const {
          auto &ret = itr_.operator*();
          assert(ret != nullptr);
          return ret;
        }

        const std::unique_ptr<Node> &operator->() const {
          auto &ret = *itr_.operator->();
          assert(ret != nullptr);
          return ret;
        }

        const_node_iterator &operator--() {
          --itr_;
          while (itr_ != end_ && (*itr_ == nullptr || !(*itr_)->isRep())) {
            --itr_;
          }

          return *this;
        }

        const_node_iterator operator--(int) {
          const_node_iterator tmp(*this);
          --itr_;

          while (itr_ != end_ && (*itr_ == nullptr || !(*itr_)->isRep())) {
            --itr_;
          }

          return tmp;
        }

        const_node_iterator &operator++() {
          ++itr_;

          while (itr_ != end_ && (*itr_ == nullptr || !(*itr_)->isRep())) {
            ++itr_;
          }

          return *this;
        }

        const_node_iterator operator++(int) {
          const_node_iterator tmp(*this);
          ++itr_;

          while (itr_ != end_ && (*itr_ == nullptr || !(*itr_)->isRep())) {
            ++itr_;
          }

          return tmp;
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
        topo_iterator(const SEG &graph, NodeID start_node,
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
        explicit topo_iterator(SEG &graph,
              bool reverse = false) :
            end_(false),
            begin_(true),
            L_(std::make_shared<std::list<NodeID>>()) {
          std::set<NodeID> mark;

          for (auto itr = std::begin(graph), en = std::end(graph);
              itr != en; ++itr) {
            auto &node = *(*itr);

            visit(graph, mark, node, reverse);
          }

          /* NOTE: This assertion doesn't work, because nodes can be
           *    unified, and multieple G entries may point towards the same
           *    Node, which should only be visited once on a topological
           *    traversal
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

        reference operator*() const {
          return itr_.operator*();
        }

        pointer operator->() const {
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

          return tmp;
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

          return tmp;
        }
        //}}}

     private:
        // Private functions {{{
        void visit(const SEG &graph, std::set<NodeID> &mark,
            const Node &node, bool reverse) {
          // ddevec -- TODO: Check for cycles???
          if (mark.count(node.id()) == 0) {
            // For cycles...
            mark.insert(node.id());

            auto &preds = node.preds();

            // Visit each non-null node in the pred graph
            for (auto id : preds) {
              auto pnode = graph.tryGetNode(id);
              if (pnode != nullptr) {
                visit(graph, mark, *pnode, reverse);
              }
            }

            if (reverse) {
              L_->push_front(node.id());
            } else {
              L_->push_back(node.id());
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

    topo_iterator topo_begin(NodeID id) const {
      return topo_iterator(*this, id);
    }

    topo_iterator topo_end(NodeID) const {
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

    //}}}

    // Modifiers {{{
    // Converters to transform between two SEGs {{{
    SEG() = default;

    template <typename node_type>
    SEG clone() const;
    //}}}

    // Edge Manipulation {{{
    bool addSucc(NodeID nd_id, NodeID succ_id) {
      // Ensure that a node exists for each edge point..
      auto &nd = getNode(nd_id);

      // Add succ/pred info for src/dest
      nd.addSucc(*this, succ_id);

      return true;
    }

    bool addPred(NodeID nd_id, NodeID pred_id) {
      // Ensure that a node exists for each edge point..
      auto &nd = getNode(nd_id);

      // Add succ/pred info for src/dest
      nd.addPred(*this, pred_id);

      return true;
    }

    bool addBidirEdge(NodeID src, NodeID dest) {
      // Ensure that a node exists for each edge point..
      auto &src_node = getNode(src);
      auto &dest_node = getNode(dest);

      // Add succ/pred info for src/dest
      src_node.addSucc(*this, dest);
      dest_node.addPred(*this, src);

      return true;
    }

    void removePred(NodeID nd_id, NodeID pred_id) {
      auto &nd = getNode(nd_id);

      // Remove the pointer from dest
      nd.removePred(*this, pred_id);
    }

    void removeSucc(NodeID nd_id, NodeID succ_id) {
      auto &nd = getNode(nd_id);

      // Remove the pointer from dest
      nd.removeSucc(*this, succ_id);
    }

    void removeBidirEdge(NodeID src_id, NodeID dest_id) {
      auto &src = getNode(src_id);
      auto &dest = getNode(dest_id);

      // Remove the pointer from src
      src.removeSucc(*this, dest_id);

      // Remove the pointer from dest
      dest.removePred(*this, src_id);
    }

    void cleanGraph() {
      for (auto &pnode : *this) {
        pnode->unique(*this);
      }
    }

    //}}}

    // Node Manipulation {{{
    // contructs new node of node_type and inserts it into our node list
    template <typename node_type, typename... va_args>
    void replaceNode(NodeID node_id, va_args&&... args) {
      auto &old_node = nodes_[node_id.val()];
      // I don't have logic for this... yet
      assert(old_node->isRep());

      Node::EdgeSet old_preds = std::move(old_node->preds());
      Node::EdgeSet old_succs = std::move(old_node->succs());

      nodes_[node_id.val()] = std::unique_ptr<node_type>(new node_type(node_id,
          std::forward<va_args>(args)...));

      auto &new_node = *nodes_[node_id.val()];

      // Add preds/succs
      auto &new_preds = new_node.preds();
      new_preds = std::move(old_preds);

      auto &new_succs = new_node.succs();
      new_succs = std::move(old_succs);
    }

    template <typename node_type, typename... va_args>
    NodeID addNode(va_args&&... args) {
      auto node_id = NodeID(nodes_.size());
      nodes_.emplace_back(new node_type(node_id,
            std::forward<va_args>(args)...));

      return node_id;
    }

    void tryRemoveNode(NodeID id) {
      if (tryGetNode(id) != nullptr) {
        removeNode(id);
      }
    }

    void removeNode(NodeID id) {
      auto &node = getNode(id);

      // Remove all edges to this node
      for (auto pred_id : node.preds()) {
        auto pred_node = tryGetNode(pred_id);
        if (pred_node != nullptr &&
            pred_node->id() != node.id()) {
          pred_node->removeSucc(*this, id);
        }
      }

      // Remove all edges from this node
      for (auto succ_id : node.succs()) {
        auto succ_node = tryGetNode(succ_id);
        if (succ_node != nullptr &&
            succ_node->id() != node.id()) {
          succ_node->removePred(*this, id);
        }
      }

      // Delete the node
      nodes_.at(node.id().val()).reset(nullptr);
    }

    //}}}
    //}}}

    // Accessors {{{

    // Returns the largest NodeID possible
    size_t getNumNodes() const {
      return nodes_.size();
    }

    NodeID getRep(NodeID id) const {
      auto ret = id;
      auto &nd = nodes_.at(id.val());
      if (nd == nullptr) {
        return NodeID::invalid();
      }

      if (nd->rep() == NodeID::invalid()) {
        return NodeID::invalid();
      }

      if (!nd->isRep()) {
        ret = getRep(nd->rep());
      }

      return ret;
    }

    NodeID getRep(NodeID id) {
      auto ret = id;
      auto &nd = nodes_[id.val()];
      if (nd == nullptr) {
        return NodeID::invalid();
      }

      if (nd->rep() == NodeID::invalid()) {
        return NodeID::invalid();
      }

      if (!nd->isRep()) {
        ret = getRep(nd->rep());
        nd->setRep(ret);
      }

      return ret;
    }

    template <typename node_type = Node>
    node_type *tryGetNode(NodeID id) {
      auto rep = getRep(id);
      if (rep == NodeID::invalid()) {
        return nullptr;
      }

      auto &pnd = nodes_[rep.val()];

      return cast<node_type>(pnd.get());
    }

    template <typename node_type = Node>
    const node_type *tryGetNode(NodeID id) const {
      auto rep = getRep(id);
      if (rep == NodeID::invalid()) {
        return nullptr;
      }

      auto &pnd = nodes_.at(rep.val());

      return cast<node_type>(pnd.get());
    }

    template <typename node_type = Node>
    node_type &getNode(NodeID id) {
      auto rep = getRep(id);

      auto &pnd = nodes_.at(rep.val());
      assert(pnd != nullptr);

      assert(pnd->id() == rep);

      return cast<node_type>(*pnd);
    }

    template <typename node_type = Node>
    const node_type &getNode(NodeID id) const {
      auto rep = getRep(id);

      auto &pnd = nodes_.at(rep.val());
      assert(pnd != nullptr);

      assert(pnd->id() == rep);


      return cast<node_type>(*pnd);
    }

    void createSCC() {
      int index = 0;

      // Create SCC data for each node:
      std::vector<SCCData> data(nodes_.size());

      // Create our required stack of visited nodes
      std::stack<NodeID> st;

      for (auto &pnode : *this) {
        sccStrongconnect(data, pnode->id(), index, st, *this);
      }
    }
    //}}}

    // Debug functions {{{
    void printDotFile(const std::string &filename,
        const ValueMap &omap) {
      // cleanGraph();
#ifndef SPECSFS_IS_TEST
      std::ofstream ostm(filename, std::ofstream::out);
      dbg_ostream ofil(ostm);
#else
      std::ofstream ofil(filename, std::ofstream::out);
#endif
      printDotHeader(ofil);
      for (const auto &pnode : *this) {
        const Node &node = *pnode;
        std::string idNode = idToString(node.id());

        ofil << "  " << idNode << " [label=\"";
        node.print_label(ofil, omap);
        ofil << "\"" << " shape=box" << "];\n";
      }

      for (const auto &pnode : *this) {
        if (pnode != nullptr) {
          auto dest_id = pnode->id();
          for (auto src_id : pnode->preds()) {
            std::string idNode1 = idToString(src_id);
            std::string idNode2 = idToString(dest_id);

            ofil << "  " << idNode1 << " -> " << idNode2 <<
              " [label=\"";
            // We don't label edges anymore...
            // edge.print_label(ofil, omap);
            ofil << "\"];\n";
          }
        }
      }
      printDotFooter(ofil);
    }
    //}}}

 private:
    // Private variables {{{
    // Holds all of the nodes
    std::vector<std::unique_ptr<Node>> nodes_;
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

    void sccStrongconnect(std::vector<SCCData> &scc_data,
        NodeID id, int &index, std::stack<NodeID> &st, SEG &ret) const {
      // dbg << "Strongconnect\n";
      // dbg << "  visit: " << id << "\n";
      // dbg << "  index: " << index << "\n";
      // dbg << "  lowlink: " << index << "\n";
      SCCData &data = scc_data.at(id.val());
      data.setIndex(index);
      data.setLowlink(index);
      data.setOnStack(true);
      st.push(id);

      index++;


      auto &node = getNode(id);
      assert(node.isRep());
      for (auto pred_id : node.preds()) {
        // Update to rep...
        pred_id = getRep(pred_id);

        // We have a node which has been merged/removed, ignore it
        if (pred_id == NodeID::invalid()) {
          continue;
        }

        // dbg << "   checking pred: " << pred_id << "\n";

        auto &pred_data = scc_data.at(pred_id.val());

        if (pred_data.index() == SCCData::invalidIndex) {
          sccStrongconnect(scc_data, pred_id, index, st, ret);
          data.setLowlink(std::min(data.lowlink(), pred_data.lowlink()));
          /*
          dbg << "    invalid Updating lowlink for " << id <<
            " to: " << data.lowlink() << "\n";
          */
        } else if (pred_data.onStack()) {
          data.setLowlink(std::min(data.lowlink(), pred_data.index()));
          /*
          dbg << "    stack Updating lowlink for " << id <<
            " to: " << data.lowlink() << "\n";
          */
        }
      }

      // If node is a root node
      if (data.lowlink() == data.index()) {
        // Copy node into scc, as our scc root
        auto &rep = ret.getNode(node.id());


        while (true) {
          auto &grp = ret.getNode(st.top());
          st.pop();

          // Must clear on-stack status!!!
          scc_data.at(grp.id().val()).setOnStack(false);

          if (grp == rep) {
            break;
          }

          /*
          dbg << "  Merging: " << rep.id() << ", " << grp.id()
            << "\n";
          */

          // Unite all of the SCCs with the one we just made
          rep.unite(ret, grp);
        }
      }
    }
    //}}}
  //}}}
};

class SEGEdge {
  //{{{
 public:
    typedef typename SEG::NodeID NodeID;

    SEGEdge(EdgeKind kind, NodeID src, NodeID dest) :
        kind_(kind), src_(src), dest_(dest) { }

    NodeID src() const {
      return src_;
    }

    NodeID dest() const {
      return dest_;
    }

    // By default print nothing
    virtual void print_label(dbg_ostream &,
        const ValueMap &) const { }

    EdgeKind getKind() const {
      return kind_;
    }

    static bool classof(const SEGEdge *) {
      return true;
    }

    virtual bool operator==(const SEGEdge &rhs) const {
      return src() == rhs.src() && dest() == rhs.dest();
    }

    bool operator!=(const SEGEdge &rhs) const {
      return !operator==(rhs);
    }

    virtual bool operator==(
        const std::reference_wrapper<SEGEdge> &rhs) const {
      // Remove reference wrapper...
      return operator==(rhs.get());
    }

    virtual bool operator<(const SEGEdge &rhs) const {
      if (src() != rhs.src()) {
        return src() < rhs.src();
      }

      return dest() <= rhs.dest();
    }

    friend bool operator<(const std::reference_wrapper<SEGEdge> &lhs,
        const std::reference_wrapper<SEGEdge> &rhs) {
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

// SEG Impl {{{
// SEG clone {{{
template <typename node_type>
SEG SEG::clone() const {
  SEG ret;

  ret.nodes_.resize(nodes_.size());
  // Initialize ret to nullptr
  // We don't use node itr, because we want to include nullptrs
  size_t idx = 0;
  for (auto &pnode : nodes_) {
    if (pnode != nullptr) {
      auto &my_node = cast<node_type>(*pnode);
      ret.nodes_[idx] = std::unique_ptr<node_type>(new node_type(my_node));
    } else {
      ret.nodes_[idx] = nullptr;
    }
    idx++;
  }

  return ret;
}
//}}}

#endif  // INCLUDE_SEG_H_
