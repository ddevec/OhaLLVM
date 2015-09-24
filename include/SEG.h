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


// Forward decl for graph!
class SEG;

// Enum For llvm RTTI {{{
enum class NodeKind {
  // DUGNodes
  DUGNode,
  AllocNode,
  PartNode,
  LoadNode,
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
  UnifyEnd
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
    typedef ID<node_id, int32_t, -1> NodeID;

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

        std::vector<NodeID> &preds() {
          return preds_;
        }

        const std::vector<NodeID> &preds() const {
          return preds_;
        }

        std::vector<NodeID> &succs() {
          return succs_;
        }

        const std::vector<NodeID> &succs() const {
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
        bool addSucc(NodeID id) {
          succs().push_back(id);
          return true;
        }

        void uniqueList(SEG &graph, std::vector<NodeID> &list) {
          // Convert to all reps
          std::transform(std::begin(list), std::end(list), std::begin(list),
              [&graph] (NodeID id) {
            auto rep = graph.getRep(id);
            assert(&graph.getNode(rep) != nullptr);
            return graph.getRep(id);
          });

          // Make reps unique
          std::sort(std::begin(list), std::end(list));
          auto it = std::unique(std::begin(list), std::end(list));
          list.erase(it, std::end(list));
        }

        void removeDuplicatePreds(SEG &graph) {
          // First update all edges to be reps:
          uniqueList(graph, preds());
        }

        void removeDuplicateSuccs(SEG &graph) {
          uniqueList(graph, succs());
        }

        bool addPred(NodeID id) {
          preds().push_back(id);
          return true;
        }


        void removeFromList(SEG &graph, NodeID id, std::vector<NodeID> &list) {
          auto rep_id = graph.getRep(id);
          auto it = std::remove_if(std::begin(list), std::end(list),
              [&rep_id, &graph] (NodeID list_id) {
            return (graph.getRep(list_id) == rep_id);
          });
          list.erase(it, std::end(list));
        }

        void removeSucc(SEG &graph, NodeID id) {
          removeFromList(graph, id, succs());
        }

        void removePred(SEG &graph, NodeID id) {
          removeFromList(graph, id, preds());
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
        virtual void print_label(llvm::raw_ostream &,
            const ObjectMap &) const { }
        //}}}

        // Actual unite functionality {{{
        virtual void unite(SEG &graph, Node &n) {
          assert(operator!=(n));
          // Retarget all edges pointing towards n
          auto &preds = n.preds();
          std::for_each(std::begin(preds), std::end(preds),
              [this, &graph, &n](NodeID pred_id) {
            pred_id = graph.getRep(pred_id);

            auto pred_edge = std::make_pair(pred_id, n.id());
            // Create a new edge which points to me
            auto new_edge = std::make_pair(pred_id, id());

            // properly handle ptr to self
            if (pred_id == n.id()) {
              new_edge.first = new_edge.second;
            }

            // Only retarget the edge (add it to our edge set), if the new edge
            //   isn't a pointer to self, (unless the old edge was a
            //   pointer to self)
            if (pred_edge.first == pred_edge.second ||
                  new_edge.first != new_edge.second) {
              graph.addEdge(new_edge.first, new_edge.second);
            }
          });

          // And all edges from n
          // std::set<NodeID> succs;
          // succs.insert(std::begin(n.succs()), std::end(n.succs()));
          auto &succs = n.succs();
          std::for_each(std::begin(succs), std::end(succs),
              [this, &graph, &n](NodeID succ_id) {
            succ_id = graph.getRep(succ_id);
            auto pred_edge = std::make_pair(n.id(), succ_id);
            auto new_edge = std::make_pair(id(), succ_id);

            if (succ_id == n.id()) {
              new_edge.second = new_edge.first;
            }

            // If the old edge wasn't a pointer to self, and the new edge is a
            // pointer to self, don't retarget it, just remove it
            if (pred_edge.first == pred_edge.second ||
                  new_edge.first != new_edge.second) {
              graph.addEdge(new_edge.first, new_edge.second);
            }
          });

          // We have to clear the node's reps, so they aren't deleted,
          //   because we just merged them!
          n.rep_ = id();
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
        std::vector<NodeID> preds_;
        std::vector<NodeID> succs_;
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

          return std::move(tmp);
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

          return std::move(tmp);
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
          llvm::dbgs() << "topo iterator create\n";

          for (auto itr = std::begin(graph), en = std::end(graph);
              itr != en; ++itr) {
            auto &node = *(*itr);

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
        void visit(const SEG &graph, std::set<NodeID> &mark,
            const Node &node, bool reverse, bool print = false) {
          // ddevec -- TODO: Check for cycles???
          if (mark.count(node.id()) == 0) {
            // For cycles...
            mark.insert(node.id());

            auto &succs = node.succs();
            std::for_each(std::begin(succs), std::end(succs),
                [this, &graph, &mark, reverse, print](NodeID succ_id) {
              visit(graph, mark, graph.getNode(succ_id), reverse);
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
    // Adds edge of edge_type between two nodes
    bool addEdge(NodeID src, NodeID dest) {
      // Ensure that a node exists for each edge point..
      auto &src_node = getNode(src);
      auto &dest_node = getNode(dest);

      // Add succ/pred info for src/dest
      src_node.addSucc(dest);
      dest_node.addPred(src);

      return true;
    }

    void removeEdge(NodeID src_id, NodeID dest_id) {
      auto &src = getNode(src_id);
      auto &dest = getNode(dest_id);

      // Remove the pointer from src
      src.removeSucc(*this, dest_id);

      // Remove the pointer from dest
      dest.removePred(*this, src_id);
    }

    void retargetEdge(const std::pair<NodeID, NodeID> &orig,
        const std::pair<NodeID, NodeID> &new_target) {
      // Update edge src/dest

      // Fix up for equivalence between multiple edges?
      auto &src = getNode(orig.first);
      auto &dest = getNode(orig.second);

      // Actually add the edge to the new source and dest
      // llvm::dbgs() << "removing succ from src: " << src.id() << "\n";
      src.removeSucc(*this, orig.second);
      // llvm::dbgs() << "removing pred from dest: " << dest.id() << "\n";
      dest.removePred(*this, orig.first);

      auto &new_src = getNode(new_target.first);
      auto &new_dest = getNode(new_target.second);

      new_src.addSucc(new_target.second);
      new_dest.addPred(new_target.first);
    }

    void cleanEdges() {
      for (auto &pnode : nodes_) {
        if (pnode != nullptr) {
          pnode->removeDuplicateSuccs(*this);
          pnode->removeDuplicatePreds(*this);
        }
      }
    }

    //}}}

    // Node Manipulation {{{
    // contructs new node of node_type and inserts it into our node list
    template <typename node_type>
    void addNode(const node_type &nd) {
      nodes_.emplace_back(new node_type(nd));
    }

    template <typename node_type, typename... va_args>
    NodeID addNode(va_args&&... args) {
      auto node_id = NodeID(nodes_.size());
      nodes_.emplace_back(new node_type(node_id,
            std::forward<va_args>(args)...));

      return node_id;
    }

    void checkNode() {
      assert(!nodes_.at(6)->isRep());
    }

    void removeNode(NodeID id) {
      auto &node = getNode(id);

      // Remove all edges to this node
      // We need a temp container, as we can't remove while iterating...

      std::set<NodeID> preds;
      preds.insert(std::begin(node.preds()), std::end(node.preds()));
      std::for_each(std::begin(preds), std::end(preds),
          [this, &id](NodeID pred_id) {
        auto &pred_node = getNode(pred_id);
        pred_node.removeSucc(*this, id);
      });

      // Remove all edges from this node
      std::set<NodeID> succs;
      succs.insert(std::begin(node.succs()), std::end(node.succs()));
      std::for_each(std::begin(succs), std::end(succs),
          [this, &id](NodeID succ_id) {
        // Don't do pointer to self... that was already done
        auto &succ_node = getNode(succ_id);
        succ_node.removePred(*this, id);
      });

      // llvm::dbgs() << "calling nodes_.erase on id: " << id << "\n";

      // Delete the node
      nodes_.at(node.id().val()).reset(nullptr);
    }

    //}}}
    //}}}

    // Accessors {{{

    // Gets the node, or creates it if it doesn't exist.  Creation uses the
    // default constructor for the node type
    size_t getNumNodes() const {
      return nodes_.size();
    }

    NodeID getRep(NodeID id) const {
      auto ret = id;
      auto &nd = nodes_.at(id.val());
      if (nd == nullptr) {
        return NodeID::invalid();
      }

      if (!nd->isRep()) {
        ret = getRep(nd->rep());
      }

      return ret;
    }

    NodeID getRep(NodeID id) {
      auto ret = id;
      auto &nd = nodes_.at(id.val());
      if (nd == nullptr) {
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

      auto &pnd = nodes_.at(rep.val());

      return llvm::cast<node_type>(pnd.get());
    }

    template <typename node_type = Node>
    node_type *tryGetNode(NodeID id) const {
      auto rep = getRep(id);
      if (rep == NodeID::invalid()) {
        return nullptr;
      }

      auto &pnd = nodes_.at(rep.val());

      return llvm::cast<node_type>(pnd.get());
    }

    template <typename node_type = Node>
    node_type &getNode(NodeID id) {
      auto rep = getRep(id);

      auto &pnd = nodes_.at(rep.val());
      assert(pnd != nullptr);

      assert(pnd->id() == rep);

      return llvm::cast<node_type>(*pnd);
    }

    template <typename node_type = Node>
    const node_type &getNode(NodeID id) const {
      auto rep = getRep(id);

      auto &pnd = nodes_.at(rep.val());
      assert(pnd != nullptr);

      assert(pnd->id() == rep);

      return llvm::cast<node_type>(*pnd);
    }

    void createSCC() {
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

    // Debug functions {{{
    void printDotFile(const std::string &filename,
        const ObjectMap &omap) const {
      std::ofstream ostm(filename, std::ofstream::out);
      llvm::raw_os_ostream ofil(ostm);
      printDotHeader(ofil);
      std::for_each(begin(), end(),
          [&ofil, &omap]
          (const node_iter_type &pnode) {
        const Node &node = *pnode;
        std::string idNode = idToString(node.id());

        ofil << "  " << idNode << " [label=\"";
        node.print_label(ofil, omap);
        ofil << "\"" << " shape=box" << "];\n";
      });

      std::for_each(begin(), end(),
          [this, &ofil, &omap]
          (const node_iter_type &pnode) {
        if (pnode != nullptr) {
          auto src = pnode->id();
          for (auto dest_id : pnode->succs()) {
            std::string idNode1 = idToString(src);
            std::string idNode2 = idToString(dest_id);

            ofil << "  " << idNode1 << " -> " << idNode2 <<
              " [label=\"";
            // We don't label edges anymore...
            // edge.print_label(ofil, omap);
            ofil << "\"];\n";
          }
        }
      });
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
      SCCData &data = scc_data.at(id.val());
      data.setIndex(index);
      data.setLowlink(index);
      data.setOnStack(true);
      st.push(id);

      index++;


      auto &node = getNode(id);
      for (auto succ_id : node.succs()) {
        // Update to rep...
        succ_id = getRep(succ_id);
        auto &succ_data = scc_data.at(succ_id.val());

        if (succ_data.index() == SCCData::invalidIndex) {
          sccStrongconnect(scc_data, succ_id, index, st, ret);
          data.setLowlink(std::min(data.lowlink(), succ_data.lowlink()));
        } else if (succ_data.onStack()) {
          data.setLowlink(std::min(data.lowlink(), succ_data.index()));
        }
      }

      // If node is a root node
      if (data.lowlink() == data.index()) {
        // Copy node into scc, as our scc root
        auto &rep = ret.getNode(node.id());

        while (true) {
          auto &grp = ret.getNode(st.top());
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
    virtual void print_label(llvm::raw_ostream &,
        const ObjectMap &) const { }

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

  std::for_each(begin(), end(),
      [this, &ret, &i]
      (const node_iter_type &pnode) {
    if (pnode != nullptr) {
      auto src_id = pnode->id();
      for (auto dest_id : pnode->succs()) {
        ret.addEdge(src_id, dest_id);
      }
    }
  });

  return std::move(ret);
}
//}}}

// Private helpers {{{
// SCC visit {{{
// Use Tarjan's method to calculate SCCs for this graph
// SCC wrapper

//}}}
//}}}
//}}}

#endif  // INCLUDE_SEG_H_
