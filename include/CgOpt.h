/*
 * Copyright (C) 2016 David Devecsery
 */

#ifndef INCLUDE_CGOPT_H_
#define INCLUDE_CGOPT_H_

#include <algorithm>
#include <map>
#include <set>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

#include "include/util.h"

template<typename id_type>
class PredNode {
  //{{{
 public:
  typedef id_type Id;
  PredNode() = default;

  const std::vector<Id> &preds() const {
    return preds_;
  }

  void addPred(Id pred) {
    preds_.push_back(pred);
  }

  void unite(PredNode &rhs) {
    preds_.insert(std::end(preds_), std::begin(rhs.preds_),
        std::end(rhs.preds_));
    rhs.preds_.clear();
  }

  void cleanPreds() {
    std::sort(std::begin(preds_), std::end(preds_));
    auto un_it = std::unique(std::begin(preds_), std::end(preds_));
    preds_.erase(un_it, std::end(preds_));
  }

  void clearPreds() {
    preds_.clear();
  }

 private:
  std::vector<Id> preds_;
  //}}}
};

template <typename id_type>
class OptNode : public PredNode<id_type> {
  //{{{
 public:
  typedef typename PredNode<id_type>::Id Id;
  static const int32_t PENonPtr = 0;

  OptNode() = default;

  void addPtsTo(int32_t id) {
    ptsto_.set(id);
  }

  void makeNonPtr() {
    ptsto_.clear();
    ptsto_.set(PENonPtr);
  }

  const util::SparseBitmap<int32_t> &ptsto() const {
    return ptsto_;
  }

  util::SparseBitmap<int32_t> &ptsto() {
    return ptsto_;
  }

  bool indirect() const {
    return indirect_;
  }

  bool ref() const {
    return ref_;
  }

  void setIndirect() {
    indirect_ = true;
  }

  void setRef(Id) {
    ref_ = true;
  }

  bool isNonPtr() {
    auto ret = ptsto().test(PENonPtr);

    // the ptsto count for all non-ptrs should be 1
    // assert(!(ret && ptsto().count() != 1));
    return ret;
  }

  void unite(OptNode &rhs) {
    indirect_ |= rhs.indirect();
    ptsto_ |= rhs.ptsto();
    implEdges_ |= rhs.implEdges_;

    rhs.ptsto_.clear();
    rhs.implEdges_.clear();

    PredNode<id_type>::unite(rhs);
  }

  bool isImplicitPred(Id pred_id) {
    return implEdges_.test(static_cast<int32_t>(pred_id));
  }

  void addImplicitPred(Id pred_id) {
    implEdges_.set(static_cast<int32_t>(pred_id));
    PredNode<id_type>::addPred(pred_id);
  }

 private:
  bool indirect_ = false;
  bool ref_ = false;
  util::SparseBitmap<int32_t> implEdges_;
  util::SparseBitmap<int32_t> ptsto_;
  //}}}
};

template <typename id_type>
class HCDNodeBase : public PredNode<id_type> {
  //{{{
 public:
  typedef typename PredNode<id_type>::Id Id;

  HCDNodeBase() = default;

  bool ref() const {
    return baseId_ == Id::invalid();
  }

  void setRef(Id id) {
    refs_.insert(id);
  }

  const std::set<Id> refs() const {
    return refs_;
  }

  void setBase(Id id) {
    baseId_ = id;
  }

  Id baseId() const {
    return baseId_;
  }

  Id getRep() {
    return baseId_;
  }

  void unite(HCDNodeBase &rhs) {
    refs_.insert(std::begin(rhs.refs_), std::end(rhs.refs_));

    if (rhs.baseId_ != Id::invalid()) {
      baseId_ = rhs.baseId_;
    }

    rhs.refs_.clear();

    PredNode<id_type>::unite(rhs);
  }

 private:
  Id baseId_ = Id::invalid();
  std::set<Id> refs_;
  //}}}
};

class CRTP_Graph {
  //{{{
 private:
  struct id_tag { };

 public:
  typedef util::ID<id_tag, int32_t, -1> Id;
  //}}}
};

// Graph used for HVN and HRU optimizations
template <typename node_type>
class Graph : public CRTP_Graph {
  //{{{
 public:
  typedef CRTP_Graph::Id Id;
  typedef node_type Node;

  Graph() = default;

  Node &getNode(Id id) {
    return nodes_[static_cast<size_t>(getRep(id))];
  }

  Id addNode() {
    Id ret(nodes_.size());
    nodes_.emplace_back();
    if_debug_enabled(auto rep_id =)
      reps_.add();
    assert(rep_id == ret);
    return ret;
  }

  Id merge(Id lhs, Id rhs) {
    auto lhs_rep = getRep(lhs);
    auto rhs_rep = getRep(rhs);
    // DON'T MERGE WITH YOURSELF, IT WILL MAKE YOU SPEND ALL DAY DEBUGGING
    //   SOMETHING STUPID
    if (lhs_rep == rhs_rep) {
      return lhs_rep;
    }
    // I'M STILL SUPER PARANOID
    assert(lhs != rhs);


    auto &lhs_node = getNode(lhs_rep);
    auto &rhs_node = getNode(rhs_rep);
    reps_.merge(lhs_rep, rhs_rep);
    auto rep_id = reps_.find(lhs_rep);
    assert(rep_id == reps_.find(rhs_rep));

    if (rep_id == lhs) {
      lhs_node.unite(rhs_node);
    } else {
      rhs_node.unite(lhs_node);
    }

    return rep_id;
  }

  size_t size() const {
    return nodes_.size();
  }

  Id getRep(Id id) {
    return reps_.find(id);
  }

  Id getId(Node &node) const {
    return Id((reinterpret_cast<intptr_t>(&node) -
        reinterpret_cast<intptr_t>(nodes_.data())) / sizeof(Node));
  }

 private:
  std::vector<Node> nodes_;
  util::UnionFind<Id> reps_;
  //}}}
};

typedef OptNode<CRTP_Graph::Id> HVNNode;
typedef Graph<HVNNode> OptGraph;
typedef OptGraph::Id GraphId;

typedef HCDNodeBase<CRTP_Graph::Id> HCDNode;
typedef Graph<HCDNode> HCDGraph;
typedef HCDGraph::Id HCDGraphId;

#endif  // INCLUDE_CGOPT_H_
