/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_ANDERSGRAPH_H_
#define INCLUDE_ANDERSGRAPH_H_

#include <map>
#include <memory>
#include <set>
#include <utility>
#include <vector>

#include "include/ValueMap.h"
#include "include/SolveHelpers.h"

class AndersGraph;
class AndersNode;

// Constraints are associated w/ nodes, and represent edges to be added
// NOTE: edges added by indirect function calls are handled seperately
class AndersCons {
  //{{{
 public:
  typedef ValueMap::Id Id;


  AndersCons(const Constraint &cons) :
    type_(cons.type()), src_(cons.src()), dest_(cons.dest()),
    offs_(cons.offs()) { }
  AndersCons(AndersCons &&) = default;
  AndersCons(const AndersCons &) = default;

  AndersCons &operator=(AndersCons &&) = default;
  AndersCons &operator=(const AndersCons &) = default;

  // Accessors {{{
  Id src() const {
    return src_;
  }

  Id dest() const {
    return dest_;
  }

  int32_t offs() const {
    return offs_;
  }

  ConstraintType type() const {
    return type_;
  }
  //}}}

  void process(AndersGraph &graph, Worklist<Id> &wl,
      const std::vector<uint32_t> &priority, const PtstoSet &update) const;

  friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
      const AndersCons &cons) {
    o << "{ ";
    switch (cons.type_) {
      case ConstraintType::Store:
        o << "Store";
        break;
      case ConstraintType::Load:
        o << "Load";
        break;
      case ConstraintType::Copy:
        o << "Copy";
        break;
      case ConstraintType::AddressOf:
        o << "Alloc";
        break;
      default:
        llvm_unreachable("Unknown cons type");
    }

    o << " s: " << cons.src_ << ", d: " << cons.dest_ << ", o: " << cons.offs_
      << " }";

    return o;
  }

 protected:
  // Constructor {{{
  AndersCons(ConstraintType type, Id src, Id dest) :
    AndersCons(type, src, dest, 0) { }
  AndersCons(ConstraintType type, Id src, Id dest, int32_t offs) :
      type_(type), src_(src), dest_(dest), offs_(offs) { }
  //}}}

 private:
  ConstraintType type_;

  Id src_;
  Id dest_;
  int32_t offs_;
  //}}}
};

class AndersNode {
  //{{{
 public:
  typedef ValueMap::Id Id;

  // Constructors {{{
  explicit AndersNode(Id id) : id_(id) { }

  AndersNode(const AndersNode &) = delete;
  AndersNode(AndersNode &&) = default;

  AndersNode &operator=(const AndersNode &) = delete;
  AndersNode &operator=(AndersNode &&) = delete;
  //}}}

  // Accessors {{{
  Id id() const {
    return id_;
  }

  PtstoSet &ptsto() {
    return ptsto_;
  }

  void clearOldPtsto() {
    oldPtsto_.clear();
  }

  const Bitmap &copySuccs() const {
    return copySuccs_;
  }

  std::vector<std::pair<Id, int32_t>> &gepSuccs() {
    return gepSuccs_;
  }

  PtstoSet getUpdateSet() {
    if (oldPtsto_ == ptsto_) {
      return PtstoSet();
    }

    auto ret = ptsto_ - oldPtsto_;
    // auto ret = ptsto_;

    oldPtsto_ = ptsto_;

    return ret;
  }

  std::vector<AndersCons> &constraints() {
    return constraints_;
  }

  std::vector<std::tuple<CallInfo, CsFcnCFG::Id, PtstoSet>> &
  indirCalls() {
    return indirCalls_;
  }
  //}}}

  // Modifiers {{{
  void setCopySuccs(Bitmap new_copy_succs) {
    copySuccs_ = std::move(new_copy_succs);
  }

  bool hasCopyEdge(Id dest_id) {
    return copySuccs_.test(dest_id.val());
  }

  bool addCopyEdge(Id dest_id) {
    bool ret = false;
    // Don't add edges to/from int/null value, or to yourself
    // These should be done externally... I think
    if (id() != ValueMap::IntValue &&
        dest_id != ValueMap::IntValue &&
        id() != ValueMap::NullValue &&
        dest_id != ValueMap::NullValue &&
        id() != dest_id) {
      ret = copySuccs_.test_and_set(dest_id.val());
    }

    return ret;
  }

  bool addCopyEdges(const PtstoSet &pts) {
    // Just skip these in the sorted vector...
    // IF they are at the start of the object space
    assert(ValueMap::NullValue.val() < 2);
    assert(ValueMap::IntValue.val() < 2);

    auto begin_it = std::begin(pts);
    auto end_it = std::end(pts);
    // FIXME: Hacky
    while (begin_it != end_it && *begin_it < ValueMap::Id(2)) {
      ++begin_it;
    }

    return copySuccs_.addSorted(begin_it, std::end(pts));
  }

  void addCons(const Constraint &cons) {
    addCons(AndersCons(cons));
  }

  void addCons(AndersCons cons) {
    constraints_.emplace_back(std::move(cons));
  }

  bool addSucc(Id obj, int32_t offs) {
    if (offs == 0) {
      return copySuccs_.test_and_set(obj.val());
    } else {
      gepSuccs_.emplace_back(obj, offs);
      return true;
    }
  }

  void addIndirCall(const CallInfo &ci, CsFcnCFG::Id cg_id) {
    indirCalls_.emplace_back(ci, cg_id, PtstoSet());
  }
  //}}}

  // Remove any unneeded info, now that anders has finished
  void cleanup() {
    constraints_.clear();
    copySuccs_.clear();
    gepSuccs_.clear();
    oldPtsto_.clear();
  }

  // And the visit function!
  void visit(AndersGraph &graph, Worklist<Id> &wl,
      const std::vector<uint32_t> &prioirty);

 private:
  // Allows AndersGraph to call merge on a node
  friend class AndersGraph;

  void merge(AndersNode &rhs) {
    // Move their constraints to our constraints.
    constraints_.reserve(rhs.constraints_.size() + constraints_.size());
    std::move(std::begin(rhs.constraints_), std::end(rhs.constraints_),
        std::back_inserter(constraints_));
    rhs.constraints_.clear();

    copySuccs_ |= rhs.copySuccs_;

    gepSuccs_.insert(std::end(gepSuccs_),
        std::begin(rhs.gepSuccs_), std::end(rhs.gepSuccs_));

    ptsto_ |= rhs.ptsto_;

    // clear our oldPtsto_ so we propagate info to new gepSuccs_ on our
    //    next iteration
    oldPtsto_.clear();

    // Free up some memory
    rhs.ptsto_.clear();
    rhs.oldPtsto_.clear();
    rhs.copySuccs_.clear();
    rhs.gepSuccs_.clear();
  }

  // Private Data {{{
  const Id id_;

  std::vector<AndersCons> constraints_;

  // Edges:
  // BddSet?
  Bitmap copySuccs_;
  std::vector<std::pair<Id, int32_t>> gepSuccs_;

  // To support indirect calls:
  //   The indirect calls whose dest(s) ar determined by this node's ptsto
  std::vector<std::tuple<CallInfo, CsFcnCFG::Id, PtstoSet>> indirCalls_;

  PtstoSet ptsto_;
  PtstoSet oldPtsto_;
  //}}}

  //}}}
};

// Graph containing a node per Id (value)
class AndersGraph {
  //{{{
 public:
  typedef ValueMap::Id Id;

  AndersGraph() = default;

  AndersGraph(const AndersGraph &) = delete;
  AndersGraph(AndersGraph &&) = delete;

  AndersGraph &operator=(const AndersGraph &) = delete;
  AndersGraph &operator=(AndersGraph &&) = delete;

  void init(Cg &main_cg, BasicFcnCFG &static_cfg,
      CgCache *cache, CgCache *call_cache) {
    cg_ = &main_cg;
    staticCFG_ = &static_cfg;
    cgCache_ = cache;
    callCgCache_ = call_cache;
  }

  bool isRep(const AndersNode &node) {
    return isRep(node.id());
  }

  bool isRep(Id id) {
    return reps_.find(id) == id;
  }

  Id getRep(Id id) {
    return reps_.find(id);
  }

  AndersNode *tryGetNode(Id id) {
    if (static_cast<size_t>(id.val()) >= nodes_.size()) {
      return nullptr;
    }

    return &getNode(id);
  }

  AndersNode &getNode(Id id) {
    auto rep = getRep(id);

    return nodes_[rep.val()];
  }

  size_t size() const {
    return nodes_.size();
  }


  void fill();

  void merge(AndersNode &n1, AndersNode &n2);

  // Removes any unneeded information after solve completes
  void cleanup() {
    for (auto &node : *this) {
      node.cleanup();
    }
  }

  typedef std::vector<AndersNode>::iterator iterator;

  iterator begin() {
    return std::begin(nodes_);
  }

  iterator end() {
    return std::end(nodes_);
  }

  Cg &cg() {
    return *cg_;
  }

  BasicFcnCFG &staticCFG() {
    return *staticCFG_;
  }

  std::pair<std::vector<Id>,
    std::map<const llvm::Function *, std::pair<CallInfo, CsFcnCFG::Id>>>
  mapIn(const llvm::Function *fcn);

  std::vector<Id>
  addExternalCall(llvm::ImmutableCallSite &cs,
      const llvm::Function *callee_fcn,
      const CallInfo &caller_ci);

 private:
  Id addConstraint(const Constraint &cons);
  void addIndirConstraint(
    const std::tuple<Cg::Id, CallInfo, CsFcnCFG::Id> &tup);
  std::vector<Id> updateGraphForCons(
  const std::map<const llvm::Function *, std::pair<CallInfo, CsFcnCFG::Id>> &);

  // Nodes in the graph, one per object
  std::vector<AndersNode> nodes_;
  util::UnionFind<Id> reps_;

  // Cache of functions
  CgCache *cgCache_;
  // Cache of functions after populating direct callsites
  CgCache *callCgCache_;

  Cg *cg_;
  BasicFcnCFG *staticCFG_;

  size_t prevCons_ = 0;
  size_t prevIndirCons_ = 0;
  //}}}
};

#endif  // INCLUDE_ANDERSGRAPH_H_
