/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_ANDERSHELPERS_H_
#define INCLUDE_ANDERSHELPERS_H_

#include <map>
#include <memory>
#include <set>
#include <utility>
#include <vector>

#include "include/ConstraintGraph.h"
#include "include/ObjectMap.h"
#include "include/SolveHelpers.h"

class AndersGraph;
class AndersNode;
class AndersCons {
  //{{{
 public:
  typedef ObjectMap::ObjID ObjID;

  enum class Kind : int32_t {
    Store,
    Load,
    IndirCall,
    Copy,
    Alloc
  };

  // Accessors {{{
  ObjID src() const {
    return src_;
  }

  ObjID dest() const {
    return dest_;
  }

  int32_t offs() const {
    return offs_;
  }

  Kind getKind() const {
    return kind_;
  }
  //}}}

  virtual void process(AndersGraph &graph, Worklist<AndersNode> &wl,
      const std::vector<uint32_t> &priority, const PtstoSet &update) const;

  friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
      const AndersCons &cons) {
    o << "{ ";
    switch (cons.kind_) {
      case Kind::Store:
        o << "Store";
        break;
      case Kind::Load:
        o << "Load";
        break;
      case Kind::IndirCall:
        o << "IndirCall";
        break;
      case Kind::Copy:
        o << "Copy";
        break;
      case Kind::Alloc:
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
  AndersCons(Kind kind, ObjID src, ObjID dest) :
    AndersCons(kind, src, dest, 0) { }
  AndersCons(Kind kind, ObjID src, ObjID dest, int32_t offs) :
      kind_(kind), src_(src), dest_(dest), offs_(offs) { }

  AndersCons(AndersCons &&) = default;
  AndersCons(const AndersCons &) = default;

  AndersCons &operator=(AndersCons &&) = default;
  AndersCons &operator=(const AndersCons &) = default;
  //}}}

 private:
  const Kind kind_;

  const ObjID src_;
  const ObjID dest_;
  const int32_t offs_;
  //}}}
};

class AndersStoreCons : public AndersCons {
 public:
  typedef ObjectMap::ObjID ObjID;

  AndersStoreCons(ObjID src, ObjID dest) :
      AndersCons(AndersCons::Kind::Store, src, dest, 0) { }

  void process(AndersGraph &graph, Worklist<AndersNode> &wl,
      const std::vector<uint32_t> &priority,
      const PtstoSet &update) const override;
};

class AndersLoadCons : public AndersCons {
 public:
  typedef ObjectMap::ObjID ObjID;

  AndersLoadCons(ObjID src, ObjID dest) :
      AndersCons(AndersCons::Kind::Load, src, dest, 0) { }

  void process(AndersGraph &graph, Worklist<AndersNode> &wl,
      const std::vector<uint32_t> &priority,
      const PtstoSet &update) const override;
};

class AndersIndirCallCons : public AndersCons {
 public:
  typedef ObjectMap::ObjID ObjID;

  // src is called pointer, dest is ret
  template <typename input_iterator>
  AndersIndirCallCons(ObjID src, ObjID dest,
      input_iterator arg_begin, input_iterator arg_end) :
      AndersCons(AndersCons::Kind::IndirCall, src, dest, 0),
      args_(arg_begin, arg_end) { }

  const std::vector<ObjID> &args() const {
    return args_;
  }

  ObjID ret() const {
    return dest();
  }

  ObjID callee() const {
    return src();
  }

  static bool classof(const AndersCons *c) {
    return c->getKind() == AndersCons::Kind::IndirCall;
  }

  void process(AndersGraph &graph, Worklist<AndersNode> &wl,
      const std::vector<uint32_t> &priority,
      const PtstoSet &update) const override;

 private:
  const std::vector<ObjID> args_;
  const ObjID ret_;
};

class AndersNode {
  //{{{
 public:
  typedef ObjectMap::ObjID ObjID;

  // Constructors {{{
  explicit AndersNode(ObjID id) : id_(id) { }

  AndersNode(const AndersNode &) = delete;
  AndersNode(AndersNode &&) = default;

  AndersNode &operator=(const AndersNode &) = delete;
  AndersNode &operator=(AndersNode &&) = delete;
  //}}}

  // Accessors {{{
  ObjID id() const {
    return id_;
  }

  PtstoSet &ptsto() {
    return ptsto_;
  }

  const Bitmap &copySuccs() const {
    return copySuccs_;
  }

  std::vector<std::pair<ObjID, int32_t>> &gepSuccs() {
    return gepSuccs_;
  }

  /*
  bool updated() const {
    return ptsto_ != oldPtsto_;
  }

  void clearUpdated() {
    oldPtsto_ = ptsto_;
  }
  */

  PtstoSet getUpdateSet() {
    if (oldPtsto_ == ptsto_) {
      return PtstoSet();
    }

    auto ret = ptsto_ - oldPtsto_;
    // auto ret = ptsto_;

    oldPtsto_ = ptsto_;

    return ret;
  }

  std::vector<std::unique_ptr<AndersCons>> &constraints() {
    return constraints_;
  }
  //}}}

  // Modifiers {{{
  void setCopySuccs(Bitmap new_copy_succs) {
    copySuccs_ = std::move(new_copy_succs);
  }

  bool hasCopyEdge(ObjID dest_id) {
    return copySuccs_.test(dest_id.val());
  }

  bool addCopyEdge(ObjID dest_id) {
    bool ret = false;
    // Don't add edges to/from int/null value, or to yourself
    // These should be done externally... I think
    /*
    assert(id() != ObjectMap::IntValue);
    assert(dest_id != ObjectMap::IntValue);
    assert(id() != ObjectMap::NullValue);
    assert(dest_id != ObjectMap::NullValue);
    assert(id() != dest_id);
    */

    if (id() != ObjectMap::IntValue &&
        dest_id != ObjectMap::IntValue &&
        id() != ObjectMap::NullValue &&
        dest_id != ObjectMap::NullValue &&
        id() != dest_id) {
      ret = copySuccs_.test_and_set(dest_id.val());
    }

    return ret;
  }

  bool addCopyEdges(const PtstoSet &pts) {
    // Just skip these in the sorted vector...
    // IF they are at the start of the object space
    assert(ObjectMap::NullValue.val() < 3);
    assert(ObjectMap::IntValue.val() < 3);
    assert(ObjectMap::NullObjectValue.val() < 3);

    auto begin_it = std::begin(pts);
    auto end_it = std::end(pts);
    // FIXME: Hacky
    while (begin_it != end_it && *begin_it < ObjectMap::ObjID(3)) {
      ++begin_it;
    }

    return copySuccs_.addSorted(begin_it, std::end(pts));
  }

  void addCons(std::unique_ptr<AndersCons> cons) {
    constraints_.emplace_back(std::move(cons));
  }

  bool addSucc(ObjID obj, int32_t offs) {
    if (offs == 0) {
      return copySuccs_.test_and_set(obj.val());
    } else {
      gepSuccs_.emplace_back(obj, offs);
      return true;
    }
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
  void visit(AndersGraph &graph, Worklist<AndersNode> &wl,
      const std::vector<uint32_t> &prioirty);

 private:
  // Allows AndersGraph to call merge on a node
  friend class AndersGraph;

  void merge(AndersNode &rhs) {
    // Move their constraints to our constraints.
    std::move(std::begin(rhs.constraints_), std::end(rhs.constraints_),
        std::back_inserter(constraints_));
    rhs.constraints_.clear();

    copySuccs_ |= rhs.copySuccs_;
    gepSuccs_.insert(std::end(gepSuccs_),
        std::begin(rhs.gepSuccs_), std::end(rhs.gepSuccs_));

    ptsto_ |= rhs.ptsto_;

    // Is this unneeded?
    oldPtsto_.clear();

    // Free up some memory
    rhs.ptsto_.clear();
    rhs.oldPtsto_.clear();
    rhs.copySuccs_.clear();
    rhs.gepSuccs_.clear();
  }

  // Private Data {{{
  const ObjID id_;

  std::vector<std::unique_ptr<AndersCons>> constraints_;

  // Edges:
  Bitmap copySuccs_;
  std::vector<std::pair<ObjID, int32_t>> gepSuccs_;

  PtstoSet ptsto_;
  PtstoSet oldPtsto_;
  //}}}

  //}}}
};

// Graph containing a node per ObjID (value)
class AndersGraph {
 public:
  typedef ObjectMap::ObjID ObjID;

  AndersGraph() = default;

  AndersGraph(const AndersGraph &) = delete;
  AndersGraph(AndersGraph &&) = delete;

  AndersGraph &operator=(const AndersGraph &) = delete;
  AndersGraph &operator=(AndersGraph &&) = delete;

  bool isRep(const AndersNode &node) {
    return isRep(node.id());
  }

  bool isRep(ObjID id) {
    return reps_.find(id) == id;
  }

  ObjID getRep(ObjID id) {
    return reps_.find(id);
  }

  AndersNode *tryGetNode(ObjID id) {
    if (static_cast<size_t>(id.val()) >= nodes_.size()) {
      return nullptr;
    }

    return &getNode(id);
  }

  AndersNode &getNode(ObjID id) {
    auto rep = getRep(id);

    return nodes_[rep.val()];
  }

  size_t size() const {
    return nodes_.size();
  }

  void fill(const ConstraintGraph &cg, ObjectMap &omap, llvm::Module &m) {
    // For each constraint destination, make a node.
    ObjID max_id(0);

    // Calculate the max_id used
    for (const auto &[callisnt, call_info] : cg.indirs()) {
      // Setup ret if we return a pointer
      if (call_info.isPointer()) {
        if (callinst > max_id) {
          max_id = callinst;
        }
      }

      for (auto arg_id : call_info) {
        if (arg_id > max_id) {
          max_id = arg_id;
        }
      }
    }

    for (auto &pcons : cg) {
      if (pcons == nullptr) {
        continue;
      }

      if (pcons->dest() > max_id) {
        max_id = pcons->dest();
      }

      if (pcons->src() > max_id) {
        max_id = pcons->src();
      }
    }

    assert(nodes_.size() == 0);
    nodes_.reserve(nodes_.size());
    for (ObjID i(0); i <= max_id; i++) {
      nodes_.emplace_back(ObjID(i));
    }
    reps_ = util::UnionFind<ObjID>(max_id.val()+1);

    // Sanity check, there are no sources greater than max_id?
    if_debug_enabled(
      for (auto &pcons : cg) {
        if (pcons == nullptr) {
          continue;
        }
        assert(pcons->src() <= max_id);
      });

    // UGH, also need to handle "GEPs" constraints, to manage dynamically
    //   indexed structures...
    // For each constraint, add it to the node associated with its source
    for (auto &pcons : cg) {
      if (pcons == nullptr) {
        continue;
      }
      auto &cons = *pcons;

      // Ignore nullvalue alloc/load/store constraints
      if (cons.type() != ConstraintType::Copy &&
           (cons.src() == ObjectMap::NullValue ||
            cons.dest() == ObjectMap::NullValue)) {
        continue;
      }

      // Ignore copy to nullvalue
      if (cons.type() == ConstraintType::Copy &&
          cons.dest() == ObjectMap::NullValue) {
        continue;
      }

      switch (cons.type()) {
        case ConstraintType::Load:
          {
            auto &node = getNode(cons.src());
            node.addCons(std::unique_ptr<AndersCons>(
                  new AndersLoadCons(cons.src(), cons.dest())));
            break;
          }
        case ConstraintType::Store:
          {
            // We add store constraints to the dest, as they are evaluated when
            //   the dest value changes
            auto &st_node = getNode(cons.dest());
            st_node.addCons(
                std14::make_unique<AndersStoreCons>(cons.src(), cons.dest()));
            break;
          }
        // Alloc constraints are added as initial points-to data
        case ConstraintType::AddressOf:
          {
            /*
            if (cons.src().val() == 8418 ||
                cons.src().val() == 8400) {
              llvm::dbgs() << "Node: " << cons.dest() << " has initial pts: " <<
                cons.src() << "\n";
            }
            */
            /*
            llvm::dbgs() << "fill addrof: " << cons.dest() << " <- " <<
              cons.src() << "\n";
            */
            auto &node = getNode(cons.dest());
            // llvm::dbgs() << "Setting ptsto to: " << cons.src() << "\n";
            assert(cons.src().val() < omap.getNumObjs());
            node.ptsto().set(cons.src());
            break;
          }
        // Copy constraints are added as edges
        case ConstraintType::Copy:
          {
            auto &node = getNode(cons.src());
            node.addSucc(cons.dest(), cons.offs());
            break;
          }
        default:
          llvm_unreachable("Invalid cons type");
      }
    }

    // Add constraints for indirect function calls:
    // For each indirect callsite (in cg)
    for (const auto &[callinst, call_info] : cg.indirs()) {
      // Defaults to invalid
      ObjID ret_id;

      // Setup ret if we return a pointer
      if (call_info.isPointer()) {
        ret_id = callinst;
      }

      auto arg_begin = std::begin(call_info);
      auto arg_end = std::end(call_info);

      auto callee = call_info.callee();

      auto &node = getNode(callee);

      node.addCons(
          std14::make_unique<AndersIndirCallCons>(callee, ret_id,
            arg_begin, arg_end));
    }

    /*
    auto &nd = getNode(ObjID(138391));
    llvm::dbgs() << "Node " << nd.id() << " has constriants:\n";
    for (auto &pcons : nd.constraints()) {
      llvm::dbgs() << "  " << *pcons << "\n";
    }

    llvm::dbgs() << "  ptsto: " << nd.ptsto() << "\n";

    llvm::dbgs() << "copySuccs: {";
    auto &succs = nd.copySuccs();
    for (auto succ_id : succs) {
      llvm::dbgs() << " " << succ_id;
    }
    llvm::dbgs() << " }\n";

    llvm::dbgs() << "gepSuccs: {";
    auto &gep_succs = nd.gepSuccs();
    for (auto &succ_pr : gep_succs) {
      llvm::dbgs() << " (" << succ_pr.first << " + " << succ_pr.second << ")";
    }
    llvm::dbgs() << " }\n";
    */
  }

  void merge(AndersNode &n1, AndersNode &n2) {
    assert(reps_.find(n1.id()) == n1.id() &&
        reps_.find(n2.id()) == n2.id());
    assert(n1.id() != n2.id());
    reps_.merge(n1.id(), n2.id());

    auto rep_id = reps_.find(n1.id());

    if (rep_id == n1.id()) {
      n1.merge(n2);
    } else {
      assert(rep_id == n2.id());
      n2.merge(n1);
    }
  }

  // Removes any unneeded information after solve completes
  void cleanup() {
    for (auto &node : *this) {
      node.cleanup();
    }
  }

  void setStructInfo(const ObjectMap::StructMap &info) {
    structInfo_ = info;
  }

  const ObjectMap::StructMap &getStructInfo() const {
    return structInfo_;
  }

  typedef std::map<ObjID, std::pair<ObjID, std::vector<ObjID>>>::const_iterator
    const_fcn_iterator;

  const_fcn_iterator fcns_begin() const {
    return std::begin(fcns_);
  }

  const_fcn_iterator fcns_end() const {
    return std::end(fcns_);
  }

  const_fcn_iterator tryGetFcnInfo(ObjID fcn_obj_id) {
    return fcns_.find(fcn_obj_id);
  }

  const std::pair<ObjID, std::vector<ObjID>> &
  getFcnInfo(ObjID fcn_obj_id) const {
    return fcns_.at(fcn_obj_id);
  }

  typedef std::vector<AndersNode>::iterator iterator;

  iterator begin() {
    return std::begin(nodes_);
  }

  iterator end() {
    return std::end(nodes_);
  }

 private:
  // Nodes in the graph, one per object
  std::vector<AndersNode> nodes_;
  util::UnionFind<ObjID> reps_;

  std::map<ObjID, std::pair<ObjID, std::vector<ObjID>>> fcns_;
  ObjectMap::StructMap structInfo_;
};

#endif  // INCLUDE_ANDERSHELPERS_H_
