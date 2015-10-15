/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_CONSTRAINTGRAPH_H_
#define INCLUDE_CONSTRAINTGRAPH_H_

#include "include/ObjectMap.h"

#include "include/SEG.h"
#include "include/Debug.h"

#include <utility>

enum class ConstraintKind { Basic, Node };
enum class ConstraintType { Copy, Load, Store, AddressOf };
class Constraint {
  //{{{
 public:
    typedef typename ObjectMap::ObjID ObjID;
    // Constructors {{{
    Constraint(ObjID s, ObjID d, ConstraintType t) :
        Constraint(ConstraintKind::Basic, s, d, t, 0) {
      assert(!(t == ConstraintType::Copy &&
          s == ObjectMap::UniversalValue &&
          d == ObjectMap::NullValue));
    }

    Constraint(ObjID s, ObjID d,
          ConstraintType t, int32_t o) :
        Constraint(ConstraintKind::Basic, s, d, t, o) {
      assert(t != ConstraintType::Load && t != ConstraintType::Store);
      assert(!(t == ConstraintType::Copy &&
          s == ObjectMap::UniversalValue &&
          d == ObjectMap::NullValue));
    }

    // No copys, yes moves {{{
    Constraint(const Constraint &) = default;
    Constraint &operator=(const Constraint&) = default;

    Constraint(Constraint &&) = default;
    Constraint &operator=(Constraint&&) = default;
    //}}}
    //}}}

    // Accessors {{{
    ObjID src() const {
      return src_;
    }

    ObjID offsSrc() const {
      return ObjectMap::getOffsID(src(), offs());
    }

    ObjID dest() const {
      return dest_;
    }

    void retarget(ObjID src, ObjID dest) {
      src_ = src;
      dest_ = dest;
    }

    ConstraintType type() const {
      return type_;
    }

    int32_t offs() const {
      return offs_;
    }

    bool strong() const {
      return strong_;
    }

    void setStrong(bool strong) {
      strong_ = strong;
    }

    virtual bool operator<(const Constraint &cons_rhs) const {
      if (type() != cons_rhs.type()) {
        return type() < cons_rhs.type();
      }

      if (dest() != cons_rhs.dest()) {
        return dest() < cons_rhs.dest();
      }

      if (src() != cons_rhs.src()) {
        return src() < cons_rhs.src();
      }

      if (offs() != cons_rhs.offs()) {
        return offs() < cons_rhs.offs();
      }

      return false;
    }

    ConstraintKind getKind() const {
      return kind_;
    }

    // For LLVM RTTI {{{
    static bool classof(const Constraint *) {
      return true;
    }
    //}}}
    //}}}

    // Print helper {{{
    void print_label(dbg_ostream &ofil, const ObjectMap &) const {
      switch (type()) {
        case ConstraintType::Copy:
          ofil << "copy";
          break;
        case ConstraintType::AddressOf:
          ofil << "addr_of";
          break;
        case ConstraintType::Load:
          ofil << "load";
          break;
        case ConstraintType::Store:
          ofil << "store";
          break;
        default:
          unreachable("Constraint with unexpected type!");
          ofil << "BLEH";
      }
    }
    //}}}

 protected:
    // Used from subclass constructors only
    Constraint(ConstraintKind kind, ObjID s, ObjID d, ConstraintType t) :
      Constraint(kind, s, d, t, 0) { }
    Constraint(ConstraintKind kind, ObjID s, ObjID d,
          ConstraintType t, int32_t o) :
        src_(s), dest_(d), type_(t), kind_(kind), offs_(o) {
      // We should never copy universal value into null value!
      assert(!(t == ConstraintType::Copy &&
          s == ObjectMap::UniversalValue &&
          d == ObjectMap::NullValue));
    }

 private:
    // Private Data {{{
    ObjID src_;
    ObjID dest_;

    bool strong_ = false;

    ConstraintType type_;

    ConstraintKind kind_;

    int32_t offs_ = 0;
    //}}}
  //}}}
};

class NodeConstraint : public Constraint {
  //{{{
 public:
    typedef typename ObjectMap::ObjID ObjID;

    NodeConstraint(ConstraintType type, ObjID src, ObjID dest, ObjID nd) :
      Constraint(ConstraintKind::Node, src, dest, type), nodeId_(nd) { }

    // No copys, yes moves {{{
    NodeConstraint(const NodeConstraint &) = default;
    NodeConstraint &operator=(const NodeConstraint&) = default;

    NodeConstraint(NodeConstraint &&) = default;
    NodeConstraint &operator=(NodeConstraint&&) = default;
    //}}}
    
    ObjID nodeId() const {
      return nodeId_;
    }

    void setNodeID(ObjID node_id) {
      nodeId_ = node_id;
    }

    bool operator<(const Constraint &cons) const override {
      auto ld_cons = cast<NodeConstraint>(cons);

      if (nodeId() != ld_cons.nodeId()) {
        return nodeId() < ld_cons.nodeId();
      }

      return Constraint::operator<(cons);
    }

    // For LLVM RTTI {{{
    static bool classof(const Constraint *cons) {
      return cons->getKind() == ConstraintKind::Node;
    }
    //}}}

 private:
    ObjID nodeId_;
  //}}}
};

class ConstraintGraph {
  //{{{
 public:
    // Typedefs {{{
    // ObjIDs
    typedef ObjectMap::ObjID ObjID;

    struct cons_id { };
    typedef ID<cons_id, int32_t>  ConsID;
    //}}}

    // Modifiers {{{
    ConsID add(ConstraintType type, ObjID d, ObjID s) {
      return add(type, d, s, 0);
    }

    ConsID add(ConstraintType type, ObjID d, ObjID s, int o) {
      /*
      dbg << "Adding edge: (" << s << ", " << d <<
        ") with type: " << static_cast<int32_t>(type) << "\n";
        */
      assert(!(type == ConstraintType::Copy &&
          s == ObjectMap::UniversalValue &&
          d == ObjectMap::NullValue));
      constraints_.emplace_back(new Constraint(s, d, type, o));
      // dbg << "Creating constriant: " << (constraints_.size()-1) << "\n";
      return ConsID(constraints_.size()-1);
    }

    ConsID add(ConstraintType type, ObjID nd, ObjID s, ObjID d) {
      constraints_.emplace_back(new NodeConstraint(type, s, d, nd));

      // dbg << "Creating constriant: " << (constraints_.size()-1) << "\n";
      return ConsID(constraints_.size()-1);
    }

    void removeConstraint(std::unique_ptr<Constraint> &pcons) {
      pcons.reset(nullptr);
    }

    void removeConstraint(ConsID id) {
      // Reset the ptr to nullptr
      constraints_.at(id.val()).reset(nullptr);
    }

    void unique() {
      std::sort(std::begin(constraints_), std::end(constraints_));
      auto it = std::unique(std::begin(constraints_), std::end(constraints_));
      constraints_.erase(it, std::end(constraints_));
    }
    //}}}

    // Accessors {{{
    Constraint  &getConstraint(ConsID id) {
      return *constraints_.at(id.val());
    }

    const Constraint  &getConstraint(ConsID id) const {
      return *constraints_.at(id.val());
    }
    //}}}

    // Graph print debugging {{{
    void printDotConstraintGraph(const std::string &graphname,
        const ObjectMap &omap) const;
    //}}}

    // Iteration {{{
    typedef std::vector<std::unique_ptr<Constraint>>::iterator iterator;
    typedef std::vector<std::unique_ptr<Constraint>>::const_iterator const_iterator;
    typedef std::unique_ptr<Constraint> iter_type;

    iterator begin() {
      return std::begin(constraints_);
    }

    iterator end() {
      return std::end(constraints_);
    }

    const_iterator begin() const {
      return std::begin(constraints_);
    }

    const_iterator end() const {
      return std::end(constraints_);
    }

    const_iterator cbegin() const {
      return std::begin(constraints_);
    }

    const_iterator cend() const {
      return std::end(constraints_);
    }

    //}}}

 private:
    // Private data {{{
    std::vector<std::unique_ptr<Constraint>> constraints_;
    //}}}
  //}}}
};

#endif  // INCLUDE_CONSTRAINTGRAPH_H_
