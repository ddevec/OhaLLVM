/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_CONSTRAINTGRAPH_H_
#define INCLUDE_CONSTRAINTGRAPH_H_

#include "include/ObjectMap.h"

#include "include/SEG.h"
#include "include/Debug.h"

#include <utility>


enum class ConstraintType { Copy, Load, Store, AddressOf };
class Constraint {
  //{{{
 public:
    typedef typename ObjectMap::ObjID ObjID;
    // Constructors {{{
    Constraint(ObjID s, ObjID d, ConstraintType t) :
      Constraint(s, d, t, 0) { }
    Constraint(ObjID s, ObjID d, ConstraintType t, int32_t o) :
      src_(s), dest_(d), type_(t), offs_(o) { }

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

    /*
    bool operator==(const SEGEdge<ObjID> &rhs) const override {
      auto &cons_rhs = llvm::cast<Constraint>(rhs);
      if (offs() != cons_rhs.offs() || type() != cons_rhs.type()) {
        return false;
      }

      return SEGEdge<ObjID>::operator==(rhs);
    }
    */

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

    ConstraintType getKind() const {
      return type_;
    }

    // For LLVM RTTI {{{
    static bool classof(const Constraint *) {
      return true;
    }
    //}}}
    //}}}

    // Target helpers {{{
    bool targetIsDest() const {
      // Okay, which target is the target of node?
      switch (type_) {
        case ConstraintType::AddressOf:
          return true;
        case ConstraintType::Load:
          return false;
        case ConstraintType::Store:
          return true;
        case ConstraintType::Copy:
          return false;
        default:
          llvm_unreachable("Unrecognized constraint type");
      }
    }

    ObjID getTarget() const {
      if (targetIsDest()) {
        return dest();
      } else {
        return src();
      }
    }
    //}}}

    // Print helper {{{
    void print_label(llvm::raw_ostream &ofil, const ObjectMap &) const {
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
          llvm_unreachable("Constraint with unexpected type!");
          ofil << "BLEH";
      }
    }
    //}}}

 private:
    // Private Data {{{
    ObjID src_;
    ObjID dest_;
    ConstraintType type_;

    int32_t offs_ = 0;
    //}}}
  //}}}
};

class StoreConstraint : public Constraint {
  //{{{
 public:
    typedef typename ObjectMap::ObjID ObjID;

    StoreConstraint(ObjID src, ObjID dest, ObjID nd) :
      Constraint(src, dest, ConstraintType::Store), nodeId_(nd) { }

    // No copys, yes moves {{{
    StoreConstraint(const StoreConstraint &) = default;
    StoreConstraint &operator=(const StoreConstraint&) = default;

    StoreConstraint(StoreConstraint &&) = default;
    StoreConstraint &operator=(StoreConstraint&&) = default;
    //}}}
    
    ObjID storeId() const {
      return nodeId_;
    }

    bool operator<(const Constraint &cons) const {
      auto st_cons = llvm::cast<StoreConstraint>(cons);

      if (storeId() != st_cons.storeId()) {
        return storeId() < st_cons.storeId();
      }

      return Constraint::operator<(cons);
    }

    // For LLVM RTTI {{{
    static bool classof(const Constraint *cons) {
      return cons->getKind() == ConstraintType::Store;
    }
    //}}}
 private:
    ObjID nodeId_;
  //}}}
};

class LoadConstraint : public Constraint {
  //{{{
 public:
    typedef typename ObjectMap::ObjID ObjID;

    LoadConstraint(ObjID src, ObjID dest, ObjID nd) :
      Constraint(src, dest, ConstraintType::Load), nodeId_(nd) { }

    // No copys, yes moves {{{
    LoadConstraint(const LoadConstraint &) = default;
    LoadConstraint &operator=(const LoadConstraint&) = default;

    LoadConstraint(LoadConstraint &&) = default;
    LoadConstraint &operator=(LoadConstraint&&) = default;
    //}}}
    
    ObjID loadId() const {
      return nodeId_;
    }

    void setLoadID(ObjID ld_id) {
      nodeId_ = ld_id;
    }

    bool operator<(const Constraint &cons) const {
      auto ld_cons = llvm::cast<LoadConstraint>(cons);

      if (loadId() != ld_cons.loadId()) {
        return loadId() < ld_cons.loadId();
      }

      return Constraint::operator<(cons);
    }

    // For LLVM RTTI {{{
    static bool classof(const Constraint *cons) {
      return cons->getKind() == ConstraintType::Load;
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
      llvm::dbgs() << "Adding edge: (" << s << ", " << d <<
        ") with type: " << static_cast<int32_t>(type) << "\n";
      constraints_.emplace_back(new Constraint(s, d, type, o));
      return ConsID(constraints_.size());
    }

    ConsID add(ConstraintType type, ObjID nd, ObjID s, ObjID d) {

      if (type == ConstraintType::Store) {
        llvm::dbgs() << "Adding store-edge: (" << s << ", " << d <<
          ", " << nd << ") with type: " << static_cast<int32_t>(type) << "\n";
        constraints_.emplace_back(new StoreConstraint(s, d, nd));
      } else if (type == ConstraintType::Load) {
        // S and D are backwards for load nodes?
        llvm::dbgs() << "Adding load-edge: (" << s << ", " << d <<
          ", " << nd << ") with type: " << static_cast<int32_t>(type) << "\n";
        constraints_.emplace_back(new LoadConstraint(s, d, nd));
      } else {
        llvm_unreachable("Non-load-store constraint add");
      }

      return ConsID(constraints_.size());
    }

    // FIXME: Slow?
    void removeConstraint(ConsID id) {
      auto it = std::begin(constraints_);
      std::advance(it, id.val());
      constraints_.erase(it);
    }

    void unique() {
      std::sort(std::begin(constraints_), std::end(constraints_));
      auto it = std::unique(std::begin(constraints_), std::end(constraints_));
      constraints_.erase(it, std::end(constraints_));
    }
    //}}}

    // Accessors {{{
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
