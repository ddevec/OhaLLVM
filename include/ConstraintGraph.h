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

    struct SrcDestCmp {
      bool operator()(const Constraint &lhs, const Constraint &rhs) const {
        if (lhs.src() == rhs.src()) {
          return lhs.dest() < rhs.dest();
        }

        return lhs.src() < rhs.src();
      }
    };

    // Constructors {{{
    Constraint(ObjID s, ObjID d, ConstraintType t) :
        Constraint(s, d, t, 0) {
    }

    Constraint(ObjID s, ObjID d,
          ConstraintType t, int32_t o) :
        // Note, when rep not specified, rep is dest
        Constraint(t, s, d, d, o) {
      assert(t != ConstraintType::Load && t != ConstraintType::Store);
    }

    Constraint(ConstraintType type, ObjID src, ObjID dest, ObjID rep) :
          Constraint(type, src, dest, rep, 0) { }

    Constraint(ConstraintType type, ObjID src, ObjID dest, ObjID rep,
        int32_t offs) :
        src_(src), dest_(dest), rep_(rep), type_(type), offs_(offs) {
      assert(!(src == ObjectMap::ObjID(2) &&
            dest == ObjectMap::ObjID(51912)));
      // We shouldn't copy from the UV to null val... its bad
      assert(!(type == ConstraintType::Copy &&
          src == ObjectMap::UniversalValue &&
          dest == ObjectMap::NullValue));
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

    ObjID rep() const {
      return rep_;
    }
    
    void updateRep(ObjID new_rep) {
      rep_ = new_rep;
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

    static constexpr const char *getTypeName(ConstraintType t) {
      return (t == ConstraintType::Copy) ? "copy" :
             (t == ConstraintType::AddressOf) ? "address_of" :
             (t == ConstraintType::Load) ? "load" :
             (t == ConstraintType::Store) ?  "store" :
             "ERROR UNKNOWN CONST EXPR";
    }

    friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
        const Constraint &cons) {
      o << cons.rep() << ": " << getTypeName(cons.type()) << ", (" <<
          cons.src() << ", " << cons.dest() << ") + " << cons.offs();
      return o;
    }
    //}}}

 private:
    // Private Data {{{
    ObjID src_;
    ObjID dest_;
    ObjID rep_;

    bool strong_ = false;

    ConstraintType type_;

    int32_t offs_ = 0;
    //}}}
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
      // assert(!(s == ObjectMap::ObjID(20852) && d == ObjectMap::ObjID(3167)));
      if (s == ObjectMap::NullValue || d == ObjectMap::NullValue ||
          s == ObjectMap::NullObjectValue || d == ObjectMap::NullObjectValue) {
        // llvm::dbgs() << "Skipping null constraint....\n";
        return ConsID();
      } else {
        assert(!(type == ConstraintType::Copy &&
            s == ObjectMap::UniversalValue &&
            d == ObjectMap::NullValue));
        constraints_.emplace_back(new Constraint(s, d, type, o));

        auto id = ConsID(constraints_.size()-1);
        return id;
      }
    }

    ConsID add(ConstraintType type, ObjID nd, ObjID s, ObjID d) {
      constraints_.emplace_back(new Constraint(type, s, d, nd));

      auto id = ConsID(constraints_.size()-1);
      return id;
    }

    void removeConstraint(std::unique_ptr<Constraint> &pcons) {
      pcons.reset(nullptr);
    }

    void removeConstraint(ConsID id) {
      // Reset the ptr to nullptr
      constraints_.at(id.val()).reset(nullptr);
    }
    //}}}

    // Accessors {{{
    Constraint  &getConstraint(ConsID id) {
      return *constraints_.at(id.val());
    }

    const Constraint  &getConstraint(ConsID id) const {
      return *constraints_.at(id.val());
    }

    size_t constraintSize() const {
      return constraints_.size();
    }

    typedef std::map<const llvm::Value *, ObjID>::const_iterator
      p2icast_iterator;

    p2icast_iterator findP2ICast(const llvm::Value *i_val) const {
      return P2ICast_.find(i_val);
    }

    bool addP2ICast(const llvm::Value *i_val, ObjID p_val) {
      auto ret = P2ICast_.emplace(i_val, p_val);
      assert(ret.second);
      return ret.second;
    }

    p2icast_iterator p2icast_end() const {
      return std::end(P2ICast_);
    }

    p2icast_iterator p2icast_begin() const {
      return std::begin(P2ICast_);
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

    // Tracks casts from pointers to integers, to help improve the accuracy of
    //   I2P casts
    std::map<const llvm::Value *, ObjID> P2ICast_;

    //}}}
  //}}}
};

#endif  // INCLUDE_CONSTRAINTGRAPH_H_
