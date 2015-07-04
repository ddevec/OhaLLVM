/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_DUG_H_
#define INCLUDE_DUG_H_

#include <cstdint>

#include <list>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "include/id.h"
#include "include/ObjectMap.h"

class PtsSet {
  //{{{
 public:
    PtsSet() = default;

 private:
  //}}}
};

class Constraint {
  //{{{
 public:
    enum class Type { Copy, Load, Store, AddressOf };

    Constraint(Type t, ObjectMap::ObjID d, ObjectMap::ObjID s);
    Constraint(Type t, ObjectMap::ObjID d, ObjectMap::ObjID s, int32_t o);

    Constraint(const Constraint &) = delete;
    Constraint &operator=(const Constraint&) = delete;

    Constraint(Constraint &&) = default;
    Constraint &operator=(Constraint&&) = default;

    Type type() const {
      return type_;
    }

    ObjectMap::ObjID src() const {
      return src_;
    }

    ObjectMap::ObjID dest() const {
      return dest_;
    }

    int32_t offs() const {
      return offs_;
    }

    bool targetIsDest() const {
      // Okay, which target is the target of node?
      switch (type_) {
        case Type::AddressOf:
          return true;
        case Type::Load:
          return false;
        case Type::Store:
          return true;
        default:
          return false;
      }
    }

    ObjectMap::ObjID getTarget() const {
      if (targetIsDest()) {
        return dest();
      } else {
        return src();
      }
    }

 private:
    Type type_;

    ObjectMap::ObjID src_;
    ObjectMap::ObjID dest_;

    int32_t offs_ = 0;
  //}}}
};

class DUG {
  //{{{
 public:
    struct pe_id { };
    typedef ID<pe_id, int32_t, -1> PEid;
    typedef ObjectMap::ObjID ObjID;

    DUG() = default;

    // No copy/move semantics
    DUG(const DUG &) = delete;
    DUG(DUG &&) = delete;

    DUG &operator=(const DUG &) = delete;
    DUG &operator=(DUG &&) = delete;

    void prepare(const ObjectMap &omap);

    void add(Constraint::Type, ObjID d, ObjID s, int32_t o = 0);

    ObjID addNode(ObjectMap &omap);

    void addIndirectCall(ObjID id, const llvm::Value *val);

    void addIndirect(const llvm::Value *v, Constraint::Type type,
        ObjID d, ObjID s, int32_t o = 0);

    void associateNode(ObjID node, const llvm::Value *val);

    // Use/def tracking {{{
    void addUse(ObjID id) {
      uses_.push_back(id);
    }

    void addDef(ObjID id) {
      defs_.push_back(id);
    }

    const std::vector<ObjID> &uses() const {
      return uses_;
    }

    const std::vector<ObjID> &defs() const {
      return defs_;
    }
    //}}}

    // PE (Pointer Equivalence class) ids {{{
    void setupPE(const std::map<ObjID, PEid> &mapping) {
      objToPE_.clear();
      objToPE_.insert(std::begin(mapping), std::end(mapping));
    }

    PEid getPE(ObjID id) const {
      PEid ret;
      auto it = objToPE_.find(id);
      if (it != std::end(objToPE_)) {
        ret = it->second;
      }

      return ret;
    }
    //}}}

    // Iterator helper {{{
    // Iterates an iter itype, returning a std::pair<ObjID(id), outp>
    template<typename itype, typename outp>
    struct pair_iter {
      //{{{
     public:
        typedef std::pair<ObjID, outp &> value_type;

        explicit pair_iter(itype iter) :
            iter_(iter) { }

        value_type operator*() {
          return std::make_pair(ObjID(pos_),
              std::ref(*iter_));
        }

        pair_iter &operator++() {
          ++pos_;
          ++iter_;

          return *this;
        }

        pair_iter &operator--() {
          --pos_;
          --iter_;

          return *this;
        }

        bool operator==(const pair_iter &it) {
          return it.iter_ == iter_;
        }

        bool operator!=(const pair_iter &it) {
          return it.iter_ != iter_;
        }

        bool operator<(const pair_iter &it) {
          return it.iter_ < iter_;
        }

     private:
        itype iter_;
        size_t pos_ = 0;
      //}}}
    };
    //}}}

    // Constraint iterators {{{
    /*
    typedef pair_iter<std::vector<Constraint>::iterator, Constraint>
      constraint_iterator;
    typedef pair_iter<std::vector<Constraint>::const_iterator, const Constraint>
      const_constraint_iterator;
    */
    typedef std::vector<Constraint>::iterator constraint_iterator;
    typedef std::vector<Constraint>::const_iterator const_constraint_iterator;

    size_t constraintSize() const {
      return constraints_.size();
    }

    constraint_iterator constraint_begin() {
      return std::begin(constraints_);
    }

    constraint_iterator constraint_end() {
      return std::begin(constraints_);
    }

    const_constraint_iterator constraint_begin() const {
      return std::begin(constraints_);
    }

    const_constraint_iterator constraint_end() const {
      return std::end(constraints_);
    }

    const_constraint_iterator constraint_cbegin() const {
      return constraints_.cbegin();
    }

    const_constraint_iterator constraint_cend() const {
      return constraints_.cend();
    }
    //}}}

    // For debugging {{{
    void printDotConstraintGraph(const std::string &graphname,
        const ObjectMap &omap) const;

    void printDotPEGraph(const std::string &graphname,
        const ObjectMap &omap) const;
    //}}}

 private:
    // An individual node within the DUG
    class DUGNode {
      //{{{
     public:
        DUGNode() = default;

        void setValue(const llvm::Value *val) {
          value_ = val;
        }

        const llvm::Value *value() const {
          return value_;
        }

     private:
        // The llvm values that this node represents
        const llvm::Value *value_;

        std::vector<PtsSet> to_;
        std::vector<PtsSet> from_;

        std::vector<DUGNode *> part_succ_;

        ObjID rep_;

        std::list<Constraint> constraints_;
      //}}}
    };

    // Our vector of nodes
    std::vector<DUGNode> nodes_;
    std::vector<Constraint> constraints_;

    // The PE equivalent for each obj in the graph
    std::map<ObjID, PEid> objToPE_;

    std::vector<std::pair<const llvm::Value *, ObjID>> indirectCalls_;

    std::vector<ObjID> defs_;
    std::vector<ObjID> uses_;
  //}}}
};

#endif  // INCLUDE_DUG_H_

