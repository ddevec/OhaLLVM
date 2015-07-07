/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_DUG_H_
#define INCLUDE_DUG_H_

#include <cstdint>

#include <functional>
#include <list>
#include <map>
#include <queue>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "include/util.h"
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
    enum class Type { Copy, Load, Store, AddressOf, Noop };

    Constraint(Type t, ObjectMap::ObjID d, ObjectMap::ObjID s);
    Constraint(Type t, ObjectMap::ObjID d, ObjectMap::ObjID s, int32_t o);

    // No copys, yes moves {{{
    Constraint(const Constraint &) = delete;
    Constraint &operator=(const Constraint&) = delete;

    Constraint(Constraint &&) = default;
    Constraint &operator=(Constraint&&) = default;
    //}}}


    // Accessors {{{
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
    //}}}
    //
    // Noop helpers {{{
    bool isNoop() const {
      return type() == Type::Noop;
    }

    void makeNoop() {
      type_ = Type::Noop;
    }
    //}}}

    // Target helpers {{{
    bool targetIsDest() const {
      // Okay, which target is the target of node?
      switch (type_) {
        case Type::AddressOf:
          return true;
        case Type::Load:
          return false;
        case Type::Store:
          return true;
        case Type::Copy:
          return false;
        case Type::Noop:
          return false;
        default:
          llvm_unreachable("Unrecognized constraint type");
      }
    }

    ObjectMap::ObjID getTarget() const {
      if (targetIsDest()) {
        return dest();
      } else {
        return src();
      }
    }
    //}}}

 private:
    Type type_;

    ObjectMap::ObjID dest_;
    ObjectMap::ObjID src_;

    int32_t offs_ = 0;
  //}}}
};

class DUG {
  //{{{
 public:
    // Id Types {{{
    struct pe_id { };
    typedef ID<pe_id, int32_t, -1> PEid;
    typedef ObjectMap::ObjID ObjID;

    struct con_id { };
    typedef ID<con_id, int32_t, -1> ConsID;
    //}}}

    DUG() = default;

    // No copy/move semantics {{{
    DUG(const DUG &) = delete;
    DUG(DUG &&) = delete;

    DUG &operator=(const DUG &) = delete;
    DUG &operator=(DUG &&) = delete;
    //}}}

    // DUG Construction Methods {{{
    void prepare(const ObjectMap &omap);

    ConsID add(Constraint::Type, ObjID d, ObjID s, int32_t o = 0);

    Constraint &getConstraint(ConsID id) {
      return constraints_.at(id.val());
    }

    ObjID addNode(ObjectMap &omap);

    void addIndirectCall(ObjID id, llvm::Instruction *val);

    void addIndirect(const llvm::Value *v, Constraint::Type type,
        ObjID d, ObjID s, int32_t o = 0);

    void addUnusedFunction(const llvm::Function *fcn,
        const std::vector<ConsID> &ids) {
      unusedFunctions_.emplace(std::make_pair(fcn, ids));
    }

    void removeUnusedFunction(const llvm::Function *fcn) {
      auto it = unusedFunctions_.find(fcn);

      for (auto id : it->second) {
        auto &cons = getConstraint(id);
        cons.makeNoop();
      }

      unusedFunctions_.erase(fcn);
    }

    void associateNode(ObjID node, const llvm::Value *val);
    //}}}

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

    // Indirect Call Iterators {{{
    typedef std::vector<std::pair<llvm::Instruction *, ObjID>>::iterator
      indirect_call_iterator;
    typedef std::vector<std::pair<llvm::Instruction *, ObjID>>::const_iterator
      const_indirect_call_iterator;

    indirect_call_iterator indirect_begin() {
      return std::begin(indirectCalls_);
    }

    indirect_call_iterator indirect_end() {
      return std::end(indirectCalls_);
    }

    const_indirect_call_iterator indirect_begin() const {
      return std::begin(indirectCalls_);
    }

    const_indirect_call_iterator indirect_end() const {
      return std::end(indirectCalls_);
    }

    const_indirect_call_iterator indirect_cbegin() const {
      return indirectCalls_.cbegin();
    }

    const_indirect_call_iterator indirect_cend() const {
      return indirectCalls_.cend();
    }

    //}}}

    // Unused Function Iterators {{{
    typedef std::map<const llvm::Function *, std::vector<ConsID>>::iterator
      unused_function_iterator;
    typedef std::map<const llvm::Function *, std::vector<ConsID>>::const_iterator  // NOLINT
      const_unused_function_iterator;

    unused_function_iterator unused_function_begin() {
      return std::begin(unusedFunctions_);
    }

    unused_function_iterator unused_function_end() {
      return std::end(unusedFunctions_);
    }

    const_unused_function_iterator unused_function_begin() const {
      return std::begin(unusedFunctions_);
    }

    const_unused_function_iterator unused_function_end() const {
      return std::end(unusedFunctions_);
    }

    const_unused_function_iterator unused_function_cbegin() const {
      return unusedFunctions_.cbegin();
    }

    const_unused_function_iterator unused_function_cend() const {
      return unusedFunctions_.cend();
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

    // Private variables {{{
    // Our vector of nodes
    std::vector<DUGNode> nodes_;
    std::vector<Constraint> constraints_;

    // The PE equivalent for each obj in the graph
    std::map<ObjID, PEid> objToPE_;

    std::vector<std::pair<llvm::Instruction *, ObjID>> indirectCalls_;
    std::map<const llvm::Function *, std::vector<ConsID>> unusedFunctions_;

    std::vector<ObjID> defs_;
    std::vector<ObjID> uses_;
    //}}}
  //}}}
};

#endif  // INCLUDE_DUG_H_

