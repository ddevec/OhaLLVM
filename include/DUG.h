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
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "include/util.h"
#include "include/ObjectMap.h"

#include "llvm/Instructions.h"

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

    // Constructors {{{
    Constraint(Type t, ObjectMap::ObjID d, ObjectMap::ObjID s);
    Constraint(Type t, ObjectMap::ObjID d, ObjectMap::ObjID s, int32_t o);

    // No copys, yes moves {{{
    Constraint(const Constraint &) = delete;
    Constraint &operator=(const Constraint&) = delete;

    Constraint(Constraint &&) = default;
    Constraint &operator=(Constraint&&) = default;
    //}}}
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
    // Private Data {{{
    Type type_;

    ObjectMap::ObjID dest_;
    ObjectMap::ObjID src_;

    int32_t offs_ = 0;
    //}}}
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

    // Control Flow graph ids
    struct cfg_id { };
    typedef ID<cfg_id, int32_t, -1> CFGid;
    //}}}

    // Internal classes {{{
    // CFGNodes {{{
    class CFGNode {
     public:
        // No Copy/move {{{
        CFGNode(const CFGNode &) = delete;
        CFGNode(CFGNode &&) = delete;

        CFGNode &operator=(const CFGNode &) = delete;
        CFGNode &operator=(CFGNode &&) = delete;
        //}}}

        // Accessors {{{
        bool m() const {
          return m_;
        }

        bool p() const {
          return !m();
        }

        bool r() const {
          return r_;
        }

        bool c() const {
          return c_;
        }
        //}}}

        // Setters {{{
        void setM() {
          m_ = true;
        }

        void setR() {
          r_ = true;
        }
        //}}}

     private:
      // Private variables {{{
      // To identify p/m nodes (see computeSSA comments)
      bool m_ = false;
      // To identify r/u nodes (see computeSSA comments)
      bool r_ = false;
      // To identify constant nodes (see computeSSA comments)
      bool c_ = false;
      //}}}
    };
    //}}}

    // CFGEdges {{{
    class CFGEdge {
     public:
        CFGEdge(CFGid dest, CFGid src) : dest_(dest), src_(src) { }

        CFGid dest() const {
          return dest_;
        }

        CFGid src() const {
          return src_;
        }

     private:
        CFGid dest_;
        CFGid src_;
    };
    //}}}
    //}}}

    // Constructors {{{
    // Default constructor
    DUG() = default;

    // No copy/move semantics {{{
    DUG(const DUG &) = delete;
    DUG(DUG &&) = delete;

    DUG &operator=(const DUG &) = delete;
    DUG &operator=(DUG &&) = delete;
    //}}}
    //}}}

    // DUG Construction Methods {{{
    void prepare(const ObjectMap &omap);

    ConsID add(Constraint::Type, ObjID d, ObjID s, int32_t o = 0);

    Constraint &getConstraint(ConsID id) {
      return constraints_.at(id.val());
    }

    ObjID addNode(ObjectMap &omap);

    void addIndirectCall(ObjID id, CFGid cfg) {
      // Indirect graph...
      indirectCalls_.emplace_back(id, cfg);
    }

    void addUnusedFunction(ObjID fcn_id,
        const std::vector<ConsID> &ids) {
      unusedFunctions_.emplace(std::make_pair(fcn_id, ids));
    }

    bool removeUnusedFunction(DUG::ObjID fcn_id);

    void associateNode(ObjID node, const llvm::Value *val);
    //}}}

    // CFG tracking {{{
    // Setters {{{
    void addUse(CFGid cfg_id, ObjID cons_dest_id) {
      uses_[cfg_id].push_back(cons_dest_id);
    }

    void addDef(CFGid cfg_id, ObjID cons_dest_id) {
      defs_[cfg_id].push_back(cons_dest_id);
    }

    void addCFGEdge(CFGid id1, CFGid id2) {
      cfgEdges_.emplace_back(id1, id2);
    }

    void addCFGCallsite(CFGid call_id, ObjID fcn_id, CFGid ret_id) {
      cfgDirCallsites_[call_id].push_back(fcn_id);
      cfgCallSuccessors_[call_id] = ret_id;
    }

    void addCFGIndirectCall(CFGid call_id, ObjID call_insn_id,
        CFGid ret_id) {
      // Don't think I actually need this... I'm using another function
      // instead... I should clean it up at some point
      // cfgIndirCallsites_[call_id].push_back(call_insn_id);
      cfgCallSuccessors_[call_id] = ret_id;
    }

    void addCFGFunctionStart(ObjID fcn_id, CFGid id) {
      cfgFunctionEntries_[fcn_id] = id;
    }

    void addCFGFunctionReturn(ObjID fcn_id, CFGid id) {
      cfgFunctionReturns_[fcn_id] = id;
    }

    void addCFGCallRetInfo(ObjID fcn_id, CFGid call_id, CFGid ret_id) {
      cfgFcnToCallRet_.emplace(fcn_id, std::make_pair(call_id, ret_id));
    }

    void addIndirFcn(ObjID call_id, ObjID fcn_id) {
      indirFcns_[call_id].push_back(fcn_id);
    }
    //}}}

    // Accessors {{{
    CFGNode &getCFGNode(CFGid id) {
      return cfgNodes_.at(id);
    }

    const CFGNode &getCFGNode(CFGid id) const {
      return cfgNodes_.at(id);
    }

    const std::pair<CFGid, CFGid> &
    getCFGCallRetInfo(ObjID fcn_id) const {
      return cfgFcnToCallRet_.at(fcn_id);
    }

    CFGid getCFGFunctionStart(ObjID fcn_id) const {
      return cfgFunctionEntries_.at(fcn_id);
    }

    CFGid getCFGFunctionReturn(ObjID fcn_id) const {
      return cfgFunctionReturns_.at(fcn_id);
    }

    CFGid getCFGCallSuccessor(CFGid call_id) const {
      return cfgCallSuccessors_.at(call_id);
    }

    const std::vector<ObjID> &getIndirFcns(ObjID call_id) const {
      return indirFcns_.at(call_id);
    }
    //}}}

    // CFG Unique Identifier Generator {{{
    CFGid getCFGid() {
      return CFGid(cfgIdGenerator_.next());
    }
    //}}}
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

    // Iterators {{{
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

        bool operator==(const pair_iter &it) const {
          return it.iter_ == iter_;
        }

        bool operator!=(const pair_iter &it) const {
          return it.iter_ != iter_;
        }

        bool operator<(const pair_iter &it) const {
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
    typedef std::vector<std::pair<ObjID, CFGid>>::iterator
      indirect_call_iterator;
    typedef std::vector<std::pair<ObjID, CFGid>>::const_iterator
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
    typedef std::map<ObjID, std::vector<ConsID>>::iterator
      unused_function_iterator;
    typedef std::map<ObjID, std::vector<ConsID>>::const_iterator  // NOLINT
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

    // Def-use Iterators {{{
    typedef std::vector<CFGEdge>::iterator cfg_iterator;
    typedef std::vector<CFGEdge>::const_iterator const_cfg_iterator;

    cfg_iterator cfg_begin() {
      return std::begin(cfgEdges_);
    }

    cfg_iterator cfg_end() {
      return std::end(cfgEdges_);
    }

    const_cfg_iterator cfg_begin() const {
      return std::begin(cfgEdges_);
    }

    const_cfg_iterator cfg_end() const {
      return std::end(cfgEdges_);
    }

    const_cfg_iterator cfg_cbegin() const {
      return cfgEdges_.cbegin();
    }

    const_cfg_iterator cfg_cend() const {
      return cfgEdges_.cend();
    }
    //}}}
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

    // Constraint data
    std::vector<Constraint> constraints_;

    // Control Flow Graph data {{{
    // The actual edges in the graph
    std::vector<CFGEdge> cfgEdges_;
    // CFGids to CFGNodes
    std::map<CFGid, CFGNode> cfgNodes_;

    // FunctionID to call/ret nodes
    std::map<ObjID, std::pair<CFGid, CFGid>> cfgFcnToCallRet_;

    // Maps Control Flow nodes to the call functions wthin them
    std::map<CFGid, std::vector<ObjID>> cfgDirCallsites_;
    // Maps Control Flow nodes to the call instructions wthin them
    std::map<CFGid, std::vector<ObjID>> cfgIndirCallsites_;

    std::map<ObjID, std::vector<ObjID>> indirFcns_;

    // Function call -> CFG node
    std::vector<std::pair<ObjID, CFGid>> indirectCalls_;

    // The return CFG node associated with each CFG containing a call
    std::map<CFGid, CFGid> cfgCallSuccessors_;
    // The CFG call node for each call instruciton
    std::map<ObjID, CFGid> cfgFunctionEntries_;
    // The CFG node for each call instruction's return
    std::map<ObjID, CFGid> cfgFunctionReturns_;

    // Defs/uses represented at each CFG node, used to assicate calculated SSA
    // info back to contraints
    std::map<CFGid, std::vector<ObjID>> defs_;
    std::map<CFGid, std::vector<ObjID>> uses_;

    // ID Generator for CFGids
    UniqueIdentifier<int32_t> cfgIdGenerator_;
    //}}}

    // The PE equivalent for each obj in the graph
    std::map<ObjID, PEid> objToPE_;

    // List of functions that have no obvious uses
    std::map<ObjID, std::vector<ConsID>> unusedFunctions_;

    //}}}
  //}}}
};

#endif  // INCLUDE_DUG_H_

