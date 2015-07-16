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
#include <unordered_set>
#include <utility>
#include <vector>

#include "include/util.h"
#include "include/ObjectMap.h"
#include "include/SEG.h"

class PtsSet {
  //{{{
 public:
    PtsSet() = default;

 private:
  //}}}
};


enum class ConstraintType { Copy, Load, Store, AddressOf };
template <typename id_type>
class Constraint : public SEGEdge<id_type> {
  //{{{
 public:
    // Constructors {{{
    Constraint(id_type s, id_type d, ConstraintType t);
    Constraint(id_type s, id_type d, ConstraintType t, int32_t o);

    // For conversion from another constraint type
    template <typename old_id_type, typename id_converter>
    Constraint(id_type src, id_type dest, const SEGEdge<old_id_type> &old_con,
            SEG<id_type> &, id_converter) :
        SEGEdge<id_type>(EdgeKind::Constraint, src, dest),
        type_(llvm::cast<Constraint<old_id_type>>(old_con).type()),
        offs_(llvm::cast<Constraint<old_id_type>>(old_con).offs()) { }

    // No copys, yes moves {{{
    Constraint(const Constraint &) = default;
    Constraint &operator=(const Constraint&) = default;

    Constraint(Constraint &&) = default;
    Constraint &operator=(Constraint&&) = default;
    //}}}
    //}}}

    // Accessors {{{
    ConstraintType type() const {
      return type_;
    }

    int32_t offs() const {
      return offs_;
    }

    // For LLVM RTTI {{{
    static bool classof(const SEGEdge<id_type> *id) {
      return id->getKind() == EdgeKind::Constraint;
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
        /*
        case Type::Noop:
          return false;
          */
        default:
          llvm_unreachable("Unrecognized constraint type");
      }
    }

    id_type getTarget() const {
      if (targetIsDest()) {
        return SEGEdge<id_type>::dest();
      } else {
        return SEGEdge<id_type>::src();
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
    ConstraintType type_;

    int32_t offs_ = 0;
    //}}}
  //}}}
};

class DUG {
  //{{{
 public:
    // Id Types {{{
    typedef ObjectMap::ObjID ObjID;

    struct pe_id { };
    typedef ID<pe_id, int32_t, -1> PEid;

    /* -- We switched this to pair<ObjID, ObjID>
    struct con_id { };
    typedef ID<con_id, int32_t, -1> ConsID;
    */

    // Control Flow graph ids
    struct cfg_id { };
    typedef ID<cfg_id, int32_t, -1> CFGid;

    //}}}

    struct SEGNodeGroup : public UnifyNode<PEid> {
      //{{{

      // Constructors {{{
      SEGNodeGroup(int32_t nodenum, PEid id, ObjID base_id) :
          UnifyNode<PEid>(NodeKind::SEGNodeGroup, nodenum, id) {
        oids.insert(base_id);
      }

      template <typename id_converter>
      SEGNodeGroup(int32_t nodenum, PEid id, const SEGNode<ObjID> &old_node,
            id_converter convert) :
          UnifyNode<PEid>(NodeKind::SEGNodeGroup, nodenum, id,
              llvm::cast<UnifyNode<ObjID>>(old_node), convert) { }
      //}}}

      // Printing for DOT debugging {{{
      void print_label(llvm::raw_ostream &ofil,
          const ObjectMap &omap) const {
        // So I can know when the end is coming, for newline printing
        for (auto it = oids.begin(),
            en = oids.end(); it != en;) {
          auto id = *it;
          auto pr = omap.getValueInfo(id);
          if (pr.first != ObjectMap::Type::Special) {
            const llvm::Value *val = pr.second;
            if (val == nullptr) {
              ofil << "temp node";
            } else if (auto GV = llvm::dyn_cast<const llvm::GlobalValue>(val)) {
              ofil <<  GV->getName();
            } else if (auto F = llvm::dyn_cast<const llvm::Function>(val)) {
              ofil <<  F->getName();
            } else {
              ofil << *val;
            }
          } else {
            if (id == ObjectMap::NullValue) {
              ofil << "NullValue";
            } else if (id == ObjectMap::NullObjectValue) {
              ofil << "NullObjectValue";
            } else if (id == ObjectMap::IntValue) {
              ofil << "IntValue";
            } else if (id == ObjectMap::UniversalValue) {
              ofil << "UniversalValue";
            } else if (id == ObjectMap::UniversalValue) {
              ofil << "PthreadSpecificValue";
            } else {
              llvm_unreachable("Shouldn't have unknown value here!");
            }
          }

          ++it;
          if (it != en) {
            ofil << "\n";
          }
        }
      }

      void unite(SEGNode<PEid> &n) override {
        auto &grp = llvm::cast<SEGNodeGroup>(n);

        oids.insert(std::begin(grp.oids), std::end(grp.oids));

        UnifyNode<PEid>::unite(n);
      }

      // For llvm RTTI
      static bool classof(const SEGNode<PEid> *node) {
        return node->getKind() == NodeKind::SEGNodeGroup;
      }
      //}}}

      std::set<ObjID> oids;
      //}}}
    };

    struct ConstraintNode : public SEGNode<ObjID> {
      //{{{
      ConstraintNode(int32_t nodenum, ObjID id) :
        SEGNode<ObjID>(NodeKind::ConstraintNode, nodenum, id) { }

      ConstraintNode(int32_t nodenum, ObjID id, const ConstraintNode &con) :
        SEGNode<ObjID>(NodeKind::ConstraintNode, nodenum, id, con) { }

      void print_label(llvm::raw_ostream &ofil,
          const ObjectMap &omap) const override {
        ObjID id = SEGNode<ObjID>::id();
        auto pr = omap.getValueInfo(id);
        if (pr.first != ObjectMap::Type::Special) {
          const llvm::Value *val = pr.second;
          if (val == nullptr) {
            ofil << "temp node";
          } else if (auto GV = llvm::dyn_cast<const llvm::GlobalValue>(val)) {
            ofil <<  GV->getName();
          } else if (auto F = llvm::dyn_cast<const llvm::Function>(val)) {
            ofil <<  F->getName();
          } else {
            ofil << *val;
          }
        } else {
          if (id == ObjectMap::NullValue) {
            ofil << "NullValue";
          } else if (id == ObjectMap::NullObjectValue) {
            ofil << "NullObjectValue";
          } else if (id == ObjectMap::IntValue) {
            ofil << "IntValue";
          } else if (id == ObjectMap::UniversalValue) {
            ofil << "UniversalValue";
          } else if (id == ObjectMap::UniversalValue) {
            ofil << "PthreadSpecificValue";
          } else {
            llvm_unreachable("Shouldn't have unknown value here!");
          }
        }
      }
      //}}}
    };



    // Internal classes {{{
    // CFGNodes {{{
    class CFGNode : public SCCNode<CFGid>{
     public:
        CFGNode(int32_t nodenum, CFGid id) :
          SCCNode<CFGid>(NodeKind::CFGNode, nodenum, id) { }

        template <typename id_converter>
        CFGNode(int32_t  nodenum, CFGid id, const SEGNode<CFGid> &nd,
              id_converter convert) :
            SCCNode<CFGid>(NodeKind::CFGNode, nodenum, id, nd, convert),
            m_(llvm::cast<CFGNode>(nd).m()), r_(llvm::cast<CFGNode>(nd).r()),
            c_(llvm::cast<CFGNode>(nd).c()) { }

        // No Copy/move {{{
        CFGNode(const CFGNode &) = default;
        CFGNode(CFGNode &&) = default;

        CFGNode &operator=(const CFGNode &) = default;
        CFGNode &operator=(CFGNode &&) = default;
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

        void setC() {
          c_ = true;
        }
        //}}}

        // Unite {{{
        void unite(const CFGNode &n) {
          m_ |= n.m_;
          r_ |= n.r_;
          c_ |= n.c_;
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
    class CFGEdge : public SEGEdge<CFGid> {
     public:
        CFGEdge(CFGid dest, CFGid src) :
            SEGEdge<CFGid>(EdgeKind::CFGEdge, dest, src) { }

        template <typename id_converter>
        CFGEdge(CFGid dest, CFGid src, const SEGEdge<CFGid> &,
              SEG<CFGid> &, id_converter) :
            SEGEdge<CFGid>(EdgeKind::CFGEdge, dest, src) { }

     private:
    };
    //}}}
    //}}}

    // Graph types {{{
    typedef SEG<ObjID> ConstraintGraph;
    typedef SEG<PEid> ConstraintPEGraph;
    typedef SEG<CFGid> ControlFlowGraph;

    typedef std::pair<ObjID, ObjID> ConsID;
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
    void prepare(const ObjectMap &) { }

    ConsID add(ConstraintType, ObjID d, ObjID s, int32_t o = 0);

    const Constraint<ObjID>  &getConstraint(ConsID id) const {
      return llvm::cast<Constraint<ObjID>>(constraintGraph_.getEdge(id));
    }

    ObjID addNode(ObjectMap &omap);

    void addUnusedFunction(ObjID fcn_id,
        const std::vector<ConsID> &ids) {
      unusedFunctions_.emplace(std::make_pair(fcn_id, ids));
    }

    bool removeUnusedFunction(ObjID fcn_id);

    void associateNode(ObjID, ObjID) { }

    void removeConstraint(ConsID id) {
      constraintGraph_.removeEdge(id);
    }

    const ConstraintGraph &getConstraintGraph() const {
      return constraintGraph_;
    }

    ConstraintPEGraph getConstraintPEGraph() const {
      // Now, create a new SEG with the mappings
      return getConstraintGraph().convert<SEGNodeGroup, Constraint<PEid>, PEid>
        (std::bind(&DUG::getPE, this, std::placeholders::_1));
    }
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
      CFG_.addEdge<CFGEdge>(id1, id2);
    }

    void addCFGCallsite(CFGid call_id, ObjID fcn_id, CFGid ret_id) {
      cfgDirCallsites_[call_id].push_back(fcn_id);
      cfgCallSuccessors_[call_id] = ret_id;
    }

    void addCFGIndirectCall(CFGid call_id, ObjID obj_id,
        CFGid ret_id) {
      // Don't think I actually need this... I'm using another function
      // instead... I should clean it up at some point
      // cfgIndirCallsites_[call_id].push_back(call_insn_id);
      indirectCalls_.emplace_back(obj_id, call_id);
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
      // return cfgNodes_.at(id);
      return llvm::cast<CFGNode>(CFG_.getNode(id));
    }

    const CFGNode &getCFGNode(CFGid id) const {
      // return cfgNodes_.at(id);
      return llvm::cast<const CFGNode>(CFG_.getNode(id));
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

    const ControlFlowGraph &getCFG() const {
      return CFG_;
    }
    //}}}

    // CFG Unique Identifier Generator {{{
    CFGid getCFGid() {
      auto ret = CFGid(cfgIdGenerator_.next());

      CFG_.addNode<CFGNode>(ret);
      /*
      cfgNodes_.emplace(std::piecewise_construct, std::make_tuple(ret),
          std::make_tuple());
      */

      return ret;
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

    // Direct Call Iterators {{{
    typedef std::map<CFGid, std::vector<ObjID>>::iterator
      direct_call_iterator;
    typedef std::map<CFGid, std::vector<ObjID>>::const_iterator
      const_direct_call_iterator;

    direct_call_iterator direct_begin() {
      return std::begin(cfgDirCallsites_);
    }

    direct_call_iterator direct_end() {
      return std::end(cfgDirCallsites_);
    }

    const_direct_call_iterator direct_begin() const {
      return std::begin(cfgDirCallsites_);
    }

    const_direct_call_iterator direct_end() const {
      return std::end(cfgDirCallsites_);
    }

    const_direct_call_iterator direct_cbegin() const {
      return cfgDirCallsites_.cbegin();
    }

    const_direct_call_iterator direct_cend() const {
      return cfgDirCallsites_.cend();
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
    typedef ControlFlowGraph::edge_iterator cfg_iterator;
    typedef ControlFlowGraph::const_edge_iterator const_cfg_iterator;

    cfg_iterator cfg_begin() {
      // return std::begin(cfgEdges_);
      return CFG_.edges_begin();
    }

    cfg_iterator cfg_end() {
      // return std::end(cfgEdges_);
      return CFG_.edges_end();
    }

    const_cfg_iterator cfg_begin() const {
      // return std::begin(cfgEdges_);
      return CFG_.edges_begin();
    }

    const_cfg_iterator cfg_end() const {
      // return std::end(cfgEdges_);
      return CFG_.edges_end();
    }

    const_cfg_iterator cfg_cbegin() const {
      // return cfgEdges_.cbegin();
      return CFG_.edges_cbegin();
    }

    const_cfg_iterator cfg_cend() const {
      // return cfgEdges_.cend();
      return CFG_.edges_cend();
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

        std::list<Constraint<ObjID>> constraints_;
      //}}}
    };

    // Private variables {{{
    // Constraint data
    ConstraintGraph constraintGraph_;
    ConstraintPEGraph constraintPEGraph_;

    // Control Flow Graph data {{{
    ControlFlowGraph CFG_;

    // FunctionID to call/ret nodes
    std::map<ObjID, std::pair<CFGid, CFGid>> cfgFcnToCallRet_;

    // Maps Control Flow nodes to the call functions within them
    std::map<CFGid, std::vector<ObjID>> cfgDirCallsites_;
    /*
    // Maps Control Flow nodes to the call instructions wthin them
    std::map<CFGid, std::vector<ObjID>> cfgIndirCallsites_;
    */
    // Function call -> CFG node
    std::vector<std::pair<ObjID, CFGid>> indirectCalls_;

    std::map<ObjID, std::vector<ObjID>> indirFcns_;


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

