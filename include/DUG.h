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
#include "include/SolveHelpers.h"


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

    // NOTE: I use int32_t's for size reasons...
    struct pe_id { };
    typedef ID<pe_id, int32_t> PEid;

    /* -- We switched this to pair<ObjID, ObjID>
    struct con_id { };
    typedef ID<con_id, int32_t, -1> ConsID;
    */

    // Control Flow graph ids
    struct cfg_id { };
    typedef ID<cfg_id, int32_t, -1> CFGid;

    struct part_id { };
    typedef ID<part_id, int32_t> PartID;

    //}}}

    // Constant ID values {{{
    enum class CFGEnum : int32_t {
      CFGInit = 0,
      eLastEnumValue
    };

    static const CFGid CFGInit;
    //}}}

    // Internal classes {{{
    // SEGNodeGroup {{{
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
              old_node, convert) {
        oids.insert(old_node.id());

        if (auto pun = llvm::dyn_cast<UnifyNode<ObjID>>(&old_node)) {
          auto &node = *pun;

          std::for_each(node.rep_begin(), node.rep_end(),
              [this](ObjID oid) {
            oids.insert(oid);
          });
        }
      }
      //}}}

      // Printing for DOT debugging {{{
      void print_label(llvm::raw_ostream &ofil,
          const ObjectMap &omap) const override {
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
      //}}}

      // Unite/merge overrides {{{
      void unite(SEG<PEid> &graph, SEGNode<PEid> &n) override {
        auto &grp = llvm::cast<SEGNodeGroup>(n);

        oids.insert(std::begin(grp.oids), std::end(grp.oids));

        UnifyNode<PEid>::unite(graph, n);
      }

      void merge(const SEGNode<PEid> &n) override {
        auto &grp = llvm::cast<SEGNodeGroup>(n);

        oids.insert(std::begin(grp.oids), std::end(grp.oids));

        UnifyNode<PEid>::merge(n);
      }
      //}}}

      // For llvm RTTI {{{
      static bool classof(const SEGNode<PEid> *node) {
        return node->getKind() == NodeKind::SEGNodeGroup;
      }
      //}}}

      std::set<ObjID> oids;
      //}}}
    };
    //}}}

    // ConstraintNode {{{
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
    //}}}

    // CFGNodes {{{
    class CFGNode : public SCCNode<CFGid> {
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

        bool u() const {
          return !r();
        }

        bool c() const {
          return c_;
        }
        //}}}

        // Print support {{{
        void print_label(llvm::raw_ostream &ofil,
            const ObjectMap &) const override {
          ofil << SEGNode<CFGid>::id() << " : {";

          std::for_each(UnifyNode<CFGid>::rep_begin(),
              UnifyNode<CFGid>::rep_end(),
              [&ofil] (CFGid rep) {
            ofil << " " << rep;
          });

          ofil << " } : m: " << m_ << " r: " << r_ << " c: " << c_;
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

        void clearM() {
          m_ = false;
        }

        void clearR() {
          r_ = false;
        }

        void clearC() {
          c_ = false;
        }
        //}}}

        // Unite {{{
        void unite(SEG<CFGid> &graph, SEGNode<CFGid> &n) override {
          auto &node = llvm::cast<CFGNode>(n);

          m_ |= node.m_;
          r_ |= node.r_;
          c_ |= node.c_;

          SCCNode<CFGid>::unite(graph, n);
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

    // Top-level Construction Methods {{{
    ConsID add(ConstraintType, ObjID d, ObjID s, int32_t o = 0);

    const Constraint<ObjID>  &getConstraint(ConsID id) const {
      return llvm::cast<Constraint<ObjID>>(constraintGraph_.getEdge(id));
    }

    ObjID addNode(ObjectMap &omap);

    void addUnusedFunction(ObjID fcn_id, std::vector<ConsID> ids) {
      unusedFunctions_.emplace(std::piecewise_construct,
          std::make_tuple(fcn_id), std::make_tuple(std::move(ids)));
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

    // Populate the top level DUG information.
    // This means creating a node for each Pointer Equivalent enetity (PEid),
    //   and creating edges for each of the top level variables
    void fillDUGTopLevel();
    //}}}

    // DUG Construction Methods {{{
    ObjID addDUGphi();
    void addDUGEdge(ObjID src, ObjID dest, PartID part);
    //}}}

    // Def/use/global tracking {{{
    // Setters {{{
    void addUse(CFGid cfg_id, ObjID cons_dest_id) {
      uses_[cfg_id].push_back(cons_dest_id);
      objToCFG_[cons_dest_id] = std::make_pair(cfg_id, ConstraintType::Load);
    }

    void addDef(CFGid cfg_id, ObjID cons_dest_id) {
      defs_[cfg_id].push_back(cons_dest_id);
      objToCFG_[cons_dest_id] = std::make_pair(cfg_id, ConstraintType::Store);
    }

    void addGlobalInit(ObjID glbl_id) {
      globalInits_.push_back(glbl_id);
      objToCFG_[glbl_id] = std::make_pair(CFGInit, ConstraintType::Store);
    }
    //}}}

    // Accessors {{{
    CFGid getCFGid(ObjID obj_id) const {
      return objToCFG_.at(obj_id).first;
    }

    ConstraintType getType(ObjID obj_id) const {
      return objToCFG_.at(obj_id).second;
    }

    bool isStrong(ObjID) const {
      return false;
    }
    //}}}
    //}}}

    // CFG tracking {{{
    // Setters {{{

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
      auto ret = cfgIdGenerator_.next();

      CFG_.addNode<CFGNode>(ret);

      return ret;
    }
    //}}}
    //}}}

    // Equivalence mappings {{{
    // PE stuffs
    void setPEs(std::map<ObjID, PEid> mapping) {
      objToPE_ = std::move(mapping);
    }

    PEid getPE(ObjID id) const {
      PEid ret;
      auto it = objToPE_.find(id);
      if (it != std::end(objToPE_)) {
        ret = it->second;
      }

      return ret;
    }


    // Parititon stuffs:
    void setPartitions(std::map<ObjID, PartID> mapping,
        std::map<PartID, std::vector<ObjID>> rev_mapping) {
      partitionMap_ = std::move(mapping);
      revPartitionMap_ = std::move(rev_mapping);
    }

    PartID getPartition(ObjID id) const {
      PartID ret;

      auto it = partitionMap_.find(id);
      if (it != std::end(partitionMap_)) {
        return it->second;
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

    // Def/use/global init Iterators {{{
    typedef std::map<CFGid, std::vector<ObjID>>::const_iterator
      const_def_use_iterator;

    typedef std::vector<ObjID>::const_iterator
      const_glbl_init_iterator;

    const_def_use_iterator defs_begin() const {
      return std::begin(defs_);
    }

    const_def_use_iterator defs_end() const {
      return std::end(defs_);
    }

    const_def_use_iterator uses_begin() const {
      return std::begin(uses_);
    }

    const_def_use_iterator uses_end() const {
      return std::end(uses_);
    }

    const_glbl_init_iterator global_inits_begin() const {
      return std::begin(globalInits_);
    }

    const_glbl_init_iterator global_inits_end() const {
      return std::end(globalInits_);
    }
    //}}}

    // CFG Iterators {{{
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

    // Partition map iterators {{{
    typedef std::map<PartID, std::vector<ObjID>>::const_iterator
      const_part_iterator;

    const_part_iterator part_begin() const {
      return std::begin(revPartitionMap_);
    }

    const_part_iterator part_end() const {
      return std::end(revPartitionMap_);
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
    class DUGNode : public SEGNode<PEid> {
      //{{{
     public:
       // Constructors {{{
        DUGNode(NodeKind kind, int32_t nodenum, PEid dest, PEid src) :
          SEGNode<PEid>(kind, nodenum, dest), dest_(dest), src_(src) { }
       //}}}

        // For llvm RTTI {{{
        bool classof(const SEGNode<PEid> *node) {
          return node->getKind() >= NodeKind::DUGNode &&
            node->getKind() < NodeKind::DUGNodeEnd;
        }

        virtual void process(PtstoData &pts, Worklist &wl) = 0;
        //}}}
     protected:
        // Private variables {{{
        PEid dest_;
        PEid src_;
        //}}}
      //}}}
    };

    // Different DUG node types {{{
    class AllocNode : public DUGNode {
      //{{{
     public:
        AllocNode(int32_t nodenum, PEid dest, PEid src) :
          DUGNode(NodeKind::AllocNode, nodenum, dest, src) { }

        void process(PtstoData &pts, Worklist &wl) override;

        bool classof(const SEGNode<PEid> *node) {
          return node->getKind() == NodeKind::AllocNode;
        }
      //}}}
    };

    class CopyNode : public DUGNode {
      //{{{
     public:
        CopyNode(int32_t nodenum, PEid dest, PEid src, PtstoSet in) :
          DUGNode(NodeKind::CopyNode, nodenum, dest, src),
          in_(std::move(in)) { }


        void process(PtstoData &pts, Worklist &wl) override;

        bool classof(const SEGNode<PEid> *node) {
          return node->getKind() == NodeKind::CopyNode;
        }

     private:
        PtstoSet in_;
      //}}}
    };

    class LoadNode : public DUGNode {
      //{{{
     public:
        LoadNode(int32_t nodenum, PEid dest, PEid src, PtstoSet in) :
          DUGNode(NodeKind::LoadNode, nodenum, dest, src),
          in_(std::move(in)) { }


        void process(PtstoData &pts, Worklist &wl) override;

        bool classof(const SEGNode<PEid> *node) {
          return node->getKind() == NodeKind::LoadNode;
        }

     private:
        PtstoSet in_;
      //}}}
    };

    class StoreNode : public DUGNode {
      //{{{
     public:
        StoreNode(int32_t nodenum, PEid dest, PEid src, PtstoSet in,
            PtstoSet out, std::set<PEid> part_succ) :
          DUGNode(NodeKind::StoreNode, nodenum, dest, src),
          in_(std::move(in)), out_(std::move(out)),
          part_succ_(std::move(part_succ)) { }


        void process(PtstoData &pts, Worklist &wl) override;

        bool classof(const SEGNode<PEid> *node) {
          return node->getKind() == NodeKind::StoreNode;
        }

     private:
        PtstoSet in_;
        PtstoSet out_;

        // Successor partitons -- Used to update worklist on process
        std::set<PEid> part_succ_;
      //}}}
    };

    class PhiNode : public DUGNode {
      //{{{
     public:
        PhiNode(int32_t nodenum, PEid dest, PEid src, PtstoSet in) :
          DUGNode(NodeKind::PhiNode, nodenum, dest, src),
          in_(std::move(in)) { }

        void process(PtstoData &pts, Worklist &wl) override;

        bool classof(const SEGNode<PEid> *node) {
          return node->getKind() == NodeKind::PhiNode;
        }
     private:
        PtstoSet in_;
      //}}}
    };
    //}}}

    // Private variables {{{
    // Constraint data
    ConstraintGraph constraintGraph_;

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
    // Also global variable inits... similar to defs... but only for GV initial
    //   values
    std::map<CFGid, std::vector<ObjID>> defs_;
    std::map<CFGid, std::vector<ObjID>> uses_;
    // Notation of ObjID's associated with global inits.  These inits are
    //   each associated with the CFGInit CFGid (before main)
    std::vector<ObjID> globalInits_;

    // ID Generator for CFGids
    IDGenerator<CFGid, static_cast<int32_t>(CFGEnum::eLastEnumValue)>
      cfgIdGenerator_;
    //}}}

    std::map<ObjID, std::pair<CFGid, ConstraintType>> objToCFG_;

    // The PE equivalent for each obj in the graph
    std::map<ObjID, PEid> objToPE_;

    // The Partition equivalence for each object in the graph
    std::map<ObjID, PartID> partitionMap_;
    std::map<PartID, std::vector<ObjID>> revPartitionMap_;

    // List of functions that have no obvious uses
    std::map<ObjID, std::vector<ConsID>> unusedFunctions_;

    SEG<PEid> DUG_;
    //}}}
  //}}}
};

#endif  // INCLUDE_DUG_H_

