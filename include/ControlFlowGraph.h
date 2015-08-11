/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_CONTROLFLOWGRAPH_H_
#define INCLUDE_CONTROLFLOWGRAPH_H_

#include <map>
#include <vector>

#include "include/util.h"
#include "include/ConstraintGraph.h"
#include "include/SEG.h"

class CFG {
 public:

    // Id Types {{{
    // Control Flow graph ids
    struct cfg_id { };
    typedef ID<cfg_id, int32_t, -1> CFGid;
    //}}}

    // Constant CFGid values {{{
    enum class CFGEnum : int32_t {
      CFGInit = 0,
      eLastEnumValue
    };

    static const CFGid CFGInit;
    //}}}

    // Graph types {{{
    typedef SEG<CFGid> ControlFlowGraph;
    typedef SEG<CFGid>::NodeID NodeID;
    typedef SEG<CFGid>::EdgeID EdgeID;
    //}}}

    // Constructors {{{
    CFG() = default;

    CFG(const CFG &other) :
      CFG_(other.getSEG().clone<Node, Edge>()) { }
    CFG(CFG &&) = default;

    CFG &operator=(const CFG &) = delete;
    CFG &operator=(CFG &&) = default;
    //}}}

    // Nodes {{{
    class Node : public UnifyNode<CFGid> {
     public:
        Node(SEG<CFGid>::NodeID node_id, CFGid id) :
          UnifyNode<CFGid>(NodeKind::CFGNode, node_id, id) { }

        // No Copy/move {{{
        Node(const Node &) = default;
        Node(Node &&) = default;

        Node &operator=(const Node &) = default;
        Node &operator=(Node &&) = default;
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
          ofil << SEGNode<CFGid>::extId() << " : {";

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
          auto &node = llvm::cast<Node>(n);

          m_ |= node.m_;
          r_ |= node.r_;
          c_ |= node.c_;

          UnifyNode<CFGid>::unite(graph, n);
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

    // Edges {{{
    class Edge : public SEGEdge<CFGid> {
     public:
        typedef typename SEG<CFGid>::NodeID NodeID;
        Edge(NodeID dest, NodeID src) :
            SEGEdge<CFGid>(EdgeKind::CFGEdge, dest, src) { }

     private:
    };
    //}}}

    // Setters {{{

    void addEdge(CFGid cfg_id1, CFGid cfg_id2) {
      auto node_id1 = getNode(cfg_id1).id();
      auto node_id2 = getNode(cfg_id2).id();
      CFG_.addEdge<Edge>(node_id1, node_id2);
    }

    void addCallsite(CFGid call_id, ConstraintGraph::ObjID fcn_id, CFGid ret_id) {
      cfgDirCallsites_[call_id].push_back(fcn_id);
      cfgCallSuccessors_[call_id] = ret_id;
    }

    void addIndirectCall(CFGid call_id, ConstraintGraph::ObjID obj_id,
        CFGid ret_id) {
      // Don't think I actually need this... I'm using another function
      // instead... I should clean it up at some point
      // cfgIndirCallsites_[call_id].push_back(call_insn_id);
      indirectCalls_.emplace_back(obj_id, call_id);
      cfgCallSuccessors_[call_id] = ret_id;
    }

    void addFunctionStart(ConstraintGraph::ObjID fcn_id, CFGid id) {
      cfgFunctionEntries_[fcn_id] = id;
    }

    void addFunctionReturn(ConstraintGraph::ObjID fcn_id, CFGid id) {
      cfgFunctionReturns_[fcn_id] = id;
    }

    void addCallRetInfo(ConstraintGraph::ObjID fcn_id, CFGid call_id, CFGid ret_id) {
      cfgFcnToCallRet_.emplace(fcn_id, std::make_pair(call_id, ret_id));
    }

    void addIndirFcn(ConstraintGraph::ObjID call_id, ConstraintGraph::ObjID fcn_id) {
      indirFcns_[call_id].push_back(fcn_id);
    }

    void addUnusedFunction(ConstraintGraph::ObjID fcn_id,
        std::vector<ConstraintGraph::ConsID> ids) {
      unusedFunctions_.emplace(std::piecewise_construct,
          std::make_tuple(fcn_id), std::make_tuple(std::move(ids)));
    }

    bool removeUnusedFunction(ConstraintGraph &cg, ConstraintGraph::ObjID fcn_id);

    void setSEG(ControlFlowGraph seg) {
      CFG_ = std::move(seg);
    }
    //}}}

    // Accessors {{{
    Node &getNode(NodeID id) {
      return CFG_.getNode<Node>(id);
    }

    const Node &getNode(NodeID id) const {
      return CFG_.getNode<Node>(id);
    }

    Node &getNode(CFGid id) {
      auto pr = CFG_.getNodes(id);
      assert(std::distance(pr.first, pr.second) == 1);

      return getNode(pr.first->second);
    }

    const Node &getNode(CFGid id) const {
      auto pr = CFG_.getNodes(id);
      assert(std::distance(pr.first, pr.second) == 1);

      return getNode(pr.first->second);
    }

    const std::pair<CFGid, CFGid> &
    getCallRetInfo(ConstraintGraph::ObjID fcn_id) const {
      return cfgFcnToCallRet_.at(fcn_id);
    }

    CFGid getFunctionStart(ConstraintGraph::ObjID fcn_id) const {
      return cfgFunctionEntries_.at(fcn_id);
    }

    CFGid getFunctionReturn(ConstraintGraph::ObjID fcn_id) const {
      return cfgFunctionReturns_.at(fcn_id);
    }

    CFGid getCallSuccessor(CFGid call_id) const {
      return cfgCallSuccessors_.at(call_id);
    }

    const std::vector<ConstraintGraph::ObjID> &getIndirFcns(ConstraintGraph::ObjID call_id) const {
      return indirFcns_.at(call_id);
    }

    const ControlFlowGraph &getSEG() const {
      return CFG_;
    }

    ControlFlowGraph &getSEG() {
      return CFG_;
    }
    //}}}

    // Def/use/global tracking {{{
    // Setters {{{
    void addUse(CFGid cfg_id, ObjectMap::ObjID cons_dest_id) {
      uses_[cfg_id].push_back(cons_dest_id);
      objToCFG_[cons_dest_id] = std::make_pair(cfg_id, ConstraintType::Load);
    }

    void addDef(CFGid cfg_id, ObjectMap::ObjID cons_dest_id) {
      defs_[cfg_id].push_back(cons_dest_id);
      objToCFG_[cons_dest_id] = std::make_pair(cfg_id, ConstraintType::Store);
    }

    void addGlobalInit(ObjectMap::ObjID glbl_id) {
      globalInits_.push_back(glbl_id);
      objToCFG_[glbl_id] = std::make_pair(CFGInit, ConstraintType::Store);
    }
    //}}}

    // Accessors {{{
    CFGid getCFGid(ObjectMap::ObjID obj_id) const {
      return objToCFG_.at(obj_id).first;
    }

    ConstraintType getType(ObjectMap::ObjID obj_id) const {
      return objToCFG_.at(obj_id).second;
    }

    bool isStrong(ObjectMap::ObjID) const {
      return false;
    }
    //}}}
    //}}}

    // Unique Identifier Generator {{{
    CFGid nextNode() {
      auto ret = idGenerator_.next();

      CFG_.addNode<Node>(ret);

      return ret;
    }
    //}}}

    // Iterators {{{
    // Indirect Call Iterators {{{
    typedef std::vector<std::pair<ObjectMap::ObjID, CFGid>>::iterator
      indirect_call_iterator;
    typedef std::vector<std::pair<ObjectMap::ObjID, CFGid>>::const_iterator
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
    typedef std::map<CFGid, std::vector<ObjectMap::ObjID>>::iterator
      direct_call_iterator;
    typedef std::map<CFGid, std::vector<ObjectMap::ObjID>>::const_iterator
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
    typedef std::map<ObjectMap::ObjID, std::vector<ConstraintGraph::ConsID>>::iterator // NOLINT
      unused_function_iterator;
    typedef std::map<ObjectMap::ObjID, std::vector<ConstraintGraph::ConsID>>::const_iterator  // NOLINT
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
    typedef std::map<CFGid, std::vector<ObjectMap::ObjID>>::const_iterator
      const_def_use_iterator;

    typedef std::vector<ObjectMap::ObjID>::const_iterator
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

    typedef std::map<ObjectMap::ObjID, std::pair<CFGid, ConstraintType>>::iterator  // NOLINT
      obj_to_cfg_iterator;
    typedef std::map<ObjectMap::ObjID, std::pair<CFGid, ConstraintType>>::const_iterator  // NOLINT
      const_obj_to_cfg_iterator;
    typedef std::pair<ObjectMap::ObjID, std::pair<CFGid, ConstraintType>>
      obj_to_cfg_type;

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

    const_obj_to_cfg_iterator obj_to_cfg_begin() const {
      return std::begin(objToCFG_);
    }

    const_obj_to_cfg_iterator obj_to_cfg_end() const {
      return std::end(objToCFG_);
    }

    const_obj_to_cfg_iterator obj_to_cfg_cbegin() const {
      return std::begin(objToCFG_);
    }

    const_obj_to_cfg_iterator obj_to_cfg_cend() const {
      return std::end(objToCFG_);
    }
    //}}}
    //}}}

 private:
    // Control Flow Graph data {{{
    ControlFlowGraph CFG_;

    // FunctionCFGid to call/ret nodes
    std::map<ObjectMap::ObjID, std::pair<CFGid, CFGid>> cfgFcnToCallRet_;

    // Maps Control Flow nodes to the call functions within them
    std::map<CFGid, std::vector<ObjectMap::ObjID>> cfgDirCallsites_;

    // Function call -> CFG node
    std::vector<std::pair<ObjectMap::ObjID, CFGid>> indirectCalls_;

    std::map<ObjectMap::ObjID, std::vector<ObjectMap::ObjID>> indirFcns_;

    // The return CFG node associated with each CFG containing a call
    std::map<CFGid, CFGid> cfgCallSuccessors_;
    // The CFG call node for each call instruciton
    std::map<ObjectMap::ObjID, CFGid> cfgFunctionEntries_;
    // The CFG node for each call instruction's return
    std::map<ObjectMap::ObjID, CFGid> cfgFunctionReturns_;

    // Defs/uses represented at each CFG node, used to assicate calculated SSA
    // info back to contraints
    // Also global variable inits... similar to defs... but only for GV initial
    //   values
    std::map<CFGid, std::vector<ObjectMap::ObjID>> defs_;
    std::map<CFGid, std::vector<ObjectMap::ObjID>> uses_;

    // Notation of ConstraintGraph::ObjID's associated with global inits.  These inits are
    //   each associated with the CFGInit CFGid (before main)
    std::vector<ObjectMap::ObjID> globalInits_;

    std::map<ObjectMap::ObjID, std::pair<CFGid, ConstraintType>> objToCFG_;

    // List of functions that have no obvious uses
    std::map<ObjectMap::ObjID, std::vector<ConstraintGraph::ConsID>> unusedFunctions_;

    // CFGid Generator for CFGids
    IDGenerator<CFGid, static_cast<int32_t>(CFGEnum::eLastEnumValue)>
      idGenerator_;
    //}}}
};

#endif  // INCLUDE_CONTROLFLOWGRAPH_H_
