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

#include "llvm/ADT/iterator_range.h"

class CFG {
 public:

    // Constant CFGid values {{{
    enum class CFGEnum : int32_t {
      CFGGlobalInit = 0,
      CFGInit = 1,
      CFGArgvBegin = 2,
      CFGArgvEnd = 3,
      eLastEnumValue
    };

    // Goes in the graph before CFGInit, used to store globals before we reach
    // code execution
    static const SEG::NodeID CFGGlobalInit;
    static const SEG::NodeID CFGInit;
    static const SEG::NodeID CFGArgvBegin;
    static const SEG::NodeID CFGArgvEnd;
    //}}}

    // Graph types {{{
    typedef SEG ControlFlowGraph;
    typedef SEG::NodeID NodeID;
    // Legacy... I should remove at some point
    typedef SEG::NodeID CFGid;
    //}}}

    // Nodes {{{
    class Node : public SEG::Node {
     public:
        Node(SEG::NodeID node_id) :
          SEG::Node(NodeKind::CFGNode, node_id) { }


#ifndef SPECSFS_IS_TEST
        Node(SEG::NodeID node_id, const llvm::BasicBlock *bb) :
          SEG::Node(NodeKind::CFGNode, node_id), bb_(bb) { }
#endif

        // No Copy/move {{{
        Node(const Node &) = default;
        Node(Node &&) = default;

        // No COPY!
        Node &operator=(const Node &) = delete;
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

        /*
        // Print support {{{
        void print_label(dbg_ostream &ofil,
            const ObjectMap &) const override {
          // Cant have BB dependencies in my unit tests
          if_unit_test_else(
            // If unit test
            ofil << SEG::Node::id() << " : {";
            ,  // If not unit test
            if (bb_ == nullptr) {
              ofil << SEG::Node::id() << " : {";
            } else {
              ofil << SEG::Node::id() << "(" << bb_->getName() << ")" <<
                  " : {";
            });

          ofil << " } : m: " << m_ << " r: " << r_ << " c: " << c_;
        }
        //}}}
        */

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
        void unite(SEG &graph, SEG::Node &n) override {
          auto &node = cast<Node>(n);

          m_ |= node.m_;
          r_ |= node.r_;
          c_ |= node.c_;

          uses_.insert(std::begin(node.uses_), std::end(node.uses_));
          defs_.insert(std::begin(node.defs_), std::end(node.defs_));


          SEG::Node::unite(graph, n);
        }
        //}}}

        // Def/use tracking {{{
        bool addDef(ObjectMap::ObjID def_id) {
          // Don't allow double adds... for now
          auto ret = defs_.insert(def_id);
          assert(ret.second);
          return ret.second;
        }

        void clearDefs() {
          defs_.clear();
        }

        bool hasDef() const {
          return !defs_.empty();
        }

        void debug_defs() const {
          if_debug(
            dbg << "  defs.size is: " << defs_.size() << "\n";
            dbg << "  defs are:";
            for (auto id : defs_) {
              dbg << " " << id;
            }
            dbg << "\n");
        }

        bool removeUse(ObjectMap::ObjID use_id) {
          // Don't allow double adds... for now
          auto ret = uses_.erase(use_id);
          assert(ret == 1);
          return (ret == 1);
        }

        bool addUse(ObjectMap::ObjID use_id) {
          // Don't allow double adds... for now
          /*
          dbg << "Adding use: " << use_id << " to node: " << id() <<
            "\n";
          */
          auto ret = uses_.insert(use_id);

          assert(ret.second);
          return ret.second;
        }

        void clearUses() {
          uses_.clear();
        }

        bool hasUse() const {
          return !uses_.empty();
        }

        void swapUses(std::set<ObjectMap::ObjID> &new_uses) {
          uses_.swap(new_uses);
        }

        void swapDefs(std::set<ObjectMap::ObjID> &new_defs) {
          defs_.swap(new_defs);
        }

        void debug_uses() const {
          if_debug(
            dbg << "  Uses.size is: " << uses_.size() << "\n";
            dbg << "  Uses are:";
            for (auto id : uses_) {
              dbg << " " << id;
            }
            dbg << "\n");
        }
        //}}}

        // Iterate defs/uses {{{
        typedef std::set<ObjectMap::ObjID>::iterator
          def_use_iterator;
        typedef std::set<ObjectMap::ObjID>::const_iterator
          const_def_use_iterator;

        def_use_iterator defs_begin() {
          return std::begin(defs_);
        }

        def_use_iterator defs_end() {
          return std::end(defs_);
        }

        const_def_use_iterator defs_begin() const {
          return std::begin(defs_);
        }

        const_def_use_iterator defs_end() const {
          return std::end(defs_);
        }

        const_def_use_iterator defs_cbegin() const {
          return std::begin(defs_);
        }

        const_def_use_iterator defs_cend() const {
          return std::end(defs_);
        }

        def_use_iterator uses_begin() {
          return std::begin(uses_);
        }

        def_use_iterator uses_end() {
          return std::end(uses_);
        }

        /*
        const_def_use_iterator uses_begin() const {
          return std::begin(uses_);
        }

        const_def_use_iterator uses_end() const {
          return std::end(uses_);
        }

        const_def_use_iterator uses_cbegin() const {
          return std::begin(uses_);
        }

        const_def_use_iterator uses_cend() const {
          return std::end(uses_);
        }
        */
        //}}}

     private:
      // Debug Variables {{{
      if_not_unit_test(const llvm::BasicBlock *bb_ = nullptr;)
      //}}}

      // Private variables {{{
      // The objects defined/uses by this node
      std::set<ObjectMap::ObjID> defs_;
      std::set<ObjectMap::ObjID> uses_;

      // To identify p/m nodes (see computeSSA comments)
      bool m_ = false;
      // To identify r/u nodes (see computeSSA comments)
      bool r_ = false;
      // To identify constant nodes (see computeSSA comments)
      bool c_ = false;
      //}}}
    };
    //}}}

    // Constructors {{{
    CFG() {
      // Add the default nodes to the graph...
      for (int i = 0; i < static_cast<int32_t>(CFGEnum::eLastEnumValue); i++) {
        auto node_id = CFG_.addNode<Node>();
        assert(node_id.val() == i);

        auto &node = CFG_.getNode<Node>(node_id);

        // global nodes are np nodes, and relevant
        node.setM();
        node.setR();
      }
    }

    CFG(const CFG &other) :
      CFG_(other.getSEG().clone<Node>()), 
      cfgFcnToCallRet_(other.cfgFcnToCallRet_),
      cfgDirCallsites_(other.cfgDirCallsites_),
      indirectCalls_(other.indirectCalls_),
      indirFcns_(other.indirFcns_),
      cfgCallSuccessors_(other.cfgCallSuccessors_),
      cfgFunctionEntries_(other.cfgFunctionEntries_),
      cfgFunctionReturns_(other.cfgFunctionReturns_),
      objToCFG_(other.objToCFG_),
      unusedFunctions_(other.unusedFunctions_) { }
    CFG(CFG &&) = default;

    CFG &operator=(const CFG &) = delete;
    CFG &operator=(CFG &&) = default;
    //}}}

    // Setters {{{
    void cleanup() {
      CFG_.cleanGraph();
    }

    void addPred(CFGid node_id, CFGid pred_id) {
      CFG_.addPred(node_id, pred_id);
    }

    void addCallsite(CFGid call_id, ObjectMap::ObjID fcn_id, CFGid ret_id) {
      cfgDirCallsites_[call_id].push_back(fcn_id);
      cfgCallSuccessors_[call_id] = ret_id;
    }

    void addIndirectCall(CFGid call_id, ObjectMap::ObjID obj_id,
        CFGid ret_id) {
      indirectCalls_.emplace_back(obj_id, call_id);
      cfgCallSuccessors_[call_id] = ret_id;
    }

    void addLongjmp(CFGid jmp_id, const llvm::Value *env) {
      longJmps_.push_back(std::make_pair(jmp_id, env));
    }

    void addSetjmp(CFGid dest_id, const llvm::Value *env) {
      setJmps_.push_back(std::make_pair(dest_id, env));
    }

    const std::vector<std::pair<CFGid, const llvm::Value *>> &
    getLongjmps() const {
      return longJmps_;
    }

    const std::vector<std::pair<CFGid, const llvm::Value *>> &
    getSetjmps() const {
      return setJmps_;
    }

    void addFunctionStart(ObjectMap::ObjID fcn_id, CFGid id) {
      cfgFunctionEntries_[fcn_id] = id;
    }

    void addFunctionReturn(ObjectMap::ObjID fcn_id, CFGid id) {
      cfgFunctionReturns_[fcn_id] = id;
    }

    void addCallRetInfo(ObjectMap::ObjID fcn_id, CFGid call_id, CFGid ret_id) {
      cfgFcnToCallRet_[fcn_id].emplace_back(call_id, ret_id);
    }

    void addIndirFcn(ObjectMap::ObjID call_id, ObjectMap::ObjID fcn_id) {
      indirFcns_[call_id].push_back(fcn_id);
    }

    void addUnusedFunction(ObjectMap::ObjID fcn_id,
        std::vector<ConstraintGraph::ConsID> ids) {
      unusedFunctions_.emplace(std::piecewise_construct,
          std::make_tuple(fcn_id), std::make_tuple(std::move(ids)));
    }

    bool removeUnusedFunction(ConstraintGraph &cg, ObjectMap::ObjID fcn_id);

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

    const std::vector<std::pair<CFGid, CFGid>> &
    getCallRetInfo(ObjectMap::ObjID fcn_id) const {
      return cfgFcnToCallRet_.at(fcn_id);
    }

    bool hasFunctionStart(ObjectMap::ObjID fcn_id) const {
      return cfgFunctionEntries_.find(fcn_id) != std::end(cfgFunctionEntries_);
    }

    CFGid getFunctionStart(ObjectMap::ObjID fcn_id) const {
      return cfgFunctionEntries_.at(fcn_id);
    }

    bool hasFunctionReturn(ObjectMap::ObjID fcn_id) const {
      return cfgFunctionReturns_.find(fcn_id) != std::end(cfgFunctionReturns_);
    }

    CFGid getFunctionReturn(ObjectMap::ObjID fcn_id) const {
      return cfgFunctionReturns_.at(fcn_id);
    }

    CFGid getCallSuccessor(CFGid call_id) const {
      return cfgCallSuccessors_.at(call_id);
    }

    bool haveIndirFcn(ObjectMap::ObjID call_id) const {
      return indirFcns_.find(call_id) != std::end(indirFcns_);
    }

    const std::vector<ObjectMap::ObjID>
        &getIndirFcns(ObjectMap::ObjID call_id) const {
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
    bool addUse(CFGid cfg_id, ObjectMap::ObjID load_dest_id) {
      if (static_cast<int32_t>(load_dest_id) == 210796) {
        llvm::dbgs() << "HAVE NODE: " << load_dest_id << "!\n";
        assert(0);
      }
      auto &node = CFG_.getNode<Node>(cfg_id);

      node.addUse(load_dest_id);

      auto ret = objToCFG_.emplace(load_dest_id, cfg_id);
      assert(ret.second);
      return ret.second;
    }

    bool addDef(CFGid cfg_id, ObjectMap::ObjID store_id) {
      if (static_cast<int32_t>(store_id) == 210796) {
        llvm::dbgs() << "HAVE DEF NODE: " << store_id << "!\n";
        assert(0);
      }
      auto &node = CFG_.getNode<Node>(cfg_id);

      node.addDef(store_id);

      auto ret = objToCFG_.emplace(store_id, cfg_id);
      assert(ret.second);
      return ret.second;
    }

    bool eraseObjToCFG(ObjectMap::ObjID obj_id) {
      size_t ret = objToCFG_.erase(obj_id);
      assert(ret == 1);
      return ret == 1;
    }
    //}}}

    // Accessors {{{
    CFGid getCFGid(ObjectMap::ObjID obj_id) const {
      return objToCFG_.at(obj_id);
    }

    bool isCallRet(ObjectMap::ObjID obj_id) const {
      return cfgFunctionReturns_.find(obj_id) == std::end(cfgFunctionReturns_);
    }

    void swapObjToCFG(std::map<ObjectMap::ObjID, CFGid> &mapping) {
      objToCFG_.swap(mapping);
    }

    void swapFunctionStarts(std::map<ObjectMap::ObjID, CFGid> &mapping) {
      cfgFunctionEntries_.swap(mapping);
    }

    void swapFunctionReturns(std::map<ObjectMap::ObjID, CFGid> &mapping) {
      cfgFunctionReturns_.swap(mapping);
    }

    bool isStrong(ObjectMap::ObjID) const {
      return false;
    }
    //}}}
    //}}}

    // Unique Identifier Generator {{{
    CFGid nextNode() {
      return CFG_.addNode<Node>();
    }

#ifndef SPECSFS_IS_TEST
    CFGid nextNode(const llvm::BasicBlock *bb) {
      return CFG_.addNode<Node>(bb);
    }
#endif
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

    // Function to CFG iterators {{{
    typedef std::map<ObjectMap::ObjID, CFGid>::iterator  // NOLINT
      fcn_cfg_iterator;
    typedef std::map<ObjectMap::ObjID, CFGid>::const_iterator  // NOLINT
      const_fcn_cfg_iterator;

    const_fcn_cfg_iterator function_start_begin() const {
      return std::begin(cfgFunctionEntries_);
    }

    const_fcn_cfg_iterator function_start_end() const {
      return std::end(cfgFunctionEntries_);
    }

    const_fcn_cfg_iterator function_ret_begin() const {
      return std::begin(cfgFunctionReturns_);
    }

    const_fcn_cfg_iterator function_ret_end() const {
      return std::end(cfgFunctionReturns_);
    }

    llvm::iterator_range<const_fcn_cfg_iterator> function_starts() const {
      return llvm::iterator_range<const_fcn_cfg_iterator>(cfgFunctionEntries_);
    }

    llvm::iterator_range<const_fcn_cfg_iterator> function_rets() const {
      return llvm::iterator_range<const_fcn_cfg_iterator>(cfgFunctionReturns_);
    }
    //}}}

    // Def/use/global init Iterators {{{
    //}}}

    // CFG Iterators {{{

    typedef std::map<ObjectMap::ObjID, CFGid>::iterator  // NOLINT
      obj_to_cfg_iterator;
    typedef std::map<ObjectMap::ObjID, CFGid>::const_iterator  // NOLINT
      const_obj_to_cfg_iterator;
    typedef std::pair<ObjectMap::ObjID, CFGid>
      obj_to_cfg_type;

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

    llvm::iterator_range<const_obj_to_cfg_iterator> obj_to_cfg() {
      return llvm::iterator_range(objToCFG_);
    }
    //}}}
    //}}}

    // Update {{{
    void updateObjIDs(const util::ObjectRemap<ObjectMap::ObjID> &remap) {
      // Update all of the object ids...
      auto do_remap = [&remap] (const ObjectMap::ObjID &id) { return remap[id]; };
      auto do_remap_key =
        [&remap] (const std::pair<ObjectMap::ObjID, CFGid> &pr) {
          return std::make_pair(remap[pr.first], pr.second);
        };
      auto do_remap_unused =
        [&remap] (std::pair<const ObjectMap::ObjID,
            std::vector<ConstraintGraph::ConsID>> &pr) {
          return std::make_pair(remap[pr.first], std::move(pr.second));
        };

      // First the dirCallsites
      for (auto &pr : cfgDirCallsites_) {
        std::transform(std::begin(pr.second), std::end(pr.second),
            std::begin(pr.second), do_remap);
      }

      // Then indirFcns
      {
        for (auto &pr : indirectCalls_) {
          pr.first = remap[pr.first];
        }

        std::map<ObjectMap::ObjID, std::vector<ObjectMap::ObjID>> new_indir_fcns;
        for (auto &pr : indirFcns_) {
          std::vector<ObjectMap::ObjID> new_vec(pr.second.size());
          std::transform(std::begin(pr.second), std::end(pr.second),
              std::begin(new_vec), do_remap);
          new_indir_fcns.emplace(remap[pr.first], std::move(new_vec));
        }
        indirFcns_ = std::move(new_indir_fcns);
      }

      // then FunctionEntries
      {
        std::map<ObjectMap::ObjID, CFGid> new_fcn_entries;
        std::transform(std::begin(cfgFunctionEntries_),
            std::end(cfgFunctionEntries_),
            std::inserter(new_fcn_entries, std::end(new_fcn_entries)),
            do_remap_key);
        cfgFunctionEntries_ = std::move(new_fcn_entries);
      }

      // Function Returns
      {
        std::map<ObjectMap::ObjID, CFGid> new_fcn_returns;
        std::transform(std::begin(cfgFunctionReturns_),
            std::end(cfgFunctionReturns_),
            std::inserter(new_fcn_returns, std::end(new_fcn_returns)),
            do_remap_key);
        cfgFunctionReturns_ = std::move(new_fcn_returns);
      }

      // objToCFG
      {
        std::map<ObjectMap::ObjID, CFGid> new_obj_to_cfg;
        std::transform(std::begin(objToCFG_),
            std::end(objToCFG_),
            std::inserter(new_obj_to_cfg, std::end(new_obj_to_cfg)),
            do_remap_key);
        objToCFG_ = std::move(new_obj_to_cfg);
      }

      // unusedFunctions
      {
        std::map<ObjectMap::ObjID, std::vector<ConstraintGraph::ConsID>>
          new_unused_functions;
        std::transform(std::begin(unusedFunctions_),
            std::end(unusedFunctions_),
            std::inserter(new_unused_functions, std::end(new_unused_functions)),
            do_remap_unused);
        unusedFunctions_ = std::move(new_unused_functions);
      }
    }
    //}}}

 private:
    // Control Flow Graph data {{{
    ControlFlowGraph CFG_;

    // FunctionCFGid to call/ret nodes
    std::map<ObjectMap::ObjID, std::vector<std::pair<CFGid, CFGid>>>
      cfgFcnToCallRet_;

    // Maps Control Flow nodes to the call functions within them
    std::map<CFGid, std::vector<ObjectMap::ObjID>> cfgDirCallsites_;

    // Function call -> CFG node
    std::vector<std::pair<ObjectMap::ObjID, CFGid>> indirectCalls_;
    std::map<ObjectMap::ObjID, std::vector<ObjectMap::ObjID>> indirFcns_;

    // set/longjmp
    std::vector<std::pair<CFGid, const llvm::Value *>> setJmps_;
    std::vector<std::pair<CFGid, const llvm::Value *>> longJmps_;

    // The return CFG node associated with each CFG containing a call
    std::map<CFGid, CFGid> cfgCallSuccessors_;

    // The CFG call node for each call instruciton
    std::map<ObjectMap::ObjID, CFGid> cfgFunctionEntries_;

    // The CFG node for each call instruction's return
    std::map<ObjectMap::ObjID, CFGid> cfgFunctionReturns_;
    std::map<ObjectMap::ObjID, CFGid> objToCFG_;

    // List of functions that have no obvious uses
    std::map<ObjectMap::ObjID, std::vector<ConstraintGraph::ConsID>> unusedFunctions_;

    //}}}
};

#endif  // INCLUDE_CONTROLFLOWGRAPH_H_
