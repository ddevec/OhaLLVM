/*
 * Copyright (C) 2015 David Devecsery
 */

#include <algorithm>
#include <fstream>
#include <limits>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "include/util.h"
#include "include/ConstraintPass.h"
#include "include/DUG.h"
#include "include/InstLabeler.h"
#include "include/LLVMHelper.h"
#include "include/ObjectMap.h"
#include "include/Tarjans.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"
#include "include/lib/DynPtsto.h"
#include "include/lib/DynAlias.h"

#include "llvm/Constants.h"
#include "llvm/Pass.h"
#include "llvm/PassSupport.h"
#include "llvm/Function.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Module.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ProfileInfo.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Support/InstIterator.h"


static llvm::cl::opt<std::string>
  fcn_name("slice-debug-fcn", llvm::cl::init("main"),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("The function to debug slicing on, default=main"));

static llvm::cl::opt<std::string>
  outfilename("slice-outfile", llvm::cl::init("slices.out"),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("file containing static slice output numbers"));

static llvm::cl::opt<bool>
  do_main_slice("slice-do-main", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc("Creates slices of \"main\""));

static llvm::cl::opt<bool>
  do_rand_slice("slice-do-random", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc("Creates random slices"));

static llvm::cl::opt<bool>
  force_alias("slice-force-dyn-alias", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc("Does load-store aliasing based on the "
        "DynAliasLoader pass"));

static llvm::cl::opt<bool>
  no_control_flow("slice-no-control-flow", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc("Disables control-flow tracking for slices"));

static llvm::cl::opt<std::string>
  rand_slice_count_str("slice-random-count", llvm::cl::init("10"),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("Random slice count"));

static llvm::cl::opt<std::string>
  rand_slice_seed_str("slice-random-seed", llvm::cl::init("1"),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("Random slice seed"));

class FunctionCallInfo {
  //{{{
 public:
  typedef std::map<const llvm::Value *, std::set<const llvm::Value *>>
    FcnMap;

  FunctionCallInfo() = default;
  FunctionCallInfo(FcnMap callsite_to_fcn, FcnMap fcn_to_callsite,
          FcnMap arg_to_callsite, FcnMap rets_of_fcn,
          const UnusedFunctions *dyn_info) :
        callsiteToFcns_(std::move(callsite_to_fcn)),
        fcnToCallsite_(std::move(fcn_to_callsite)),
        argToCallsite_(std::move(arg_to_callsite)),
        retsOfFunc_(std::move(rets_of_fcn)),
        dynInfo_(dyn_info) { }

  FunctionCallInfo &operator=(FunctionCallInfo &&) = default;

  const FcnMap &getCallsiteToFcn() const {
    return callsiteToFcns_;
  }

  const FcnMap &getFcnToCallsite() const {
    return fcnToCallsite_;
  }

  const FcnMap &getArgToCallsite() const {
    return argToCallsite_;
  }

  const FcnMap &getRetsOfFunc() const {
    return retsOfFunc_;
  }

  const UnusedFunctions *getDynInfo() const {
    return dynInfo_;
  }

 private:
  FcnMap callsiteToFcns_;
  FcnMap fcnToCallsite_;
  FcnMap argToCallsite_;
  FcnMap retsOfFunc_;

  const UnusedFunctions *dynInfo_;
  //}}}
};

typedef std::unordered_map<const llvm::Function *, SEG::NodeID>
    NodeMap;

class FunctionNode : public SEG::Node {
  //{{{
 public:
  explicit FunctionNode(SEG::NodeID node_id,
      const llvm::Function *fcn,
      const UnusedFunctions &dyn_info,
      ObjectMap &omap) :
        SEG::Node(NodeKind::HUNode, node_id),
        func_(fcn) {
    // Populate my predBBs_ LOCALLY (locally visited basic blocks)
    for (auto &bb : *fcn) {
      if (!dyn_info.isUsed(bb)) {
        continue;
      }
      predBBs_.set(omap.getValue(&bb));

      // Update my CALLEES set
      for (auto &inst : bb) {
        if (auto ci = dyn_cast<llvm::CallInst>(&inst)) {
          callees_.insert(ci);
        }
      }
    }
  }

  void addNodePreds(SEG &seg,
      const NodeMap &nmap,
      const FunctionCallInfo &call_info) {
    auto &callsite_to_fcn = call_info.getCallsiteToFcn();
    // For each callee in this function, add a pred to the SEG
    for (auto pci : callees_) {
      auto fcn_it = callsite_to_fcn.find(pci);
      if (fcn_it != std::end(callsite_to_fcn)) {
        for (auto vfcn : fcn_it->second) {
          auto fcn = cast<llvm::Function>(vfcn);
          // No edges for external functions :(
          if (!fcn->isDeclaration()) {
            // Add a pred from them to me
            seg.addPred(nmap.at(fcn), SEG::Node::id());
            /*
            llvm::dbgs() << "adding edge: " << func_->getName() <<
              " -> " << fcn->getName() << "\n";
            */
          }
        }
      }
    }
  }

  // Do our bottom up traversal to fill in callee bbs
  void addCalleePreds(SEG &seg,
      const NodeMap &nmap,
      ObjectMap &omap,
      const FunctionCallInfo &call_info) {
    // Don't process ourself twice
    if (haveCalleeBBs_) {
      return;
    }

    auto &callsite_to_fcn = call_info.getCallsiteToFcn();

    // Get all of our pred callees
    for (auto ci : callees_) {
      /*
      llvm::dbgs() << "fcn is: " <<
        cast<llvm::Function>(omap.valueAtID(callee_oid))->getName() << "\n";
      */

      auto dest_it = callsite_to_fcn.find(ci);
      if (dest_it != std::end(callsite_to_fcn)) {
        for (auto fcn : dest_it->second) {
          auto callee_id =
            nmap.at(cast<llvm::Function>(fcn));
          auto &pred = seg.getNode<FunctionNode>(callee_id);

          // Don't need to merge ourself
          if (pred.id() == SEG::Node::id()) {
            continue;
          }

          /*
          llvm::dbgs() << "Checking pred_node: " << pred.func_->getName()
            << "\n";
          */

          // Now, merge the callee's BBs
          predBBs_ |= pred.getPredBBs(seg, nmap, omap, call_info);
        }
      }
    }

    haveCalleeBBs_ = true;
  }

  void unite(SEG &seg, SEG::Node &n) override {
    auto &node = cast<FunctionNode>(n);

    // Unite the BB sets
    predBBs_ |= node.predBBs_;
    // Unite the visited sets
    callees_.insert(std::begin(node.callees_), std::end(node.callees_));

    node.callees_.clear();
    node.predBBs_.clear();

    SEG::Node::unite(seg, n);
  }

  const util::SparseBitmap<ObjectMap::ObjID> &getPredBBs(SEG &seg,
      const NodeMap &nmap,
      ObjectMap &omap,
      const FunctionCallInfo &call_info) {
    if (!haveCalleeBBs_) {
      addCalleePreds(seg, nmap, omap, call_info);
    }

    assert(haveCalleeBBs_);
    return predBBs_;
  }

 private:
  const llvm::Function *func_;
  util::SparseBitmap<ObjectMap::ObjID> predBBs_;

  // Set of call instructions within this function
  std::set<const llvm::CallInst *> callees_;
  bool haveCalleeBBs_ = false;
  //}}}
};

// Helpers to actuall manage getting the predecessor basic blocks given a
// partial stack
//{{{
// Generate a pred-graph of the function calls
//   Populate each of the function calls w/ used BBs
//   Happens on construction of node

// Then, compress sccs
//   TarjanSCC

// Then, preform a bottom-up traversal, merging callees with callers
//   Handled by addCalleePreds()

// Those are blocks visited by /that/ scc (function set)
// Use this to get pred info -- callers are pred edges (unless stack is given),
//   callees are taken care of by this algorithm
static std::pair<std::vector<const llvm::CallInst *>,
  util::SparseBitmap<ObjectMap::ObjID>>
getFcnPreds(const llvm::BasicBlock *init_bb, ObjectMap &omap,
    const UnusedFunctions *dyn_info) {
  util::SparseBitmap<ObjectMap::ObjID> bb_list;
  std::vector<const llvm::CallInst *> ci_vec;

  std::vector<const llvm::BasicBlock *> worklist;
  std::vector<const llvm::BasicBlock *> worklist_new;

  worklist.push_back(init_bb);

  while (!worklist.empty()) {
    for (auto bb : worklist) {
      auto bb_id = omap.getValue(bb);

      // If we haven't visited this bb yet
      //   (NOTE: implicitly inserts into bb_list)
      if (bb_list.test_and_set(bb_id)) {
        // Insert its preds into our worklist
        for (auto it = pred_begin(bb), en = pred_end(bb);
            it != en; ++it) {
          if (!dyn_info->isUsed(*it)) {
            continue;
          }
          worklist_new.push_back(*it);
        }

        // Also, check for call insts
        for (auto &inst : *bb) {
          if (auto ci = dyn_cast<llvm::CallInst>(&inst)) {
            ci_vec.push_back(ci);
          }
        }
      }
    }

    worklist.swap(worklist_new);
    worklist_new.clear();
  }

  return std::make_pair(std::move(ci_vec), std::move(bb_list));
}

// ALGORITHM for getting pred bbs:
static util::SparseBitmap<ObjectMap::ObjID> getPredBBs(ObjectMap::ObjID bb_id,
    const std::vector<const llvm::Instruction *> &partial_stack,
    SEG &function_graph,
    const NodeMap &nmap,
    const FunctionCallInfo &call_info,
    ObjectMap &omap) {
  // NOTE: function_graph is a DAG (because of SCC collapsing), so it is
  //   impossible that a caller is also a callee (pred != succ)
  std::unordered_set<SEG::NodeID, SEG::NodeID::hasher> caller_visited;
  auto my_bb = cast<llvm::BasicBlock>(omap.valueAtID(bb_id));
  auto my_fcn = my_bb->getParent();
  // llvm::dbgs() << "my_fcn is: " << my_fcn->getName() << "\n";
  auto my_node_id = nmap.at(my_fcn);
  auto &my_node =
    function_graph.getNode<FunctionNode>(my_node_id);
  my_node_id = my_node.id();
  caller_visited.emplace(my_node_id);

  auto &callsite_to_fcn = call_info.getCallsiteToFcn();

  // First, get all pred BBs in the function
  // Returns pair<vector<callinst>(callees), util::SparseBitmap<>(bb)>
  auto pred_pr = getFcnPreds(my_bb, omap, call_info.getDynInfo());
  auto bb_set = std::move(pred_pr.second);

  auto next_node_id = my_node_id;
  // **This deals with pred callees
  for (auto call_inst : pred_pr.first) {
    // Iterate through all the functons of that call inst
    // If they haven't been visited (caller_visited), add their bbsets to our
    //   list
    auto dest_it = callsite_to_fcn.find(call_inst);
    // NOTE: calls to declaration functions (those without callsite_to_fcn
    //    values) can be safely ignored
    if (dest_it != std::end(callsite_to_fcn)) {
      for (auto &fcn : dest_it->second) {
        auto &call_node = function_graph.getNode<FunctionNode>(nmap.at(
              cast<llvm::Function>(fcn)));
        auto fcn_id = call_node.id();
        if (caller_visited.emplace(fcn_id).second) {
          bb_set |= call_node.getPredBBs(function_graph, nmap, omap, call_info);
        }
      }
    }
  }

  // Now, deal w/ the partial stack.  Ignore the node's preds, and just do the
  //   stacked functions
  for (auto pinst : partial_stack) {
    // NOTE: We don't add the bb's function to the caller_visited list, because
    //   we are not exploring the whole function
    auto bb = pinst->getParent();

    auto caller_pred_pr = getFcnPreds(my_bb, omap, call_info.getDynInfo());

    for (auto call_inst : caller_pred_pr.first) {
      auto dest_it = callsite_to_fcn.find(call_inst);
      // NOTE: calls to declaration functions (those without callsite_to_fcn
      //    values) can be safely ignored
      if (dest_it != std::end(callsite_to_fcn)) {
        for (auto &fcn : dest_it->second) {
          auto &call_node = function_graph.getNode<FunctionNode>(nmap.at(
                cast<llvm::Function>(fcn)));
          auto fcn_id = call_node.id();
          if (caller_visited.emplace(fcn_id).second) {
            bb_set |= call_node.getPredBBs(function_graph, nmap, omap,
                call_info);
          }
        }
      }
    }

    bb_set |= caller_pred_pr.second;

    next_node_id = function_graph.getNode(nmap.at(bb->getParent())).id();
  }

  // Now, handle callers
  // -- Including calls (use seg to handle calls)
  // iterate through preds of my_node
  std::vector<SEG::NodeID> worklist;
  std::vector<SEG::NodeID> worklist_new;
  worklist.emplace_back(next_node_id);

  while (!worklist.empty()) {
    for (auto work_id : worklist) {
      auto &work_node = function_graph.getNode<FunctionNode>(work_id);

      for (auto pred_ref_id : work_node.preds()) {
        auto &pred_node = function_graph.getNode<FunctionNode>(pred_ref_id);
        auto pred_id = pred_node.id();
        auto rc = caller_visited.emplace(pred_id);

        if (rc.second) {
          // Add the predBBs from pred_node to my bb_set
          bb_set |= pred_node.getPredBBs(function_graph, nmap, omap, call_info);

          // Also, add the pred_id to my worklist
          worklist_new.emplace_back(pred_id);
        }
      }
    }

    worklist.swap(worklist_new);
    worklist_new.clear();
  }

  // Return my bb_set
  return std::move(bb_set);
}
//}}}

class StackCache {
  //{{{
 public:
  static const size_t ElementsPerArray = 512;

  struct stack_id_tag { };
  typedef util::ID<stack_id_tag> StackID;

  class StackInfo {
    //{{{
   public:
    StackInfo() = delete;
    StackInfo(std::vector<const llvm::Instruction *> stack, StackID id) :
        stack_(std::move(stack)), id_(id) { }

    // We pass these around by reference, so we cannot move or copy them
    StackInfo(const StackInfo &) = delete;
    StackInfo(StackInfo &&) = default;

    StackInfo &operator=(const StackInfo &) = delete;
    StackInfo &operator=(StackInfo &&) = delete;

    StackInfo(const std::vector<const llvm::Instruction *> &stack, StackID id,
        StackID parent_id) :
        stack_(stack), id_(id), parentId_(parent_id) { }

    const std::vector<const llvm::Instruction *> &stack() const {
      assert(this != nullptr);
      return stack_;
    }

    StackID parentId(StackCache &cache) const {
      if (parentId_ == StackID::invalid()) {
        // Get parent id:
        auto &st = stack();
        if (st.empty()) {
          parentId_ = id();
        } else if (st.size() == 1) {
          parentId_ = StackCache::EmptyStack();
        } else {
          auto parent_stack = st;
          parent_stack.pop_back();
          parentId_ = cache.getStack(parent_stack);
        }
      }
      return parentId_;
    }

    StackID id() const {
      return id_;
    }

    friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
        const StackInfo &stack) {
      o << "{";
      for (auto &elm : stack.stack()) {
        o << " " << elm;
      }
      o << " }";
      return o;
    }

   private:
    std::vector<const llvm::Instruction *> stack_;
    StackID id_;

    // mutable -- basically a cached value, so transparent to const functions
    mutable StackID parentId_ = StackID::invalid();
    //}}}
  };

  struct StackHasher {
    size_t operator()(const std::vector<const llvm::Instruction *> &stack)
          const {
      size_t hash = 0;
      std::for_each(std::begin(stack), std::end(stack),
          [&hash] (const llvm::Instruction *frame) {
        hash = stackHashCombine(hash, frame);
      });
      return hash;
    }
  };

  StackCache() {
    infoMap_.emplace(std::vector<const llvm::Instruction *>(), 0);
    stacks_.emplace_back(std::vector<const llvm::Instruction *>(), StackID(0));
  }

  static StackID EmptyStack() {
    return StackID(0);
  }

  StackID getStack(const std::vector<const llvm::Instruction *> &stack) {
    /*
    llvm::dbgs() << "emplace stack: " << stack.size() << " to id: " <<
      stacks_.size() << "\n";
    */
    auto rc = infoMap_.emplace(stack, stacks_.size());

    if (rc.second) {
      stacks_.emplace_back(stack, StackID(rc.first->second));
    }

    assert(rc.first->second < stacks_.size());
    return StackID(rc.first->second);
  }

  // now with -- /Recursion Support/
  StackID getChild(StackID st_id, const llvm::Instruction *child_site,
      const NodeMap &nmap,
      SEG &function_graph) {
    auto &inf = getStack(st_id);
    auto &oldstack = inf.stack();
    if (!oldstack.empty()) {
      auto old_fcn = oldstack.back()->getParent()->getParent();
      auto new_fcn = child_site->getParent()->getParent();

      auto old_id = function_graph.getNode(nmap.at(old_fcn)).id();
      auto new_id = function_graph.getNode(nmap.at(new_fcn)).id();

      // If recursive call, return the same stack!
      if (old_id == new_id) {
        return st_id;
      }
      // Otherwise, actually parse out the new stack
    }
    std::vector<const llvm::Instruction *> newstack(inf.stack());
    newstack.push_back(child_site);

    /*
    llvm::dbgs() << "GetChild!\n";
    llvm::dbgs() << "newstack: {";
    for (auto id : newstack) {
      llvm::dbgs() << " " << id;
    }
    llvm::dbgs() << " }\n";
    */

    auto rc = infoMap_.emplace(newstack, stacks_.size());

    // llvm::dbgs() << "rc.second: " << rc.second << "\n";

    if (rc.second) {
      /*
      llvm::dbgs() << "Creating stack in stacks_\n";
      llvm::dbgs() << "  id: " << rc.first->second << "\n";
      */
      stacks_.emplace_back(newstack, StackID(rc.first->second));
    }

    /*
    llvm::dbgs() << "stacks_.size(): " << stacks_.size() << "\n";
    llvm::dbgs() << "rc.first->second: " << rc.first->second << "\n";
    */

    assert(rc.first->second < stacks_.size());
    return StackID(rc.first->second);
  }

  StackID getParent(StackID st_id) {
    auto &inf = getStack(st_id);
    auto id = inf.parentId(*this);
    assert(static_cast<size_t>(id) < stacks_.size());
    return id;
  }

  const StackInfo &getStack(const StackID id) const {
    return stacks_[id.val()];
  }

 private:
  static size_t stackHashCombine(size_t hash, const llvm::Instruction *frame) {
    return hash ^ (hash >> 11) ^ std::hash<const void *>()(
        reinterpret_cast<const void *>(frame));
  }

  std::unordered_map<std::vector<const llvm::Instruction *>, size_t,
    StackHasher> infoMap_;

  std::vector<StackInfo> stacks_;
  //}}}
};

class ContextCache {
  //{{{
 public:
  typedef StackCache::StackInfo StackInfo;
  struct context_id_tag { };
  typedef util::ID<context_id_tag> ContextID;
  class Context {
    //{{{
   public:
    typedef StackCache::StackInfo Stack;
    typedef StackCache::StackID StackID;
    Context() = delete;
    Context(StackID si, ObjectMap::ObjID bb, ObjectMap &omap,
        const StackCache &stacks, const FunctionCallInfo &call_info,
        const NodeMap &nmap,
        SEG &function_graph) :
          stack_(si), curBB_(bb),
          predBBs_(getPredBBs(bb, stacks.getStack(si).stack(),
                function_graph, nmap, call_info, omap)) { }

    struct hasher {
      size_t operator()(const Context &c) {
        auto stack_hash = StackID::hasher()(c.stack_);
        auto bb_hash = ObjectMap::ObjID::hasher()(c.curBB_);
        bb_hash ^= bb_hash >> 11;
        bb_hash ^= stack_hash;
        return bb_hash;
      }
    };

    bool operator==(const Context &rhs) const {
      return rhs.stack_ == stack_ && rhs.curBB_ == curBB_;
    }

    const util::SparseBitmap<ObjectMap::ObjID> &predBBs() const {
      return predBBs_;
    }

    const StackCache::StackID stack() const {
      return stack_;
    }

    ObjectMap::ObjID curBB() const {
      return curBB_;
    }

   private:
    StackID stack_;
    ObjectMap::ObjID curBB_;
    util::SparseBitmap<ObjectMap::ObjID> predBBs_;
    //}}}
  };

  ContextCache() = default;

  ContextID find(StackCache::StackID stack, ObjectMap::ObjID bb_id,
      ObjectMap &omap, const StackCache &stack_info,
      const FunctionCallInfo &call_info,
      const NodeMap &nmap,
      SEG &function_graph) {
    auto rc_pr = cache_.emplace(std::piecewise_construct,
        std::make_tuple(stack, bb_id),
        std::make_tuple(contexts_.size()));

    if (rc_pr.second) {
      contexts_.emplace_back(stack, bb_id, omap, stack_info,
          call_info, nmap, function_graph);
    }

    return ContextID(rc_pr.first->second);
  }

  const Context &getContext(ContextID id) const {
    return contexts_[id.val()];
  }

 private:
  struct MapKeyHash {
    size_t operator()(const std::pair<StackCache::StackID,
        ObjectMap::ObjID> &pr) const {
      auto ret = StackCache::StackID::hasher()(pr.first);

      ret ^= ret << 11;
      ret ^= ObjectMap::ObjID::hasher()(pr.second);

      return ret;
    }
  };

  std::unordered_map<std::pair<StackCache::StackID, ObjectMap::ObjID>,
    size_t, MapKeyHash> cache_;
  std::vector<Context> contexts_;
  //}}}
};

// To do context sensitive processing we need to
class Position {
  //{{{
 public:
  typedef ContextCache::Context Context;

  Position() = delete;

  Position(const Position &) = default;
  Position(Position &&) = default;

  Position(const llvm::Value *val,
           ObjectMap &omap, const StackCache &stack_cache,
           const FunctionCallInfo &call_info,
           const NodeMap &nmap,
           SEG &function_graph) :
        Position(val, StackCache::EmptyStack(),
            omap, stack_cache, call_info, nmap, function_graph) { }

  Position(const llvm::Value *val,
           Context::StackID stack,
           ObjectMap &omap, const StackCache &stack_cache,
           const FunctionCallInfo &call_info,
           const NodeMap &nmap,
           SEG &function_graph) :
       val_(val) {
    // Now, calculate the context given this value and stack
    if (auto ins = dyn_cast<llvm::Instruction>(val_)) {
      // Regenerate the context from a combination of the stack and bb of the
      //   current instruction
      // llvm::dbgs() << "Context cache find on : " << *val << "\n";
      context_ = contextCache_.find(stack, omap.getValue(ins->getParent()),
          omap, stack_cache, call_info, nmap, function_graph);
      // llvm::dbgs() << "resulting stack: " << context_->stack() << "\n";
    } else if (dyn_cast<llvm::Constant>(val_)) {
      // Ummm, just ignore this sucker?
      context_ = ContextCache::ContextID::invalid();
    } else if (auto arg = dyn_cast<llvm::Argument>(val_)) {
      // Arguments are pulled directly from their potential callsites...
      //   magic callsite remappings here...
      // llvm::dbgs() << "Context cache find on (arg) : " << *val << "\n";
      context_ = contextCache_.find(stack,
          omap.getValue(&arg->getParent()->getEntryBlock()),
          omap, stack_cache, call_info, nmap, function_graph);
    } else {
      llvm::dbgs() << "position constructor on: " << *val_ << "\n";
      llvm_unreachable("unsupported value?");
    }
  }

  const llvm::Value *val() const {
    return val_;
  }

  const util::SparseBitmap<ObjectMap::ObjID> &predBBs() const {
    assert(context_ != ContextCache::ContextID::invalid());
    return contextCache_.getContext(context_).predBBs();
  }

  Context::StackID stack() const {
    assert(context_ != ContextCache::ContextID::invalid());
    return contextCache_.getContext(context_).stack();
  }

  bool hasContext() const {
    return context_ != ContextCache::ContextID::invalid();
  }

 private:
  ContextCache::ContextID context_ = ContextCache::ContextID::invalid();
  const llvm::Value *val_;
  static ContextCache contextCache_;
  //}}}
};
ContextCache Position::contextCache_;

class StaticSlice : public llvm::ModulePass {
 public:
  static char ID;
  StaticSlice() : llvm::ModulePass(ID) { }

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const {
    usage.addRequired<llvm::AliasAnalysis>();
    usage.addRequired<ConstraintPass>();
    usage.addRequired<UnusedFunctions>();
    usage.addRequired<DynPtstoLoader>();
    usage.addRequired<llvm::DominatorTree>();
    if (force_alias) {
      usage.addRequired<DynAliasLoader>();
    }
    usage.setPreservesAll();
  }

  bool runOnModule(llvm::Module &m) override {
    alias_ = &getAnalysis<llvm::AliasAnalysis>();
    if (force_alias) {
      dynAlias_ = &getAnalysis<DynAliasLoader>();
    }
    dynInfo_ = &getAnalysis<UnusedFunctions>();
    auto &cons_pass = getAnalysis<ConstraintPass>();
    omap_ = cons_pass.getObjectMap();

    // Create nearest inverse dominator list?
    // The nearest inverse dominator of a bb is its parent in the dom tree
    // The inverse dominators of a terminator are all direct children in the dom
    //      tree
    for (auto &fcn : m) {
      if (!fcn.isDeclaration()) {
        auto &dom = getAnalysis<llvm::DominatorTree>(fcn);

        for (auto &bb : fcn) {
          auto pnode = dom.getNode(&bb);

          if (pnode != nullptr) {
            auto idom = pnode->getIDom();
            if (idom != nullptr) {
              dom_[&bb] = pnode->getIDom()->getBlock();
            }
          }
        }
      }
    }

    // First, we need CFG info, calc the callsites for each function here
    // Now, calculate which stores provide each load here:
    // That should be all of our indirection....
    std::unordered_map<llvm::Value *, std::set<const llvm::Value *>>
      load_src_to_store_dest;
    std::unordered_map<llvm::Value *, std::set<const llvm::Function *>>
      call_dest_to_fcn;

    // For each store, find all loads which may alias with it
    // For each load, find all functions which may alias with it
    std::vector<llvm::Function *> fcns;
    std::vector<llvm::Value *> call_dests;

    FunctionCallInfo::FcnMap fcn_to_callsite;
    FunctionCallInfo::FcnMap arg_to_callsite;
    FunctionCallInfo::FcnMap callsite_to_fcn;
    FunctionCallInfo::FcnMap rets_of_fcn;

    // Prep function callsites {{{
    llvm::dbgs() << "Scanning for instructions\n";
    for (auto &fcn : m) {
        if (!dynInfo_->isUsed(fcn)) {
          continue;
        }
      // Need to find which fcns an id corresponds to
      fcns.push_back(&fcn);

      // Need to find the ids stored by each store
      // Need both the indirect function call list, and the list of ids stored
      //   by each load
      for (auto &bb : fcn) {
        if (!dynInfo_->isUsed(bb)) {
          continue;
        }
        for (auto &inst : bb) {
          if (llvm::isa<llvm::ReturnInst>(&inst)) {
            // llvm::dbgs() << "Adding ret for " << fcn.getName() << "\n";
            rets_of_fcn[&fcn].insert(&inst);
          } else if (auto ci = dyn_cast<llvm::CallInst>(&inst)) {
            // Functions without known callsites -- track their args
            if (LLVMHelper::getFcnFromCall(ci) == nullptr) {
              llvm::CallSite cs(ci);

              call_dests.push_back(cs.getCalledValue());
            }
          }
        }
      }
    }

    size_t count = 0;
    llvm::dbgs() << "Handling indirect calls\n";
    for (auto &call : call_dests) {
      if ((count++ % 1000) == 0) {
        llvm::dbgs() << "  count: " << count << " of " <<
          call_dests.size() << "\n";
      }
      auto &call_fcn = call_dest_to_fcn[call];
      for (auto &fcn : fcns) {
        if (alias_->alias(llvm::AliasAnalysis::Location(call, 1),
              llvm::AliasAnalysis::Location(fcn, 1)) !=
              llvm::AliasAnalysis::NoAlias) {
          call_fcn.insert(fcn);
        }
      }
    }
    // For each inst in fcn:
    llvm::dbgs() << "Setting up internal structures\n";
    for (auto &fcn : m) {
      if (!dynInfo_->isUsed(fcn)) {
        continue;
      }
      for (auto &bb : fcn) {
        if (!dynInfo_->isUsed(bb)) {
          continue;
        }
        for (auto &inst : bb) {
          // For each call inst, if its indirect, look up what functions it may
          //   point to
          if (auto ci = dyn_cast<llvm::CallInst>(&inst)) {
            llvm::CallSite cs(ci);

            auto fcn = LLVMHelper::getFcnFromCall(ci);

            // Then make a mapping from each operand to each argument
            if (fcn != nullptr && !fcn->isDeclaration()) {
              if (!dynInfo_->isUsed(fcn)) {
                continue;
              }
              auto cs_argi = cs.arg_begin();
              auto cs_arge = cs.arg_end();
              auto argi = fcn->arg_begin();
              auto arge = fcn->arg_end();
              for (; cs_argi != cs_arge; ++cs_argi) {
                if (argi == arge) {
                  // llvm::dbgs() << "numoperands != arg count?\n";
                  break;
                }
                auto operand = cs_argi->get();
                auto &arg = *argi;
                ++argi;

                // Copy operand into argi
                arg_to_callsite[&arg].insert(operand);
              }

              /*
              llvm::dbgs() << "Adding callsite for fcn: " <<
                static_cast<void *>(fcn) <<
                " (" << fcn << ")\n";
              */
              fcn_to_callsite[fcn].insert(ci);
              callsite_to_fcn[ci].insert(fcn);
            } else {
              // Get the functions associated with those ids
              for (auto &fcn : call_dest_to_fcn[cs.getCalledValue()]) {
                if (!dynInfo_->isUsed(fcn)) {
                  continue;
                }
                if (!fcn->isDeclaration()) {
                  auto cs_argi = cs.arg_begin();
                  auto cs_arge = cs.arg_end();
                  auto argi = fcn->arg_begin();
                  auto arge = fcn->arg_end();
                  // Fill out the argument mappings
                  for (; cs_argi != cs_arge; ++cs_argi) {
                    if (argi == arge) {
                      // llvm::dbgs() << "numoperands != arg count?\n";
                      break;
                    }
                    auto operand = cs_argi->get();
                    auto &arg = *argi;
                    ++argi;

                    // Copy operand into argi
                    arg_to_callsite[&arg].insert(operand);
                  }

                  /*
                  llvm::dbgs() << "Adding indir for fcn: " <<
                    reinterpret_cast<const void *>(fcn) <<
                    " (" << fcn << ")\n";
                  */
                  fcn_to_callsite[fcn].insert(ci);
                  callsite_to_fcn[ci].insert(fcn);
                }
              }
            }
          }
        }
      }
    }
    //}}}

    llvm::dbgs() << "Making FunctionCallInfo with fcn_to_callsite size:  " <<
      fcn_to_callsite.size() << "\n";
    llvm::dbgs() << "Making FunctionCallInfo with rets_of_fcn size:  " <<
      rets_of_fcn.size() << "\n";
    callInfo_ = FunctionCallInfo(std::move(callsite_to_fcn),
        std::move(fcn_to_callsite),
        std::move(arg_to_callsite),
        std::move(rets_of_fcn),
        dynInfo_);

    // Setup context information {{{
    for (auto &fcn : m) {
      if (!dynInfo_->isUsed(fcn)) {
        continue;
      }
      auto node_id =
        fcnGraph_.addNode<FunctionNode>(&fcn, *dynInfo_, omap_);
      if_debug_enabled(auto ret = )
        fcnToNode_.emplace(&fcn, node_id);
      assert(ret.second);
    }

    // Now, add pred nodes
    for (auto &pnode : fcnGraph_) {
      auto &node = cast<FunctionNode>(*pnode);
      node.addNodePreds(fcnGraph_, fcnToNode_, callInfo_);
    }

    // Now run Tarjan's for SCCs
    {
      RunTarjans<> X(fcnGraph_);
    }

    // Data can now be accessed (lazily populated) w/ node.getPredBBs()
    // }}}

    llvm::dbgs() << "SLICING\n";
    if (do_rand_slice) {
      InstLabeler lblr(m, dynInfo_);

      llvm::dbgs() << "Total Insts: " << lblr.totalInsts() << "\n";
      llvm::dbgs() << "Total USED Insts: " << lblr.totalUsedInsts() << "\n";

      std::ofstream out_file(outfilename, std::ofstream::out);

      int num_slices = std::stoi(rand_slice_count_str);
      int rand_seed = std::stoi(rand_slice_seed_str);

      std::uniform_int_distribution<int> dist(0, lblr.getNumUsedFcns()-1);

      std::minstd_rand rgen(rand_seed);
      for (int i = 0; i < num_slices; i++) {
        auto fcn_num = dist(rgen);
        int64_t num_insts = 0;
        // Create a slice for each instruction in main?
        auto &insts = lblr.getUsedInsts(fcn_num);
        num_insts = insts.size();

        std::uniform_int_distribution<int> inst_dist(0, num_insts-1);
        auto inst_num = inst_dist(rgen);

        auto &inst = *insts[inst_num];
        // Create a slice of this instruction:
        llvm::dbgs() << "Slicing: " << inst << "\n";
        auto slice_set = getSlice(Position(&inst, omap_, stackCache_,
              callInfo_, fcnToNode_, fcnGraph_));
        int64_t slice_insts = 0;
        for (auto val : slice_set) {
          auto inst = dyn_cast<llvm::Instruction>(val);
          if (inst != nullptr) {
            slice_insts++;
          }
        }
        llvm::dbgs() << "slice num: " << i << "\n";
        llvm::dbgs() << "  slice name: " <<
          inst.getParent()->getParent()->getName() << ": " <<
          inst.getParent()->getName() << "->" << inst << "\n";
        llvm::dbgs() << "  slice insts: " << slice_insts << "\n";
        /*
        llvm::dbgs() << "Have slice:\n";
        for (auto val : slice_set) {
          llvm::dbgs() << "  " << *val << "\n";
        }
        */

        // and write out the slice, for later analysis:
        InstWriter::Write(out_file, i,
            std::begin(slice_set), std::end(slice_set),
            lblr);
      }
    }

    if (do_main_slice) {
      auto main_fcn = m.getFunction(fcn_name);

      // Create a slice for each instruction in main?
      for (auto &bb : *main_fcn) {
        for (auto &inst : bb) {
          // Create a slice of this instruction:
          llvm::dbgs() << "Slicing: " << inst << "\n";
          auto slice_set = getSlice(Position(&inst, omap_, stackCache_,
                callInfo_, fcnToNode_, fcnGraph_));
          llvm::dbgs() << "Have slice:\n";
          for (auto val : slice_set) {
            llvm::dbgs() << "  " << *val << "\n";
          }
        }
      }
    }

    return false;
  }

  std::vector<Position> getSources(const Position &pos,
    std::unordered_map<const llvm::Value *,
        util::SparseBitmap<ObjectMap::ObjID>> inst_to_checked_bbs) {
    // Now, for each type of instructions:
    // Instructions I need to care about:
    //   Unary
    //   Binary
    //   cmp
    //   gep
    //   phi
    //   Select
    //  Hard(er):
    //   Store
    //   Load
    //   Call
    //   Invoke?
    //   VAArg?
    //   Return
    // Instructions I can safely ignore
    //   Fence
    std::vector<Position> ret;
    auto v = pos.val();

    auto &arg_to_callsite = callInfo_.getArgToCallsite();
    auto &callsite_to_fcn = callInfo_.getCallsiteToFcn();
    auto &ret_to_fcn = callInfo_.getRetsOfFunc();

    // If its an instruction:
    if (auto pinst = dyn_cast<llvm::Instruction>(v)) {
      // If this is in an unused BB, ignore
      /*
      if (!dynInfo_->isUsed(pinst->getParent())) {
        return ret;
      }
      */
      assert(dynInfo_->isUsed(pinst->getParent()));

      auto stack = pos.stack();
      /*
      llvm::dbgs() << " stack is: {";
      for (auto elm : stack.stack()) {
        llvm::dbgs() << " " << elm;
      }
      llvm::dbgs() << "}\n";
      */

      if (auto ri = dyn_cast<llvm::ReturnInst>(pinst)) {
        auto ret_val = ri->getReturnValue();
        if (ret_val != nullptr) {
          ret.emplace_back(ret_val, stack, omap_, stackCache_, callInfo_,
              fcnToNode_, fcnGraph_);
        }
      } else if (llvm::isa<llvm::InvokeInst>(pinst)) {
        // Add any args to our op list
        /*
        for (auto &val : ii->arg_operands()) {
          ret.push_back(&val);
        }
        */
        llvm_unreachable("Invoke not supported");
      } else if (auto ci = dyn_cast<llvm::CallInst>(pinst)) {
        bool do_skip = false;

        if (llvm::isa<llvm::IntrinsicInst>(ci)) {
          do_skip = true;
        }

        if (!do_skip) {
          // For a call we add a frame to our stack...
          // llvm::dbgs() << "Getting callsite: " << *ci << "\n";
          // How to detect recursion?
          // -- don't need to explore ret if thier bb set is equivalent to ours
          auto it = callsite_to_fcn.find(ci);
          if (it != std::end(callsite_to_fcn)) {
            auto &fcns = it->second;
            for (auto fcn : fcns) {
              if (cast<llvm::Function>(fcn)->isDeclaration()) {
                llvm::ImmutableCallSite cs(ci);
                auto argi = cs.arg_begin();
                auto arge = cs.arg_end();
                for (; argi != arge; ++argi) {
                  // llvm::dbgs() << "Have operand: " << *argi->get() << "\n";
                  ret.emplace_back(argi->get(), stack, omap_, stackCache_,
                      callInfo_, fcnToNode_, fcnGraph_);
                }
              } else {
                auto ret_it = ret_to_fcn.find(fcn);
                if (ret_it != std::end(ret_to_fcn)) {
                  for (auto &rinst : ret_to_fcn.at(fcn)) {
                    auto ret_inst = cast<llvm::ReturnInst>(rinst);
                    auto new_stack = stackCache_.getChild(stack, ret_inst,
                        fcnToNode_, fcnGraph_);
                    ret.emplace_back(ret_inst, new_stack, omap_, stackCache_,
                        callInfo_, fcnToNode_, fcnGraph_);
                  }
                } else {
                  llvm::dbgs() << "WARNING: Couldn't find return inst for fcn: "
                    << cast<llvm::Function>(fcn)->getName() << "\n";
                }
              }
            }
          }
        }
      } else if (llvm::isa<llvm::AllocaInst>(pinst)) {
        // Don't have any sources for alloc insts, so ignore them
      } else if (llvm::isa<llvm::LoadInst>(pinst)) {
        auto &bb_set = pos.predBBs();
        auto &visited_set = inst_to_checked_bbs[pinst];
        auto to_visit = bb_set - visited_set;

        // Add the set we're about to visit to our visited set
        visited_set |= to_visit;

        auto ld_src = pinst->getOperand(0);
        /*
        llvm::dbgs() << "ld isnt is: " <<
          pinst->getParent()->getParent()->getName() << ": " <<
          pinst->getParent()->getName() << " -- "
          << *pinst << "\n";
          */

        // Now visit all the bbs we need to
        for (auto bb_id : to_visit) {
          auto bb = cast<llvm::BasicBlock>(omap_.valueAtID(bb_id));
          assert(dynInfo_->isUsed(bb));
          for (auto &inst : *bb) {
            if (llvm::isa<llvm::StoreInst>(inst)) {
              auto st_dest = inst.getOperand(1);

              if (llvm::isa<llvm::PointerType>(inst.getOperand(0)->getType())) {
                // If we're forcing using static alias analysis:
                if (force_alias) {
                  if (dynAlias_->loadStoreAlias(cast<llvm::LoadInst>(pinst),
                        cast<llvm::StoreInst>(&inst))) {
                    ret.emplace_back(&inst, StackCache::EmptyStack(), omap_,
                        stackCache_, callInfo_, fcnToNode_, fcnGraph_);
                  }
                } else {
                  // llvm::dbgs() << "store is: " << inst << "\n";
                  if (alias_->alias(llvm::AliasAnalysis::Location(st_dest),
                          llvm::AliasAnalysis::Location(ld_src)) !=
                        llvm::AliasAnalysis::NoAlias) {
                    // llvm::dbgs() << "Adding inst: " << inst << "\n";
                    // llvm::dbgs() << "  with stack: " << stack << "\n";  // NOLINT
                    ret.emplace_back(&inst, StackCache::EmptyStack(), omap_,
                        stackCache_, callInfo_, fcnToNode_, fcnGraph_);
                  }
                }
              // OR if we just cast a ptr to an int...
              } else if (llvm::ConstantExpr *ce =
                  dyn_cast<llvm::ConstantExpr>(inst.getOperand(0))) {
                if (ce->getOpcode() == llvm::Instruction::PtrToInt) {
                  llvm::dbgs() << "FIXME: unsupported constexpr cast to int"
                    " then store\n";
                }
              } else {
                llvm::dbgs() << "FIXME: unsupported load from non-ptr: " <<
                  inst << "\n";
              }
            }
          }
        }

        // llvm::dbgs() << "END LD INST\n";
      } else if (auto si = dyn_cast<llvm::StoreInst>(pinst)) {
        // Add the operands (both?) to our op list
        /*
        llvm::dbgs() << "Creating pos at (0): " << *si->getOperand(0) <<
          " stack is: " << stack << "\n";;
        */
        ret.emplace_back(si->getOperand(0), stack, omap_, stackCache_,
            callInfo_, fcnToNode_, fcnGraph_);
        /*
        llvm::dbgs() << "Creating pos at: " << *si->getOperand(1) <<
          " stack is: " << stack << "\n";  // NOLINT
        */
        ret.emplace_back(si->getOperand(1), stack, omap_, stackCache_,
            callInfo_, fcnToNode_, fcnGraph_);
      } else if (auto gep = dyn_cast<llvm::GetElementPtrInst>(pinst)) {
        // Add the pointed to struct to our op list
        ret.emplace_back(gep->getOperand(0), stack, omap_, stackCache_,
            callInfo_, fcnToNode_, fcnGraph_);
      } else if (auto si = dyn_cast<llvm::SelectInst>(pinst)) {
        ret.emplace_back(si->getOperand(1), stack, omap_, stackCache_,
            callInfo_, fcnToNode_, fcnGraph_);
        ret.emplace_back(si->getOperand(2), stack, omap_, stackCache_,
            callInfo_, fcnToNode_, fcnGraph_);
      } else if (auto phi = dyn_cast<llvm::PHINode>(pinst)) {
        // Add each phi source to our op list
        int num_vals = phi->getNumIncomingValues();
        for (int i = 0; i < num_vals; i++) {
          auto phi_val = phi->getIncomingValue(i);
          if (auto pinst = dyn_cast<llvm::Instruction>(phi_val)) {
            if (!dynInfo_->isUsed(pinst->getParent())) {
              continue;
            }
          }
          ret.emplace_back(phi->getIncomingValue(i), stack, omap_, stackCache_,
              callInfo_, fcnToNode_, fcnGraph_);
        }
      } else if (auto ui = dyn_cast<llvm::UnaryInstruction>(pinst)) {
        ret.emplace_back(ui->getOperand(0), stack, omap_, stackCache_,
            callInfo_, fcnToNode_, fcnGraph_);
        // Add the op to our op list
      } else if (auto bi = dyn_cast<llvm::BinaryOperator>(pinst)) {
        ret.emplace_back(bi->getOperand(0), stack, omap_, stackCache_,
            callInfo_, fcnToNode_, fcnGraph_);
        ret.emplace_back(bi->getOperand(1), stack, omap_, stackCache_,
            callInfo_, fcnToNode_, fcnGraph_);
        // Add each op to our op list
      } else if (dyn_cast<llvm::FenceInst>(pinst)) {
        // Ignore fence
      } else if (auto ci = dyn_cast<llvm::CmpInst>(pinst)) {
        ret.emplace_back(ci->getOperand(0), stack, omap_, stackCache_,
            callInfo_, fcnToNode_, fcnGraph_);
        ret.emplace_back(ci->getOperand(1), stack, omap_, stackCache_,
            callInfo_, fcnToNode_, fcnGraph_);
      } else if (auto si = dyn_cast<llvm::SwitchInst>(pinst)) {
        ret.emplace_back(si->getCondition(), stack, omap_, stackCache_,
            callInfo_, fcnToNode_, fcnGraph_);
      } else if (auto bi = dyn_cast<llvm::BranchInst>(pinst)) {
        if (bi->isConditional()) {
          ret.emplace_back(bi->getCondition(), stack, omap_, stackCache_,
              callInfo_, fcnToNode_, fcnGraph_);
        }
      } else if (auto armw = dyn_cast<llvm::AtomicRMWInst>(pinst)) {
        // Ignore rmw?
        ret.emplace_back(armw->getValOperand(), stack, omap_, stackCache_,
            callInfo_, fcnToNode_, fcnGraph_);
        ret.emplace_back(armw->getPointerOperand(), stack, omap_, stackCache_,
            callInfo_, fcnToNode_, fcnGraph_);
      } else {
        llvm::dbgs() << "inst is: " << *pinst << "\n";
        llvm_unreachable("Unsupported inst");
      }

      // Also deal w/ control flow info:
      if (!no_control_flow) {
        auto it = dom_.find(pinst->getParent());
        if (it != std::end(dom_)) {
          auto dom = it->second;

          ret.emplace_back(dom->getTerminator(), stack, omap_, stackCache_,
              callInfo_, fcnToNode_, fcnGraph_);
        }
      }
      // If its not an instruction it must be an Argument... (i hope)
    } else if (auto cons = dyn_cast<llvm::Constant>(v)) {
      if (llvm::isa<llvm::ConstantInt>(cons)) {
        // Ignore
      } else if (llvm::isa<llvm::ConstantFP>(cons)) {
      } else if (llvm::isa<llvm::UndefValue>(cons)) {
      } else if (llvm::isa<llvm::ConstantPointerNull>(cons)) {
        // Ignore
      } else if (llvm::isa<llvm::Function>(cons)) {
        // Ignore
      } else if (llvm::isa<llvm::GlobalVariable>(cons)) {
        // Ignore
      } else if (llvm::isa<llvm::ConstantExpr>(cons)) {
        // Ignore -- all arguments must be constant... leads nowhere
      } else {
        llvm::dbgs() << "unknown constant?: " << *cons << "\n";
        llvm_unreachable("unknown constant");
      }
    } else {
      auto arg = cast<llvm::Argument>(v);

      auto callsite_it = arg_to_callsite.find(arg);
      if (callsite_it != std::end(arg_to_callsite)) {
        for (auto &val : arg_to_callsite.at(arg)) {
          ret.emplace_back(val, stackCache_.getParent(pos.stack()),
              omap_, stackCache_, callInfo_, fcnToNode_, fcnGraph_);
        }
      } else {
        llvm::dbgs() << "WARNING:  couldn't find callsite for arg: "
            << arg->getParent()->getName() << ": " << *arg << "\n";
      }
    }

    return std::move(ret);
  }

  std::set<const llvm::Value *> getSlice(Position pos) {
    std::set<const llvm::Value *> ret;
    // Add v to our set, and do some work
    std::vector<Position> worklist;
    std::vector<Position> next_worklist;

    // To denote which bbs we've checked for each inst -- avoids unneeded work
    std::unordered_map<const llvm::Value *,
          util::SparseBitmap<ObjectMap::ObjID>>
      inst_to_checked_bbs;

    worklist.push_back(pos);
    ret.insert(pos.val());

    // llvm::dbgs() << "Initial stack is: " << pos.stack() << "\n";

    bool ch = true;
    while (ch) {
      ch = false;
      // Now, go to town
      for (auto &dest_val : worklist) {
        /*
        if (dest_val.hasContext()) {
          llvm::dbgs() << "worklist stack is: " << dest_val.stack() << "\n";
        }
        */
        // Find sources for instruction
        // NOTE: Tricky pts are loads, and calls
        std::vector<Position> srcs = getSources(dest_val, inst_to_checked_bbs);
        // Add those sources to worklist
        for (auto src : srcs) {
          /*
          if (src.val() == nullptr) {
            llvm::dbgs() << "dest_val is: " << *dest_val.val() << "\n";
          }
          */
          assert(src.val() != nullptr);
          if (ret.find(src.val()) == std::end(ret)) {
            /*
            if (src.hasContext()) {
              llvm::dbgs() << "src_stack is: " << src.stack() << "\n";
            }
            */
            next_worklist.push_back(src);
            ret.insert(src.val());
            ch = true;
          }
        }
      }

      std::swap(worklist, next_worklist);
      next_worklist.clear();
    }

    return std::move(ret);
  }

 private:
  const UnusedFunctions *dynInfo_;

  ObjectMap omap_;

  llvm::AliasAnalysis *alias_;
  DynAliasLoader *dynAlias_;

  NodeMap fcnToNode_;
  SEG fcnGraph_;

  FunctionCallInfo callInfo_;
  StackCache stackCache_;
  std::map<const llvm::BasicBlock *, const llvm::BasicBlock *> dom_;
};


// New algorithm:
//
// NOTE: Instruction + Context ==> Position
// NOTE: Context contains list of pred BBs & stack
// Given Starting Instruction and Context --
// getSlice(startPos):
//   Make worklist of Position
//   Insert startition pos into worklist
//   while (!worklist.empty()):
//     pos = worklist.next();
//     preds = FindPreds(pos);
//     worklist.insert(preds);
//
//
// FindPreds(Position pos):
//   pred_insts = findDirectPred(pos);
//       Uses context to only search predBBs for sol
//   NOTE:  Determine any stack updates here -- (for call or Ret insts)
//    -- solve w/ some relation if the set of pred BB's doesn't change...
//   if (pred_ins.bb != pos.ins.bb || stack_update)
//     pred_con = getContext(pred_ins.bb, pos.con.stack);
//
//   poses.push_back(pred_ins, pred_con);
//   for (pos : poses)
//     if (!positionSet.contains(pos)):
//       retSet.add(pos)
//
//  return retSet;
//


char StaticSlice::ID = 0;
static llvm::RegisterPass<StaticSlice>
X("static-slice", "static-slice", false, false);

