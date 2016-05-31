/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/FcnCFG.h"

#include <string>
#include <vector>

using std::swap;


typedef std::unordered_map<const llvm::Function *, SEG::NodeID>
    NodeMap;

class FunctionNode : public SEG::Node {
  //{{{
 public:
  explicit FunctionNode(SEG::NodeID node_id,
      const llvm::Function *fcn,
      const UnusedFunctions &dyn_info) :
        SEG::Node(NodeKind::HUNode, node_id),
        func_(fcn) {
    // Populate my predBBs_ LOCALLY (locally visited basic blocks)
    for (auto &bb : *fcn) {
      if (!dyn_info.isUsed(bb)) {
        continue;
      }
      predBBs_.set(&bb);

      // Update my CALLEES set
      for (auto &inst : bb) {
        if (auto ci = dyn_cast<llvm::CallInst>(&inst)) {
          callees_.insert(ci);
        }
      }
    }
  }

  // Do our bottom up traversal to fill in callee bbs
  void addCalleePreds(SEG &seg,
      const NodeMap &nmap,
      const CallDests &call_info) {
    // Don't process ourself twice
    if (haveCalleeBBs_) {
      return;
    }

    // Get all of our pred callees
    for (auto ci : callees_) {
      auto &callee_vec = call_info.getDests(pci);
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
        auto &predbb_set = pred.getPredBBs(seg, nmap, call_info);
        predBBs_.insert(std::begin(predbb_set), std::end(predbb_set));
      }
    }

    haveCalleeBBs_ = true;
  }

  void unite(SEG &seg, SEG::Node &n) override {
    auto &node = cast<FunctionNode>(n);

    // Unite the BB sets
    predBBs_.insert(std::begin(node.predBBs_), std::end(node.predBBs_));
    // Unite the visited sets
    callees_.insert(std::begin(node.callees_), std::end(node.callees_));

    node.callees_.clear();
    node.predBBs_.clear();

    SEG::Node::unite(seg, n);
  }

  const std::set<const llvm::BasicBlock *> &getPredBBs(SEG &seg,
      const NodeMap &nmap,
      const CallDests &call_info) {
    if (!haveCalleeBBs_) {
      addCalleePreds(seg, nmap, call_info);
    }

    assert(haveCalleeBBs_);
    return predBBs_;
  }

  const std::set<const llvm::CallInst *> &callees() const {
    return callees_;
  }

  const llvm::Function func() const {
    return func_;
  }

 private:
  const llvm::Function *func_;
  std::set<const llvm::BasicBlock *> predBBs_;

  // Set of call instructions within this function
  std::set<const llvm::CallInst *> callees_;
  bool haveCalleeBBs_ = false;
  //}}}
};

// One which returns info for all preds
class StaticFcnCFGInfo : public FcnCFGInfo {
  //{{{
 public:
  StaticFcnCFGInfo(SEG &seg, FunctionNode &node) :
    FcnCFGInfo(node.func()),
    seg_(seg), node_(node) { }

  std::vector<std::unique_ptr<FcnCFGInfo>> preds() {
    // Return a node for each pred in the seg
    for (auto &pred_id : node_.preds()) {
      auto &pred_node = seg_.getNode<FunctionNode>(pred_id);

      if (pred_node.id() != node_.id()) {
        ret.emplace_back(new StaticFcnCFGInfo(seg_, pred_node));
      }
    }
  }

 private:
  SEG &seg_;
  FunctionNode &node_;
  //}}}
};

class ProfileFcnCFGInfo {
  //{{{
  //}}}
};

static void add_node_pred(FunctionNode &node,
    SEG &seg,
    const NodeMap &nmap,
    CallDests &call_info) {
  // For each callee in this function, add a pred to the SEG
  for (auto pci : node.callees()) {
    callee_vec = call_info.getDests(pci);
    for (auto &fcn : callee_vec) {
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


char FcnCFG::ID = 0;
FcnCFG::FcnCFG() : llvm::ModulePass(ID) { }

namespace llvm {
  static RegisterPass<FcnCFG>
      X("fcn-cfg", "Generate control-flow-graph info for callsites between "
          " functions", false, false);
}  // namespace llvm

void FcnCFG::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  // Because we're an AliasAnalysis
  // AliasAnalysis::getAnalysisUsage(usage);
  usage.setPreservesAll();

  // For DCE
  usage.addRequired<UnusedFunctions>();

  // For function numbering?
  usage.addRequired<ConstraintPass>();

  // For indir callsite info
  usage.addRequried<CallDests>();
}

bool ConstraintPass::runOnModule(llvm::Module &m) {
  auto &dyn_info = getAnalysis<UnusedFunctions>();
  auto dynCalls_ = &getAnalysis<DynCallPaths>();
  auto &call_dests = getAnalysis<CallDests>();

  // Add each fcn in M
  for (auto &fcn : m) {
    auto node_id = fcnGraph_.addNode<FunctionNode>(&fcn, *dyn_info_);
  }

  // Then, determine callsite/CFG information for
  //   each function in M
  // If we have dyn CFG info, load from that.
  // Otherwise, infer statically
  if (!dynCalls_->hasInfo()) {
    // Build Call Graph:
    NodeMap fcn_to_node;
    for (auto &fcn : m) {
      auto node_id = callGraph_.addNode<FunctionNode>(&fcn, dyn_info);
      fcn_to_node.emplace(&fcn, node_id);
    }

    for (auto &pnode : callGraph_) {
      auto &node = cast<FunctionNode>(*pnode);
      add_node_pred(node, callGraph_, fcn_to_node, call_dests);
    }

    // Calc SCCs
    {
      RunTarjans<> X(callGraph_);
    }
  }
}

std::vector<std::unique_ptr<FcnCFGInfo>> getInfo(const llvm::Function *fcn) {
  std::vector<std::unique_ptr<FcnCFGInfo>> ret;

  // If we have callsite info, return the appropriate callsite info
  // If we need to do it statically, return a static variant

  return std::move(ret);
}

