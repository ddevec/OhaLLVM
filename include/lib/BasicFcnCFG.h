/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LIB_BASICFCNCFG_H_
#define INCLUDE_LIB_BASICFCNCFG_H_

#include <set>
#include <unordered_map>
#include <vector>

#include "include/util.h"
#include "include/DynamicInfo.h"
#include "include/SEG.h"
#include "include/Tarjans.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

class BasicFcnCFG {
 private:
  struct id_tag {};

  class FcnNode : public SEG::Node {
    //{{{
   public:
    FcnNode(SEG::NodeID node_id,
        const llvm::Function *fcn) :
          SEG::Node(NodeKind::HUNode, node_id),
          func_(fcn) {
      reps_.insert(fcn);
    }

    void unite(SEG &seg, SEG::Node &n) override {
      auto &node = cast<FcnNode>(n);

      reps_.insert(std::begin(node.reps_), std::end(node.reps_));
      node.reps_.clear();

      SEG::Node::unite(seg, n);
    }

    const std::unordered_set<const llvm::Function *> &reps() const {
      return reps_;
    }

   private:
    const llvm::Function *func_;

    // Set of call instructions within this function
    std::unordered_set<const llvm::Function *> reps_;
    //}}}
  };

 public:
  typedef util::ID<id_tag, uint32_t, std::numeric_limits<uint32_t>::max()> Id;

  BasicFcnCFG(llvm::Module &m, DynamicInfo &di);

  BasicFcnCFG(const BasicFcnCFG &rhs) {
    fcnGraph_ = rhs.fcnGraph_.clone<FcnNode>();
    fcnMap_ = rhs.fcnMap_;
    idToFcn_ = rhs.idToFcn_;
  }

  Id getId(const llvm::Function *fcn) const {
    return util::convert_id<Id>(
        fcnGraph_.getNode(fcnMap_.at(fcn)).id());
  }

  const std::unordered_set<const llvm::Function *> &
  getSCC(const llvm::Function *fcn) const {
    return getSCC(getId(fcn));
  }

  const std::unordered_set<const llvm::Function *> &
  getSCC(Id id) const {
    auto seg_id = util::convert_id<SEG::NodeID>(id);
    return fcnGraph_.getNode<FcnNode>(seg_id).reps();
  }

  void addIndirEdge(const llvm::Function *caller_fcn,
      const llvm::Function *callee_fcn) {
    auto caller_id = fcnGraph_.getNode(fcnMap_.at(caller_fcn)).id();
    auto callee_id = fcnGraph_.getNode(fcnMap_.at(callee_fcn)).id();
    if (callee_id == caller_id) {
      return;
    }

    fcnGraph_.addPred(callee_id, caller_id);

    updateScc();
  }

 private:
  // Umm, yeah, update the sccs...
  // FIXME: Use optimized alg from pldi07 paper
  void updateScc() {
    RunTarjans<> X(fcnGraph_);
  }

  SEG fcnGraph_;

  std::map<const llvm::Function *, SEG::NodeID> fcnMap_;
  std::vector<const llvm::Function *> idToFcn_;
};

#endif  // INCLUDE_LIB_BASICFCNCFG_H_
