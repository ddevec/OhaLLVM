/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LIB_FCNCFG_H_
#define INCLUDE_LIB_FCNCFG_H_

#include <limits>
#include <set>
#include <unordered_map>
#include <vector>

#include "include/util.h"
#include "include/SEG.h"
#include "include/ValueMap.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

class FcnCFG : public llvm::ModulePass {
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

      SEG::Node::unite(seg, n);
    }

    const std::set<const llvm::Function *> &reps() const {
      return reps_;
    }

   private:
    const llvm::Function *func_;

    // Set of call instructions within this function
    std::set<const llvm::Function *> reps_;
    //}}}
  };

 public:
  typedef util::ID<id_tag, uint32_t, std::numeric_limits<uint32_t>::max()> Id;

  static char ID;
  FcnCFG();

  virtual bool runOnModule(llvm::Module &M);

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  llvm::StringRef getPassName() const override {
    return "FcnCFG";
  }

  Id getId(const llvm::Function *fcn) const {
    return util::convert_id<Id>(fcnMap_.at(fcn));
  }

  const std::set<const llvm::Function *> &
  getSCC(const llvm::Function *fcn) const {
    return getSCC(getId(fcn));
  }

  const std::set<const llvm::Function *> &
  getSCC(Id id) const {
    auto seg_id = util::convert_id<SEG::NodeID>(id);
    return fcnGraph_.getNode<FcnNode>(seg_id).reps();
  }

 private:
  SEG fcnGraph_;

  std::unordered_map<const llvm::Function *, SEG::NodeID> fcnMap_;
  std::vector<const llvm::Function *> idToFcn_;
};

#endif  // INCLUDE_LIB_FCNCFG_H_
