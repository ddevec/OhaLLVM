/*
 * Copyright (C) 2016 David Devecsery
 */

#ifndef INCLUDE_LIB_SPECCSCFG_H_
#define INCLUDE_LIB_SPECCSCFG_H_

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

class SpecCsCFG : public llvm::ModulePass {
 private:
  struct id_tag {};

  class CsNode : public SEG::Node {
    //{{{
   public:
    CsNode(SEG::NodeID node_id,
        const llvm::Instruction *cs) :
          SEG::Node(NodeKind::HUNode, node_id),
          cs_(cs) {
      reps_.insert(cs);
    }

    void unite(SEG &seg, SEG::Node &n) override {
      auto &node = cast<CsNode>(n);

      reps_.insert(std::begin(node.reps_), std::end(node.reps_));

      node.reps_.clear();

      SEG::Node::unite(seg, n);
    }

    const std::set<const llvm::Instruction *> &reps() const {
      return reps_;
    }

   private:
    const llvm::Instruction *cs_;

    // Set of call instructions within this function
    std::set<const llvm::Instruction *> reps_;
    //}}}
  };

 public:
  typedef util::ID<id_tag, int32_t, -1> Id;

  static char ID;
  SpecCsCFG();

  virtual bool runOnModule(llvm::Module &M);

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  llvm::StringRef getPassName() const override {
    return "SpecCsCFG";
  }

  Id getId(const llvm::Instruction *fcn) const {
    auto ret = util::convert_id<Id>(
        csGraph_.getNode(csMap_.at(fcn)).id());
    assert(static_cast<size_t>(ret) < csGraph_.getNumNodes());
    return ret;
  }

  const SEG::Node &getNode(Id id) const {
    return csGraph_.getNode(util::convert_id<SEG::NodeID>(id));
  }

  const std::set<const llvm::Instruction *> &
  getSCC(const llvm::Instruction *fcn) const {
    return getSCC(getId(fcn));
  }

  const std::set<const llvm::Instruction *> &
  getSCC(Id id) const {
    auto seg_id = util::convert_id<SEG::NodeID>(id);
    return csGraph_.getNode<CsNode>(seg_id).reps();
  }

  const std::vector<std::vector<Id>> &findPathsFromMain(Id end) const;

  size_t size() const {
    return csGraph_.getNumNodes();
  }

 private:
  void findPath(const CsNode &node, Id end,
      std::unordered_map<Id, std::vector<std::vector<Id>>, Id::hasher> &cache)
    const;

  SEG csGraph_;

  Id mainNode_;

  std::unordered_map<const llvm::Instruction *, SEG::NodeID> csMap_;

  mutable std::unordered_map<Id, std::vector<std::vector<Id>>, Id::hasher>
    pathCache_;
};

#endif  // INCLUDE_LIB_SPECCSCFG_H_
