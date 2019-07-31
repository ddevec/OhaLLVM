/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_CSFCNCFG_H_
#define INCLUDE_CSFCNCFG_H_

#include <limits>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "include/util.h"
#include "include/CallInfo.h"

#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

class CsFcnCFG {
 private:
  struct id_tag {};

 public:
  typedef util::ID<id_tag, uint32_t, std::numeric_limits<uint32_t>::max()> Id;

  class FcnNode {
    //{{{
   public:
     FcnNode() = delete;
     FcnNode(const llvm::Function *fcn, const CallInfo &ci) :
       fcn_(fcn), ci_(ci) { }

     FcnNode(FcnNode &&) = default;
     FcnNode &operator=(FcnNode &&) = default;

     FcnNode(const FcnNode &) = default;
     FcnNode &operator=(const FcnNode &) = default;

     const CallInfo &ci() const {
       return ci_;
     }

     const llvm::Function *fcn() const {
       return fcn_;
     }

     const std::set<Id> &preds() const {
       return preds_;
     }

     std::set<Id> &preds() {
       return preds_;
     }

     void addPred(Id pred) {
       preds_.emplace(pred);
     }

     void remapCi(const util::ObjectRemap<CallInfo::Id> &ci) {
       ci_.remap(ci);
     }

     void remapCi(const ValueMap &map) {
       ci_.updateReps(map);
     }

      friend llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
          const FcnNode &node) {
        os << "(" << node.fcn_->getName() << ", " <<
          util::print_iter(node.preds_) << ")";
        return os;
      }

   private:
    std::set<Id> preds_;

    const llvm::Function *fcn_;
    CallInfo ci_;
    //}}}
  };

  CsFcnCFG() = default;

  Id addNode(const llvm::Function *fcn, const CallInfo &ci) {
    Id ret(nodes_.size());
    nodes_.emplace_back(fcn, ci);
    return ret;
  }

  FcnNode &getNode(Id &id) {
    assert(id != Id::invalid());
    assert(static_cast<size_t>(id) < nodes_.size());
    return nodes_[static_cast<size_t>(id)];
  }

  std::unordered_multimap<const llvm::Function *, Id> findDirectPreds(Id start,
      const std::unordered_set<const llvm::Function *> &candidates);

  util::ObjectRemap<Id> copyNodes(const CsFcnCFG &callee,
      const util::ObjectRemap<CallInfo::Id> &ci_remap);

  void updateNodes(const ValueMap &map) {
    for (auto &node : nodes_) {
      node.remapCi(map);
    }
  }

  void updateNodes(const util::ObjectRemap<CallInfo::Id> &map) {
    for (auto &node : nodes_) {
      node.remapCi(map);
    }
  }

  friend llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
      const CsFcnCFG &cfg) {
    for (size_t i = 0; i < cfg.nodes_.size(); ++i) {
      if (i != 0) {
        os << ", ";
      }
      os << i << ": " << cfg.nodes_[i];
    }
    return os;
  }

 private:
  std::vector<FcnNode> nodes_;
};

#endif  // INCLUDE_CSFCNCFG_H_
