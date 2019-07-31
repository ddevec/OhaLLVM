/*
 * Copyright (C) 2016 David Devecsery
 */

#include "include/CsFcnCFG.h"

#include <algorithm>
#include <unordered_map>
#include <unordered_set>

#include "include/util.h"

#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

std::unordered_multimap<const llvm::Function *, CsFcnCFG::Id>
CsFcnCFG::findDirectPreds(Id start,
    const std::unordered_set<const llvm::Function *> &candidates) {
  std::unordered_multimap<const llvm::Function *, Id> ret;
  std::unordered_set<Id> visited;

  // llvm::dbgs() << "findDirPath, graph: " << *this << "\n";
  // Add the current node to our work list
  util::Worklist<Id> wl;
  wl.push(start);

  while (!wl.empty()) {
    auto cur_id = wl.pop();

    auto &cur_node = getNode(cur_id);
    auto fcn = cur_node.fcn();
    /*
    llvm::dbgs() << "Considering: (" << cur_id << ") " <<
      fcn->getName() << "\n";
    */

    // candid_it... LOL
    auto candid_it = candidates.find(fcn);
    if (candid_it != std::end(candidates)) {
      // llvm::dbgs() << "  have pred: " << fcn->getName() << "\n";
      ret.emplace(fcn, cur_id);
      auto rc = visited.emplace(cur_id);
      if (!rc.second) {
        continue;
      }

      // add preds to wl
      for (auto pred_id : cur_node.preds()) {
        // auto &pred_node = getNode(pred_id);
        // auto pred_fcn = pred_node.fcn();
        // llvm::dbgs() << "  !pushing: " << pred_fcn->getName() << "\n";
        wl.push(pred_id);
      }
    }
  }

  return ret;
}

util::ObjectRemap<CsFcnCFG::Id> CsFcnCFG::copyNodes(const CsFcnCFG &callee,
    const util::ObjectRemap<CallInfo::Id> &ci_remap) {
  util::ObjectRemap<CsFcnCFG::Id> ret(callee.nodes_.size());

  Id remap_id(0);
  for (auto &node : callee.nodes_) {
    auto id = addNode(node.fcn(), node.ci());
    ret.set(remap_id, id);
    remap_id++;
  }

  // doh! update the preds for those nodes
  for (size_t i = 0; i < callee.nodes_.size(); ++i) {
    Id node_id(i);

    auto &rhs_node = callee.nodes_[i];
    auto &lhs_node = nodes_[static_cast<size_t>(ret[node_id])];

    // Remap the call info of the node...
    lhs_node.remapCi(ci_remap);

    // Convert the preds
    auto &rhs_preds = rhs_node.preds();
    auto &lhs_preds = lhs_node.preds();

    // copy the preds from callee.nodes_[i] into rhs
    std::transform(std::begin(rhs_preds), std::end(rhs_preds),
        std::inserter(lhs_preds, std::begin(lhs_preds)),
        [&ret] (Id pred_id) {
          return ret[pred_id];
        });
  }

  return ret;
}


