/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/AndersGraph.h"

#include <algorithm>
#include <map>
#include <utility>
#include <tuple>
#include <vector>

AndersGraph::Id AndersGraph::addConstraint(const Constraint &cons) {
  Id ret = Id::invalid();
  // Ignore nullvalue alloc/load/store constraints
  if (cons.type() != ConstraintType::Copy &&
       (cons.src() == ValueMap::NullValue ||
        cons.dest() == ValueMap::NullValue)) {
    return ret;
  }

  // Ignore copy to nullvalue
  if (cons.type() == ConstraintType::Copy &&
      cons.dest() == ValueMap::NullValue) {
    return ret;
  }

  switch (cons.type()) {
    case ConstraintType::Load:
      {
        /*
        llvm::dbgs() << "fill load: " << cons.dest() << " <- " <<
          cons.src() << "\n";
        llvm::dbgs() << "  dest: " << cons.dest() << ": " <<
          ValPrint(cons.dest(), cg_->vals()) << "\n";
        llvm::dbgs() << "  src ptr is: " <<
          ValPrint(cons.src(), cg_->vals()) << "\n";
        */
        auto &node = getNode(cons.src());
        node.addCons(cons);
        ret = node.id();
        break;
      }
    case ConstraintType::Store:
      {
        /*
        llvm::dbgs() << "fill store: " << cons.dest() << " <- " <<
          cons.src() << "\n";
        llvm::dbgs() << "  dest ptr: " << cons.dest() << ": " <<
          ValPrint(cons.dest(), cg_->vals()) << "\n";
        llvm::dbgs() << "  src is: " <<
          ValPrint(cons.src(), cg_->vals()) << "\n";
        */
        // We add store constraints to the dest, as they are evaluated when
        //   the dest value changes
        auto &st_node = getNode(cons.dest());
        st_node.addCons(cons);
        ret = st_node.id();
        break;
      }
    // Alloc constraints are added as initial points-to data
    case ConstraintType::AddressOf:
      {
        /*
        if (cons.src().val() == 8418 ||
            cons.src().val() == 8400) {
          llvm::dbgs() << "Node: " << cons.dest() << " has initial pts: " <<
            cons.src() << "\n";
        }
        */
        auto &node = getNode(cons.dest());
        if (cons.src() >= cg_->getMaxAlloc()) {
          llvm::dbgs() << "fill addrof: " << cons.dest() << " <- " <<
            cons.src() << "\n";
          llvm::dbgs() << "  src: " << cons.src() << " max: " <<
            cg_->getMaxAlloc() << "\n";
          llvm::dbgs() << "  dest: " << cons.dest() << ": " <<
            ValPrint(cons.dest(), cg_->vals()) << "\n";
          llvm::dbgs() << "  alloc value is: " <<
            ValPrint(cons.src(), cg_->vals()) << "\n";
        }
        assert(cons.src() < cg_->getMaxAlloc());
        node.ptsto().set(cons.src());
        ret = node.id();
        break;
      }
    // Copy constraints are added as edges
    case ConstraintType::Copy:
      {
        auto &node = getNode(cons.src());
        node.addSucc(cons.dest(), cons.offs());
        ret = node.id();
        break;
      }
    default:
      llvm_unreachable("Invalid cons type");
  }

  return ret;
}

void AndersGraph::addIndirConstraint(
    const std::tuple<Cg::Id, CallInfo, CsFcnCFG::Id> &tup) {
  auto id = std::get<0>(tup);
  auto &ci = std::get<1>(tup);
  auto cg_id = std::get<2>(tup);

  // Find the node assocated with the called value
  auto &node = getNode(id);
  node.addIndirCall(ci, cg_id);
}

void AndersGraph::fill() {
  // For each constraint destination, make a node.
  Id max_id(0);

  // Find the max id
  // First scan indir functions
  for (auto &cons : cg_->constraints()) {
    if (cons.dest() > max_id) {
      max_id = cons.dest();
    }

    if (cons.src() > max_id) {
      max_id = cons.src();
    }
  }

  assert(nodes_.size() == 0);
  nodes_.reserve(nodes_.size());
  for (Id i(0); i <= max_id; i++) {
    nodes_.emplace_back(Id(i));
  }
  reps_ = util::UnionFind<Id>(max_id.val()+1);

  // Sanity check, there are no sources greater than max_id?
  if_debug_enabled(
    for (auto &cons : cg_->constraints()) {
      assert(cons.src() <= max_id);
    });

  // UGH, also need to handle "GEPs" constraints, to manage dynamically
  //   indexed structures...
  // For each constraint, add it to the node associated with its source
  for (auto &cons : cg_->constraints()) {
    addConstraint(cons);
  }

  // FIXME: Add indirect constraints!!
  for (auto &tup : cg_->indirCalls()) {
    addIndirConstraint(tup);
  }

  prevCons_ = cg_->constraints().size();
  prevIndirCons_ = cg_->indirCalls().size();

  /*
  auto &nd = getNode(Id(138391));
  llvm::dbgs() << "Node " << nd.id() << " has constriants:\n";
  for (auto &pcons : nd.constraints()) {
    llvm::dbgs() << "  " << *pcons << "\n";
  }

  llvm::dbgs() << "  ptsto: " << nd.ptsto() << "\n";

  llvm::dbgs() << "copySuccs: {";
  auto &succs = nd.copySuccs();
  for (auto succ_id : succs) {
    llvm::dbgs() << " " << succ_id;
  }
  llvm::dbgs() << " }\n";

  llvm::dbgs() << "gepSuccs: {";
  auto &gep_succs = nd.gepSuccs();
  for (auto &succ_pr : gep_succs) {
    llvm::dbgs() << " (" << succ_pr.first << " + " << succ_pr.second << ")";
  }
  llvm::dbgs() << " }\n";
  */
}

void AndersGraph::merge(AndersNode &n1, AndersNode &n2) {
  assert(reps_.find(n1.id()) == n1.id() &&
      reps_.find(n2.id()) == n2.id());
  assert(n1.id() != n2.id());
  reps_.merge(n1.id(), n2.id());

  auto rep_id = reps_.find(n1.id());

  if (rep_id == n1.id()) {
    n1.merge(n2);
  } else {
    assert(rep_id == n2.id());
    n2.merge(n1);
  }
}

std::vector<AndersGraph::Id>
AndersGraph::updateGraphForCons(
  const std::map<const llvm::Function *, std::pair<CallInfo, CsFcnCFG::Id>>
      &ci) {
  std::vector<Id> ret;
  // Now, create new nodes for each of the new constraints
  auto &constraints = cg_->constraints();

  /*
  llvm::dbgs() << "Updating graph\n";

  llvm::dbgs() << "old cons size was:" << prevCons_ << "\n";
  llvm::dbgs() << "new cons size is:" << constraints.size() << "\n";
  */

  auto max_id = Id(nodes_.size()-1);
  auto start_id = Id(nodes_.size());
  auto start_it = std::begin(constraints);
  std::advance(start_it, prevCons_);
  for (auto it = start_it, en = std::end(constraints);
      it != en; std::advance(it, 1)) {
    auto &cons = *it;

    if (cons.dest() > max_id) {
      max_id = cons.dest();
    }

    if (cons.src() > max_id) {
      max_id = cons.src();
    }
  }

  // Also consider callinfo?
  for (auto &pr : ci) {
    auto &new_ci = pr.second.first;
    for (auto &arg : new_ci.args()) {
      max_id = std::max(max_id, arg);
    }

    max_id = std::max(max_id, new_ci.varArg());
    max_id = std::max(max_id, new_ci.ret());
  }

  ++max_id;
  llvm::dbgs() << "got max id: " << max_id << "\n";

  /*
  nodes_.reserve(static_cast<size_t>(max_id));
  reps_.reserve(static_cast<size_t>(max_id));
  */
  for (Id i(start_id); i < max_id; i++) {
    nodes_.emplace_back(i);
    if_debug_enabled(auto rep_id =)
      reps_.add();
    assert(rep_id == i);
  }

  // Now add all the new constraints:
  for (auto it = start_it, en = std::end(constraints);
      it != en; std::advance(it, 1)) {
    auto fill_id = addConstraint(*it);
    if (fill_id != Id::invalid()) {
      ret.push_back(fill_id);
    }
  }

  auto indir_it = std::begin(cg_->indirCalls());
  std::advance(indir_it, prevIndirCons_);
  for (auto it = indir_it, en = std::end(cg_->indirCalls());
      it != en; std::advance(it, 1)) {
    addIndirConstraint(*it);
  }

  prevCons_ = cg_->constraints().size();
  prevIndirCons_ = cg_->indirCalls().size();

  return ret;
}

std::pair<std::vector<AndersGraph::Id>,
  std::map<const llvm::Function *, std::pair<CallInfo, CsFcnCFG::Id>>>
AndersGraph::mapIn(const llvm::Function *fcn) {
  auto pcallee_cg = callCgCache_->tryGetCg(fcn);

  if (pcallee_cg == nullptr) {
    auto callee_cg = cgCache_->getCg(fcn);

    callee_cg.resolveCalls(*cgCache_, *callCgCache_);

    callCgCache_->addCg(fcn, std::move(callee_cg));
    pcallee_cg = callCgCache_->tryGetCg(fcn);
    assert(pcallee_cg != nullptr);
  }

  /*
  llvm::dbgs() << "pcallee_cg has graph: " << pcallee_cg->localCFG() <<
    "\n";
  */
  llvm::dbgs() << "Mapping " << fcn->getName() << " into Cg\n";
  auto ret = cg_->mapIn(*pcallee_cg);
  /*
  llvm::dbgs() << "cg_ now has graph: " << cg_->localCFG() << "\n";
  */

  // Also need to add allocs!!!
  // This means we need to update the alloc set in BddPtstoSet

  auto cons = updateGraphForCons(ret);

  BddPtstoSet::updateGeps(*cg_);

  return std::pair<std::vector<AndersGraph::Id>,
          std::map<const llvm::Function *, std::pair<CallInfo, CsFcnCFG::Id>>>
            (std::move(cons), std::move(ret));
}

std::vector<AndersGraph::Id>
AndersGraph::addExternalCall(llvm::ImmutableCallSite &cs,
    const llvm::Function *callee_fcn,
    const CallInfo &caller_ci) {
  // First, add constraints for the call in our cg
  cg_->addConstraintsForExternalCall(cs, callee_fcn, caller_ci);
  std::map<const llvm::Function *, std::pair<CallInfo, CsFcnCFG::Id>> tmp;
  // Then update our graph
  return updateGraphForCons(tmp);
}
