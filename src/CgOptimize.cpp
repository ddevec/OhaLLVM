/*
 * Copyright (C) 2015 David Devecsery
 */

#include <cassert>
#include <cstdint>

#include <algorithm>
#include <map>
#include <set>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

#include "include/Cg.h"

#include "llvm/Constants.h"
#include "llvm/Function.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Module.h"

#include "include/util.h"
#include "include/RunTarjans.h"
#include "include/ValueMap.h"
#include "include/lib/IndirFcnTarget.h"
#include "include/lib/UnusedFunctions.h"

class HVNData {
  //{{{
 public:
  typedef OptGraph::Id Id;
  explicit HVNData(OptGraph &hvn_graph) : hvnGraph_(hvn_graph) { }

  int32_t getNextPE() {
    return nextPE_++;
  }

  int32_t getGEPPE(Id node_id, int32_t offs) {
    auto it = gepToPE_.find(std::make_pair(node_id, offs));

    if (it == std::end(gepToPE_)) {
      auto rp = gepToPE_.emplace(std::make_pair(node_id, offs), getNextPE());
      assert(rp.second);
      it = rp.first;
    }

    return it->second;
  }

  int32_t getHashValue(const HVNNode &node) {
    auto &ptsto = node.ptsto();

    auto it = hashValueMap_.find(ptsto);
    if (it == std::end(hashValueMap_)) {
      auto rv = hashValueMap_.emplace(ptsto, getNextPE());
      assert(rv.second);
      it = rv.first;
    }

    return it->second;
  }

  int32_t getPEForID(Id id) {
    auto it = idToPE_.find(id);
    if (it == std::end(idToPE_)) {
      auto rv = idToPE_.emplace(id, getNextPE());
      assert(rv.second);
      it = rv.first;
    }

    return it->second;
  }

  GraphId getRef(Id id) {
    auto ref_it = nodeToRef_.find(id);

    if (ref_it == std::end(nodeToRef_)) {
      auto new_node_id = hvnGraph_.addNode();
      auto &hvn_node = hvnGraph_.getNode(new_node_id);
      hvn_node.setRef();

      auto rc = nodeToRef_.emplace(id, new_node_id);
      assert(rc.second);
      ref_it = rc.first;
    }

    if_debug_enabled(auto &ret = hvnGraph_.getNode(ref_it->second);)
    assert(ret.ref());
    return ref_it->second;
  }

 private:
  // 0 is non-ptr
  int32_t nextPE_ = 1;

  std::map<std::pair<Id, int32_t>, int32_t> gepToPE_;

  std::unordered_map<util::SparseBitmap<int32_t>, int32_t> hashValueMap_;

  std::unordered_map<Id, int32_t> idToPE_;

  OptGraph &hvnGraph_;
  std::map<Id, Id> nodeToRef_;
  //}}}
};

size_t Cg::updateConstraints(OptGraph &graph) {
  std::unordered_map<GraphId, GraphId> rep_remapping;

  auto max_id = getMaxId();
  for (int32_t i = 0; i < static_cast<int32_t>(max_id); i++) {
    GraphId node_id(i);

    auto rep_id = graph.getRep(node_id);

    if (util::convert_id<Id>(node_id) == ValueMap::IntValue ||
        util::convert_id<Id>(rep_id) == ValueMap::IntValue ||
        util::convert_id<Id>(node_id) == ValueMap::NullValue ||
        util::convert_id<Id>(rep_id) == ValueMap::NullValue) {
      continue;
    }

    // This is to lower any reps above vals_.size() to reps below vals_.size()
    // NOTE: These were introduced by the "ref" nodes in HU
    if (rep_id != node_id) {
      if (rep_id > util::convert_id<GraphId>(max_id)) {
        // NOTE: we don't have to merge if the rep is outside of our mapping and
        //   we don't have another rep
        auto rc = rep_remapping.emplace(rep_id, node_id);
        if (!rc.second) {
          vals_.merge(util::convert_id<Id>(node_id),
              util::convert_id<Id>(rc.first->second));
        }
      } else {
        vals_.merge(util::convert_id<Id>(node_id),
            util::convert_id<Id>(rep_id));
      }
    }
  }

  size_t num_removed = 0;
  std::set<Constraint> dedup;

  std::vector<Constraint> new_cons;
  for (size_t i = 0; i < constraints_.size(); i++) {
    auto &cons = constraints_[i];

    // Don't optimize int/null value cons
    if (cons.src() == ValueMap::IntValue ||
        cons.dest() == ValueMap::IntValue ||
        cons.src() == ValueMap::NullValue ||
        cons.dest() == ValueMap::NullValue) {
      new_cons.push_back(cons);
      continue;
    }

    auto rep_obj_id = cons.rep();
    auto src_obj_id = cons.src();
    auto dest_obj_id = cons.dest();
    auto &src_rep_node = graph.getNode(util::convert_id<GraphId>(src_obj_id));
    auto &dest_rep_node = graph.getNode(util::convert_id<GraphId>(dest_obj_id));

    auto src_rep_id = vals_.getRep(src_obj_id);
    auto dest_rep_id = vals_.getRep(dest_obj_id);
    auto rep_rep_id = vals_.getRep(rep_obj_id);

    cons.updateRep(rep_rep_id);

    if (cons.type() == ConstraintType::AddressOf) {
      cons.retarget(src_obj_id, dest_rep_id);
    } else {
      cons.retarget(src_rep_id, dest_rep_id);
    }

    // Remove any non-ptrs
    if (src_rep_node.isNonPtr() || dest_rep_node.isNonPtr()) {
      num_removed++;
      continue;
    }

    // Remove any copys to self
    if (cons.type() == ConstraintType::Copy &&
        cons.src() == cons.dest() && cons.offs() == 0) {
      num_removed++;
      continue;
    }

    auto rc = dedup.emplace(cons);
    if (!rc.second) {
      num_removed++;
      continue;
    }

    new_cons.push_back(cons);
  }

  assert(constraints_.size() - new_cons.size() == num_removed);
  constraints_.swap(new_cons);

  // Also update indirect call info:
  for (auto &tup : indirCalls_) {
    auto &id = std::get<0>(tup);
    id = vals_.getRep(id);

    auto &ci = std::get<1>(tup);
    ci.updateReps(vals_);
  }

  for (auto &pr : callInfo_) {
    auto &ci = pr.second.first;
    ci.updateReps(vals_);
  }

  localCFG_.updateNodes(vals_);

  return num_removed;
}

size_t Cg::HVN() {
  OptGraph hvn_graph;
  HVNData data(hvn_graph);

  // Get the maximum possible Id from our CG
  auto max_src_dest_id = getMaxId();

  // Now create a node for each destination
  for (int32_t i = 0; i < static_cast<int32_t>(max_src_dest_id)+1; i++) {
    auto node_id = hvn_graph.addNode();
    assert(static_cast<int32_t>(node_id) == i);

    // Force special nodes to be indirect
    auto &node = hvn_graph.getNode(node_id);
    auto obj_id = util::convert_id<ValueMap::Id>(node_id);
    if (ValueMap::isSpecial(obj_id)) {
      node.setIndirect();
    }

    // Force Allocs to be indirect
    // if (obj_id < vals_.getMaxReservedAlloc())
    if (obj_id < vals_.getMaxAlloc()) {
      node.setIndirect();
    }
  }

  auto indir_ci = [&hvn_graph] (const CallInfo &ci) {
    for (auto id : ci.args()) {
      auto &arg_node = hvn_graph.getNode(util::convert_id<GraphId>(id));
      arg_node.setIndirect();
    }

    auto ret_id = ci.ret();
    auto &ret_node = hvn_graph.getNode(util::convert_id<GraphId>(ret_id));
    ret_node.setIndirect();

    auto var_id = ci.varArg();
    if (var_id != ValueMap::Id::invalid()) {
      auto &var_node = hvn_graph.getNode(util::convert_id<GraphId>(var_id));
      var_node.setIndirect();
    }
  };

  // Now, force all indirect calls to be indirect
  for (auto &tup : indirCalls()) {
    auto &ci = std::get<1>(tup);
    indir_ci(ci);
  }

  for (auto &pr : callInfo_) {
    indir_ci(pr.second.first);
  }

  // Now, fill in the graph edges:
  std::vector<bool> touched(hvn_graph.size());
  for (auto &cons : constraints_) {
    // Don't optimize null/int values, they are special
    if (cons.src() == ValueMap::IntValue ||
        cons.dest() == ValueMap::IntValue ||
        cons.src() == ValueMap::NullValue ||
        cons.dest() == ValueMap::NullValue) {
      continue;
    }

    auto dest_val_id = cons.dest();
    auto dest_node_id = util::convert_id<GraphId>(dest_val_id);
    auto &dest_node = hvn_graph.getNode(dest_node_id);
    auto src_val_id = cons.src();
    auto src_node_id = util::convert_id<GraphId>(src_val_id);

    touched[static_cast<size_t>(dest_node_id)] = true;
    touched[static_cast<size_t>(src_node_id)] = true;

    // Handle the edge addition appropriately
    switch (cons.type()) {
      case ConstraintType::Load:
        // Load cons cause the dest to be indirect, but add no edges
        dest_node.setIndirect();
        break;
      case ConstraintType::Store:
        // Store cons are ignored
        // However, we need to ensure that the constraint is not optimized
        //   out, so we set the node to be indirect
        hvn_graph.getNode(util::convert_id<GraphId>(cons.rep())).setIndirect();
        break;
      case ConstraintType::AddressOf:
        // Alloc cons cause the dest to be indirect, no need to put objects in
        //   the graph (NOTE: They are set to indirect above)
        dest_node.setIndirect();
        break;
      case ConstraintType::Copy:
        // Copy cons:
        // Without offsets are edges
        if (cons.offs() == 0) {
          dest_node.addPred(src_node_id);
        // With offsets create a new PE, labeled by the src, offs combo
        } else {
          dest_node.addPtsTo(data.getGEPPE(src_node_id, cons.offs()));
        }
        break;
    }
  }

  // Set any untouched nodes to be an "indirect node" so it isn't incorrectly
  //   merged (since the untouched nodes may have been previously merged when
  //   running HRU, we could cause incorrect points-to sets by merging them)
  for (size_t i = 0; i < touched.size(); ++i) {
    auto node_id = OptGraph::Id(i);
    auto &node = hvn_graph.getNode(node_id);
    if (!touched[i]) {
      node.setIndirect();
    }
  }

  auto traverse_pe = [&data, &hvn_graph] (HVNNode &node, GraphId node_id) {
    // If node is indirect, add a new PE
    auto node_rep = hvn_graph.getRep(node_id);
    if (node.indirect()) {
      node.addPtsTo(data.getNextPE());
    }

    // Now, unite any pred ids:
    for (auto pred_id : node.preds()) {
      auto pred_rep = hvn_graph.getRep(pred_id);
      auto &pred_node = hvn_graph.getNode(pred_id);

      // skip pointers to self
      if (pred_rep == node_rep) {
        continue;
      }

      // If the pred node isn't a non_ptr
      if (!pred_node.ptsto().test(HVNNode::PENonPtr)) {
        node.addPtsTo(data.getHashValue(pred_node));
      }
    }

    if (node.ptsto().empty()) {
      node.addPtsTo(HVNNode::PENonPtr);
    }

    node.cleanPreds();
  };

  // hvn_graph.printDotFile("HVNStart.dot", *g_omap);
  // Finally run Tarjan's:
  run_tarjans(hvn_graph, traverse_pe);

  std::unordered_map<util::SparseBitmap<int32_t>, GraphId> pts_to_pe;

  for (GraphId id(0); id < GraphId(hvn_graph.size()); id++) {
    auto &node = hvn_graph.getNode(id);
    // We're done w/ preds now, clear them
    node.clearPreds();

    auto &ptsto = node.ptsto();

    if (ptsto.empty() || ptsto.test(HVNNode::PENonPtr)) {
      // assert(ptsto.count() <= 1);
      node.makeNonPtr();
    }

    auto ret = pts_to_pe.emplace(ptsto, hvn_graph.getRep(id));
    if (!ret.second) {
      auto it = ret.first;

      // auto &rep_node = hvn_graph.getNode(it->second);

      auto rep_id = hvn_graph.merge(id, it->second);
      it->second = rep_id;
    }
  }

  // Now, update constraints based on the hvn_graph, return how many constraitns
  //    we removed
  return updateConstraints(hvn_graph);
}

size_t Cg::HU() {
  OptGraph hvn_graph;
  HVNData data(hvn_graph);

  // Get the maximum possible Id from our CG
  auto max_src_dest_id = getMaxId();

  // Now create a node for each destination
  for (int32_t i = 0; i < static_cast<int32_t>(max_src_dest_id)+1; i++) {
    auto node_id = hvn_graph.addNode();
    assert(static_cast<int32_t>(node_id) == i);

    // Force special nodes to be indirect
    auto &node = hvn_graph.getNode(node_id);
    auto obj_id = util::convert_id<ValueMap::Id>(node_id);
    if (ValueMap::isSpecial(obj_id)) {
      node.setIndirect();
    }

    // Force Allocs to be indirect
    // if (obj_id < vals_.getMaxReservedAlloc())
    if (obj_id < vals_.getMaxAlloc()) {
      node.setIndirect();
    }
  }

  auto indir_ci = [&hvn_graph] (const CallInfo &ci) {
    for (auto id : ci.args()) {
      auto &arg_node = hvn_graph.getNode(util::convert_id<GraphId>(id));
      arg_node.setIndirect();
    }

    auto ret_id = ci.ret();
    auto &ret_node = hvn_graph.getNode(util::convert_id<GraphId>(ret_id));
    ret_node.setIndirect();

    auto var_id = ci.varArg();
    if (var_id != ValueMap::Id::invalid()) {
      auto &var_node = hvn_graph.getNode(util::convert_id<GraphId>(var_id));
      var_node.setIndirect();
    }
  };

  // Now, force all indirect calls to be indirect
  for (auto &tup : indirCalls()) {
    auto &ci = std::get<1>(tup);
    indir_ci(ci);
  }

  for (auto &pr : callInfo_) {
    indir_ci(pr.second.first);
  }

  // Now, fill in the graph edges:
  std::vector<bool> touched(hvn_graph.size());
  for (auto &cons : constraints_) {
    // Don't optimize null/int values, they are special
    if (cons.src() == ValueMap::IntValue ||
        cons.dest() == ValueMap::IntValue ||
        cons.src() == ValueMap::NullValue ||
        cons.dest() == ValueMap::NullValue) {
      continue;
    }

    auto dest_val_id = cons.dest();
    auto dest_node_id = util::convert_id<GraphId>(dest_val_id);
    auto &dest_node = hvn_graph.getNode(dest_node_id);
    auto src_val_id = cons.src();
    auto src_node_id = util::convert_id<GraphId>(src_val_id);

    touched[static_cast<size_t>(dest_node_id)] = true;
    touched[static_cast<size_t>(src_node_id)] = true;

    // Handle the edge addition appropriately
    switch (cons.type()) {
      case ConstraintType::Load:
        {
          // Load cons cause the dest to be indirect, but add no edges
          dest_node.setIndirect();
          auto src_ref_id = data.getRef(src_node_id);
          dest_node.addPred(src_ref_id);
        }
        break;
      case ConstraintType::Store:
        {
          // Store cons are ignored
          // However, we need to ensure that the constraint is not optimized
          //   out, so we set the node to be indirect
          hvn_graph.getNode(
              util::convert_id<GraphId>(cons.rep())).setIndirect();
          auto dest_ref_id = data.getRef(dest_node_id);
          auto &dest_ref = hvn_graph.getNode(dest_ref_id);
          dest_ref.addPred(src_node_id);
        }
        break;
      case ConstraintType::AddressOf:
        {
          // Alloc cons cause the dest to be indirect, no need to put objects in
          //   the graph (NOTE: They are set to indirect above)
          dest_node.setIndirect();
          auto dest_ref_id = data.getRef(dest_node_id);
          auto &dest_ref = hvn_graph.getNode(dest_ref_id);

          dest_ref.addImplicitPred(src_node_id);
        }
        break;
      case ConstraintType::Copy:
        // Copy cons:
        // Without offsets are edges
        if (cons.offs() == 0) {
          dest_node.addPred(src_node_id);

          auto src_ref_id = data.getRef(src_node_id);
          auto dest_ref_id = data.getRef(dest_node_id);
          auto &dest_ref = hvn_graph.getNode(dest_ref_id);

          dest_ref.addImplicitPred(src_ref_id);
        // With offsets create a new PE, labeled by the src, offs combo
        } else {
          dest_node.addPtsTo(data.getGEPPE(src_node_id, cons.offs()));
        }
        break;
    }
  }

  // Set any untouched nodes to be an "indirect node" so it isn't incorrectly
  //   merged (since the untouched nodes may have been previously merged when
  //   running HRU, we could cause incorrect points-to sets by merging them)
  for (size_t i = 0; i < touched.size(); ++i) {
    auto node_id = OptGraph::Id(i);
    auto &node = hvn_graph.getNode(node_id);
    if (!touched[i]) {
      node.setIndirect();
    }
  }

  auto traverse_pe = [this, &data, &hvn_graph]
      (HVNNode &node, GraphId node_id) {
    // If node is indirect, add a new PE
    auto node_rep = hvn_graph.getRep(node_id);

    if (node.indirect()) {
      node.addPtsTo(data.getNextPE());
    }

    // Now, unite any pred ids:
    for (auto pred_id : node.preds()) {
      if (node.isImplicitPred(pred_id)) {
        continue;
      }

      auto pred_rep = hvn_graph.getRep(pred_id);
      auto &pred_node = hvn_graph.getNode(pred_rep);

      // skip pointers to self
      if (pred_rep == node_rep) {
        continue;
      }

      // If the pred node isn't a non_ptr
      if (!pred_node.ptsto().test(HVNNode::PENonPtr)) {
        node.ptsto() |= pred_node.ptsto();
      }
    }

    if (node.ptsto().empty()) {
      node.addPtsTo(HVNNode::PENonPtr);
    }

    node.cleanPreds();
  };

  // hvn_graph.printDotFile("HVNStart.dot", *g_omap);
  // Finally run Tarjan's:
  run_tarjans(hvn_graph, traverse_pe);

  std::unordered_map<util::SparseBitmap<int32_t>, GraphId> pts_to_pe;

  for (GraphId id(0); id < GraphId(hvn_graph.size()); id++) {
    auto &node = hvn_graph.getNode(id);
    // We're done w/ preds now, clear them
    node.clearPreds();

    auto &ptsto = node.ptsto();

    if (ptsto.empty() || ptsto.test(HVNNode::PENonPtr)) {
      // assert(ptsto.count() <= 1);
      node.makeNonPtr();
      continue;
    }

    /*
    if (util::convert_id<Id>(id) < vals_.getMaxAlloc() ||
        util::convert_id<Id>(id) > vals_.getMaxReservedAlloc()) {
      llvm::dbgs() << "Node: " << id << " has pts: " << ptsto << "\n";
    }
    */
    auto ret = pts_to_pe.emplace(ptsto, hvn_graph.getRep(id));
    if (!ret.second) {
      auto it = ret.first;

      // auto &rep_node = hvn_graph.getNode(it->second);

      auto rep_id = hvn_graph.merge(id, it->second);
      it->second = rep_id;
    }
  }

  // Now, update constraints based on the hvn_graph, return how many constraitns
  //    we removed
  return updateConstraints(hvn_graph);
}

// Plan:
//  Get results ready for ASPLOS
//    Get speculative version functioning
//      Working on tests & zlib
//    Get non-CS version back to functioning
//      Get working on tests & zlib
//    Get speculative non-CS version running
//      Get working on tests & zlib
//
//      !!GOAL: by Tuesday!!
//
//    Get benchmarks working w/ test infrastructure
//      For all benchmarks
//    Evaluate on existing benchmarks
//      #'s should be good for prelim asplos #'s
//
//    Once I have #'s,
//    Optimize to improve numbers
//      Global Dedup
//      Local optimization (before merge)
//      HCD
//      Incremental Tarjan's
//      Better Indir cycle detection

// TODO(ddevec) HCD...
/*
void Cg::HCD() {
  return updateConstraints(hvn_graph);
}
*/

void Cg::HRU(size_t min_removed) {
  int32_t itr = 0;
  size_t num_removed;
  do {
    llvm::dbgs() << "HRU iter: " << itr << "\n";
    num_removed = HU();
    // num_removed = HVN(cg, omap);
    llvm::dbgs() << "  num_removed: " << num_removed << "\n";
    itr++;
  } while (num_removed > min_removed);
}

void Cg::HR(size_t min_removed) {
  int32_t itr = 0;
  size_t num_removed;
  do {
    llvm::dbgs() << "HR iter: " << itr << "\n";
    num_removed = HVN();
    llvm::dbgs() << "  num_removed: " << num_removed << "\n";
    itr++;
  } while (num_removed > min_removed);
}


void Cg::optimize() {
  // Run HVN then HRU over the CG's constraints
  llvm::dbgs() << "before HVN constraint_size: " << constraints_.size() <<
    "\n";
  // HR(1000);
  HVN();
  llvm::dbgs() << "after HVN constraint_size: " << constraints_.size() <<
    "\n";

  // HVN();
  HRU(100);
  llvm::dbgs() << "after HRU constraint_size: " << constraints_.size() <<
    "\n";
}

