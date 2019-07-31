/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/lib/SpecCsCFG.h"

#include <algorithm>
#include <iterator>
#include <map>
#include <vector>
#include <unordered_set>

#include "include/lib/CallDests.h"
#include "include/Tarjans.h"

// Add Function CFG stuff here
// Get callsite info...
// Etc...

extern llvm::cl::opt<bool> no_spec;

/*
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
        }
      }
    }
  }
}
*/

char SpecCsCFG::ID = 0;
SpecCsCFG::SpecCsCFG() : llvm::ModulePass(ID) { }
namespace llvm {
static RegisterPass<SpecCsCFG> cX("SpecCsCFG",
    "Adds Control Flow Graph tracing for Callsites",
    false, false);
}  // namespace llvm

void SpecCsCFG::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  // Analysis that handles indirect function targets...
  usage.addRequired<CallDests>();

  // Unused Function Info
  usage.addRequired<UnusedFunctions>();

  // EOM
  usage.setPreservesAll();
}

bool SpecCsCFG::runOnModule(llvm::Module &m) {
  auto &call_info = getAnalysis<CallDests>();
  auto &dyn_info = getAnalysis<UnusedFunctions>();
  std::multimap<const llvm::Function *,
    const llvm::Instruction *> fcn_to_calls;
  // Populate our SEG to contain all of the functions as nodes
  // Step one, add a node for each function
  mainNode_ = util::convert_id<Id>(csGraph_.addNode<CsNode>(nullptr));

  for (auto &fcn : m) {
    if (!dyn_info.isUsed(fcn) && !no_spec) {
      continue;
    }
    for (auto &bb : fcn) {
      if (!dyn_info.isUsed(bb) && !no_spec) {
        continue;
      }

      for (auto &inst : bb) {
        if (auto ci = dyn_cast<llvm::CallInst>(&inst)) {
          auto node_id = csGraph_.addNode<CsNode>(ci);
          csMap_.emplace(ci, node_id);
          fcn_to_calls.emplace(&fcn, ci);
        }
      }
    }
  }

  // Add edges for all of the callsites
  for (auto &fcn : m) {
    if (!dyn_info.isUsed(fcn) && !no_spec) {
      continue;
    }

    for (auto &bb : fcn) {
      if (!dyn_info.isUsed(bb) && !no_spec) {
        continue;
      }

      for (auto &inst : bb) {
        auto pinst = &inst;

        if (auto ci = dyn_cast<llvm::CallInst>(pinst)) {
          llvm::ImmutableCallSite cs(ci);


          auto src_id = csMap_.at(ci);
          auto dests = call_info.getDests(cs);
          /*
          llvm::dbgs() << "CS: " << *ci << "\n";
          for (auto &dest : dests) {
            llvm::dbgs() << "  dest: " << dest->getName() << "\n";
          }
          */

          // Add node for "main"
          if (fcn.getName() == "main") {
            /*
            llvm::dbgs() << "  Adding main pred: " << src_id << "->" <<
              mainNode_ << "\n";
            */

            csGraph_.addPred(src_id, util::convert_id<SEG::NodeID>(mainNode_));
          }

          // llvm::dbgs() << "call: " << ValPrinter(ci) << "\n";
          for (auto pdest_fcn : dests) {
            auto pred_set = fcn_to_calls.equal_range(pdest_fcn);
            // llvm::dbgs() << "  calls: " << ValPrinter(pdest_fcn) << "\n";

            for (auto it = pred_set.first, en = pred_set.second;
                it != en; ++it) {
              assert(it->first == pdest_fcn);
              auto dest_id = csMap_.at(it->second);
              csGraph_.addPred(dest_id, src_id);
              /*
              llvm::dbgs() << "  Adding pred: " << src_id << "->" <<
                dest_id << "\n";
              */
            }
          }
        } else if (auto ii = dyn_cast<llvm::InvokeInst>(pinst)) {
          llvm::dbgs() << "Unexpected invoke inst: " << *ii << "\n";
          llvm_unreachable("I don't support invokes!");
        }
      }
    }
  }

  // Calculate SCC
  {
    RunTarjans<> X(csGraph_);
  }

  // Tarjans can leave some duplicated edges, we don't want to deal with those
  csGraph_.cleanGraph();

  // Done
  return false;
}

static size_t num_added = 0;
static size_t num_vecs_added = 0;
static size_t most_preds = 0;

void SpecCsCFG::findPath(const CsNode &node, Id end,
    std::unordered_map<Id, std::vector<std::vector<Id>>, Id::hasher> &cache)
    const {
  auto node_id = util::convert_id<Id>(node.id());
  if (node_id == end) {
    cache[node_id].emplace_back(std::vector<Id>(1, end));
  } else {
    // See if we have this node cached?
    if (cache.find(node_id) != std::end(cache)) {
      return;
    }

    std::vector<std::vector<Id>> rets;

    auto &preds = node.preds();
    /*
    // most_preds = std::max(static_cast<size_t>(preds.size()), most_preds);
    if (most_preds <= static_cast<size_t>(preds.size())) {
      llvm::dbgs() << "Have most preds: " << preds.size() << "\n";
      llvm::dbgs() << "Fcns:\n";
      for (auto inst : node.reps()) {
        llvm::dbgs() << "  " << ValPrinter(inst) << "\n";
      }
      most_preds = preds.size();
    }
    */

    std::unordered_set<SEG::NodeID> dedup_set;

    for (auto &pred_id : preds) {
      auto &pred_node = csGraph_.getNode<CsNode>(pred_id);
      // Don't find a pred to myself
      if (util::convert_id<Id>(pred_node.id()) == node_id) {
        continue;
      }

#ifndef NDEBUG
      auto rc =
#endif
        dedup_set.emplace(pred_node.id());
      assert(rc.second);

      findPath(pred_node, end, cache);

      auto it = cache.find(util::convert_id<Id>(pred_node.id()));
      assert(it != std::end(cache));

      auto &pred_vec = it->second;

      // Copy all of the cached nodes into rets
      /*
      auto ins_it = rets.insert(std::end(rets),
          std::begin(pred_vec), std::end(pred_vec));
      for (auto en = std::end(rets); ins_it != en; ++ins_it) {
        ins_it->emplace_back(node_id);
      }
      */
      // Handle sizing appropriately...
      for (auto &vec : pred_vec) {
        rets.emplace_back(vec.size()+1);
        auto &new_vec = rets.back();
        std::copy(std::begin(vec), std::end(vec), std::begin(new_vec));
        new_vec[vec.size()] = node_id;
      }
    }

    num_added++;
    num_vecs_added += rets.size();
    cache.emplace(node_id, std::move(rets));
  }
}

const std::vector<std::vector<SpecCsCFG::Id>> &
SpecCsCFG::findPathsFromMain(Id end) const {
  // Ugh, this is uglytown
  // Optimizations
  // Use DP algorithm,
  // Memoize path results in table
  std::unordered_map<Id, std::vector<std::vector<Id>>, Id::hasher>
    result_cache;

  // basic Algorithm:
  //   findPath(node, goal_node):
  //     if node == goal_node:
  //       return { goal_node }
  //     else
  //       for succ in node.succs():
  //         return { node } + findPath(succ, goal_nodes)
  //
  // Memoize:
  //   add PathCache:
  //     if node == goal_node:
  //       return { goal_node }
  //     if node in PathCache:
  //       return PathCache.at(node)
  //     else:
  //       for succ in node.succs():
  //         update PathCache[node]
  //         return { node } + findPath(succ, goal_nodes)
  auto it = pathCache_.find(end);

  if (it != std::end(pathCache_)) {
    return it->second;
  }

  llvm::dbgs() << "Find path with graph size: " << csGraph_.getNumNodes() <<
    "\n";

  num_added = 0;
  num_vecs_added = 0;
  most_preds = 0;
  auto &end_node = csGraph_.getNode<CsNode>(
      util::convert_id<SEG::NodeID>(end));
  findPath(end_node, mainNode_,
      result_cache);

  llvm::dbgs() << "total num added: " << num_added << "\n";
  llvm::dbgs() << "total num vecs added: " << num_vecs_added << "\n";
  llvm::dbgs() << "most preds: " << most_preds << "\n";

  auto rc_it = result_cache.find(util::convert_id<Id>(end_node.id()));

  if (rc_it == std::end(result_cache)) {
    static std::vector<std::vector<SpecCsCFG::Id>> empty_vector;
    llvm::dbgs() << "WARNING: No path from main to: " << end << "\n";
    return empty_vector;
  }

  auto &ret = rc_it->second;

  auto rc = pathCache_.emplace(end, std::move(ret));

  // llvm::dbgs() << "have paths of size: " << rc.first->second.size() << "\n";
  return rc.first->second;
}

