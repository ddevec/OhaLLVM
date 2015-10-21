/*
 * Copyright (C) 2015 David Devecsery
 */

#include <algorithm>
#include <set>
#include <utility>
#include <vector>

#include "include/SpecSFS.h"

#include "llvm/Analysis/ProfileInfo.h"

#include "include/ControlFlowGraph.h"
#include "include/DUG.h"
#include "include/Debug.h"
#include "include/SEG.h"
#include "include/util.h"
#include "include/lib/DynPtsto.h"

class CostApprox {
 public:
    // 1/10000?
    static constexpr double TimeThreshold = .0001;
    CostApprox(const llvm::Module &m, llvm::ProfileInfo &pi) :
          pi_(pi) {
      for (auto &fcn : m) {
        for (auto &bb : fcn) {
          auto num_executions = pi.getExecutionCount(&bb);
          auto num_insts = std::distance(std::begin(bb), std::end(bb));

          totalDynInsts_ += num_executions * num_insts;
        }
      }
    }

    bool costIsLow(const llvm::BasicBlock &bb) {
      // If this block's cost is less than... 1/10000th of the execuiton time?
      auto bb_insts = std::distance(std::begin(bb), std::end(bb));
      auto dyn_executions = pi_.getExecutionCount(&bb);
      auto bb_dyn_insts = bb_insts * dyn_executions;

      auto ret = (bb_dyn_insts / totalDynInsts_) < TimeThreshold;

      return ret;
    }

 private:
    llvm::ProfileInfo &pi_;
    double totalDynInsts_ = 0.0;
};

bool SpecSFS::addDynPtstoInfo(llvm::Module &m, DUG &dug,
    CFG &, ObjectMap &omap) {
  // Okay, here we go... dynamic cold path point-to info

  // We're going to:
  // iterate each BB:
  // for each fcn
  //   for each BB in fcn
  //     If BB.exeCount is small:
  //       Use dynamic ptsto set:
  //       Remove all incoming ptsto edges
  //       Set each ptsto val to propigate a constant value
  //         -- Do this by changing node type to a new type?
  //       Change any associated CFG nodes with constant values?
  //       NO - only if I'm sure the allocation is to a single precise location
  //       NOTE: I get this information statically, so no need to change this
  //         -- unless I somehow get that info dynamically

  auto &prof_info = getAnalysis<llvm::ProfileInfo>();
  const auto &dyn_ptsto = getAnalysis<DynPtstoLoader>();
  // To check if ProfileInfo is valid...
  const auto &unused_fcn = getAnalysis<UnusedFunctions>();

  // If we have the dynamic information do the optimization
  if (unused_fcn.hasInfo() && dyn_ptsto.hasInfo()) {
    CostApprox ca(m, prof_info);

    std::vector<std::vector<DUG::DUGid>> dug_providers(omap.size());

    for (auto &pnode : dug) {
      auto &node = cast<DUGNode>(*pnode);

      // Store nodes do not modify top-level values directly...
      // All other nodes do
      if (!llvm::isa<DUG::StoreNode>(node)) {
        dug_providers[node.dest().val()].push_back(node.id());
      }
    }

    // For each function
    for (auto &fcn : m) {
      for (auto &bb : fcn) {
        if (unused_fcn.isUsed(bb)) {
          // Figure out how frequently the BB is used
          if (ca.costIsLow(bb)) {
            // Use dyn ptsto info
            // Get the dyn info for this BB
            for (auto &instr : bb) {
              // If we have an instruction returning a pointer, modify its
              // node w/ the constant ptr info
              if (llvm::isa<llvm::PointerType>(instr.getType())) {
                auto val_id = omap.getValue(&instr);
                // Rewrite all nodes that provide this value:
                auto &providers = dug_providers[val_id.val()];
                for (auto &dug_id : providers) {
                  auto &dug_node = dug.getNode(dug_id);
                  assert(!llvm::isa<DUG::ConstNode>(dug_node));
                  assert(!llvm::isa<DUG::ConstPartNode>(dug_node));

                  auto &ptsto_set = dyn_ptsto.getPtsto(val_id);

                  // DONT replace alloc nodes! I need the allocations!
                  if (!llvm::isa<DUG::AllocNode>(dug_node)) {
                    // If its a PartNode, we need to go through some headache
                    llvm::dbgs() << "replacing node: " << dug_node.id() <<
                      ", val_id: " << val_id << ", with const pststo:";
                    for (auto pts : ptsto_set) {
                      llvm::dbgs() << " " << pts;
                    }
                    llvm::dbgs() << "\n";

                    dug.replaceWithConstantNode(dug_node.id(), ptsto_set);
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  return false;
}

