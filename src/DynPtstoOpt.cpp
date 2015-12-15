/*
 * Copyright (C) 2015 David Devecsery
 */

#include <algorithm>
#include <map>
#include <set>
#include <string>
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

static llvm::cl::opt<std::string>
  TimeThresholdStr("specsfs-dyn-threshold", llvm::cl::init(".00001"),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("Threshold to consider a dynamic ptsto value cold"));

class CostApprox {
 public:
    // 1/10000?
    // Go needs less accurate dyn-ptsto info to be performant (it still retains
    //   solid accuracy with this rate though)
    // static constexpr double TimeThreshold = .00001;
    // Sphinx needs more accurate dyn ptsto data to benefit... although it
    //   doesn't seem to slow it down as much as expected...
    // static constexpr double TimeThreshold = .001;
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

      auto TimeThreshold = stod(TimeThresholdStr);
      auto ret = (bb_dyn_insts / totalDynInsts_) < TimeThreshold;

      return ret;
    }

    bool costIsLow(const std::vector<std::unique_ptr<InstrumentationSite>>
        &inst_site_vec) {
      double total_cost = 0;

      for (auto &pinst : inst_site_vec) {
        auto bb = pinst->getBB();

        total_cost += pinst->approxCost() * pi_.getExecutionCount(bb);
      }

      total_cost /= totalDynInsts_;

      auto TimeThreshold = stod(TimeThresholdStr);
      return total_cost < TimeThreshold;
    }

 private:
    llvm::ProfileInfo &pi_;
    double totalDynInsts_ = 0.0;
};

std::map<ObjectMap::ObjID, Bitmap>
SpecSFS::addDynPtstoInfo(llvm::Module &m, DUG &,
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

  std::map<ObjectMap::ObjID, Bitmap> top_level_constraints;

  // If we have the dynamic information do the optimization
  if (unused_fcn.hasInfo() && dyn_ptsto.hasInfo()) {
    CostApprox ca(m, prof_info);

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
              if (llvm::isa<llvm::PointerType>(instr.getType()) &&
                  !llvm::isa<llvm::AllocaInst>(instr)) {
                if (auto ci = dyn_cast<llvm::CallInst>(&instr)) {
                  auto fcn = LLVMHelper::getFcnFromCall(ci);

                  if (fcn != nullptr && AllocInfo::fcnIsMalloc(fcn)) {
                    continue;
                  }
                }


                auto val_id = omap.getValue(&instr);

                // NOTE: in the instance I encounter an unknown value in my
                //   dynamic ptsto analysis, I will drop that ptsto, so
                //   hasPtsto is needed...
                if (dyn_ptsto.hasPtsto(val_id)) {
                  // Add dyn_ptsto info for this top level variable

                  // Don't add dyn_ptsto info for alloc instructions
                  std::unique_ptr<Assumption> ptsto_aspn(new PtstoAssumption(
                        &instr, dyn_ptsto.getPtsto(val_id)));

                  auto approx_deps = ptsto_aspn->getApproxDependencies(omap, m);

                  if (ca.costIsLow(approx_deps)) {
                    auto &dyn_bmp = top_level_constraints[val_id];
                    for (auto &cons : dyn_ptsto.getPtsto(val_id)) {
                      auto pr = omap.findObjAliases(cons);

                      if (pr.first) {
                        for (auto field : pr.second) {
                          dyn_bmp.set(field.val());
                        }
                      }

                      dyn_bmp.set(cons.val());
                    }

                    specAssumptions_.add(std::move(ptsto_aspn));
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  return std::move(top_level_constraints);
}

