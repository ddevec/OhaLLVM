/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_SPECANDERS_H_
#define INCLUDE_SPECANDERS_H_

#include <map>
#include <memory>
#include <vector>

#include "include/AndersGraph.h"
#include "include/Assumptions.h"
#include "include/Cg.h"
#include "include/ValueMap.h"
#include "include/ConstraintPass.h"

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

// The actual SFS module, most of the work is done via the ObjectMap and Def-Use
// Graph (DUG), these methods mostly operate on them.

using AliasResult = llvm::AliasResult;
using MemoryLocation = llvm::MemoryLocation;

/*
class SpecAnders : public llvm::AnalysisInfoMixin<SpecAnders> {
 public:
  typedef SpecAndersAAResult Result;

  Result run(Module &m, FunctionAnalysisManager &AM);

 private:
  friend llvm::AnalysisInfoMixin<SpecAnders>;
  static llvm::AnalysisKey key;
};
*/

class SpecAndersAAResult;

class SpecAndersAnalysis {
 public:
  SpecAndersAnalysis() = default;

  void run(llvm::Module &m,
      ConstraintPass &cp,
      UnusedFunctions &uf,
      IndirFunctionInfo &indir_info,
      CallContextLoader &call_info);

  const AssumptionSet &getSpecAssumptions() const {
    return cp_->getSpecAssumptions();
  }

  ValueMap::Id getRep(ValueMap::Id id) {
    // Convert input objID to rep ObjID:
    return mainCg_->vals().getRep(id);
  }

  const PtstoSet &getPointsTo(ValueMap::Id id) {
    // Convert input objID to rep ObjID:
    auto rep_id = getRep(id);

    return graph_.getNode(rep_id).ptsto();
  }

  ConstraintPass &getConstraintPass() {
    return *cp_;
  }
  const ConstraintPass &getConstraintPass() const {
    return *cp_;
  }

 private:
  friend SpecAndersAAResult;
  // Takes dynamic pointsto information, as well as hot/cold basic block
  //   information, and trims the edges of the DUG appropriately
  /*
  std::map<ValueMap::Id, Bitmap>
  addDynPtstoInfo(llvm::Module &m, DUG &graph, ObjectMap &omap);
  */
  PtstoSet *ptsCacheGet(const llvm::Value *val);

  void addIndirCall(const PtstoSet &fcn_pts,
      const CallInfo &caller_ci,
      CsFcnCFG::Id cur_graph_node,
      Worklist<AndersGraph::Id> &wl,
      std::vector<uint32_t> &priority);
  void addIndirEdges(const CallInfo &caller_ci,
      const CallInfo &callee_ci,
      Worklist<AndersGraph::Id> &wl,
      const std::vector<uint32_t> &priority);
  void handleGraphChange(
      size_t old_size,
      Worklist<AndersGraph::Id> &wl,
      std::vector<uint32_t> &priority);

  // Solves the remaining graph, providing full flow-sensitive inclusion-based
  // points-to analysis
  bool solve();

  // Private data {{{
  AndersGraph graph_;

  std::unique_ptr<DynamicInfo> dynInfo_;

  // Imported from ConstraintPass
  std::unique_ptr<Cg> mainCg_;
  std::unique_ptr<CgCache> cgCache_;
  std::unique_ptr<CgCache> callCgCache_;

  ConstraintPass *cp_;

  std::unordered_map<const llvm::Value *, PtstoSet> ptsCache_;

  // std::map<ObjectMap::ObjID, ObjectMap::ObjID> hcdPairs_;
  //}}}
};

template <class T>
using AAResultBase = llvm::AAResultBase<T>;

class SpecAndersAAResult : public AAResultBase<SpecAndersAAResult> {
 public:
  explicit SpecAndersAAResult(SpecAndersAnalysis &anders) :
    AAResultBase<SpecAndersAAResult>(), anders_(anders) { }
  SpecAndersAAResult(SpecAndersAAResult &&arg) :
    AAResultBase(std::move(arg)), anders_(arg.anders_) { }

  AliasResult alias(const MemoryLocation &LocA, const MemoryLocation &LocB);

 private:
  SpecAndersAnalysis &anders_;
};

class SpecAndersWrapperPass : public llvm::ModulePass {
 public:
  static char ID;
  SpecAndersWrapperPass();
  explicit SpecAndersWrapperPass(char &id);

  virtual bool runOnModule(llvm::Module &M);

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  llvm::StringRef getPassName() const override {
    return "SpecAnders";
  }

  SpecAndersAAResult &getResult() { return *result_; }
  const SpecAndersAAResult &getResult() const { return *result_; }

  const SpecAndersAnalysis &anders() const { return anders_; }

 private:
  SpecAndersAnalysis anders_;
  std::unique_ptr<SpecAndersAAResult> result_;
};

#endif  // INCLUDE_SPECANDERS_H_
