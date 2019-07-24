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

class SpecAnders : public llvm::ModulePass,
                public llvm::AAResultBase<SpecAnders> {
 public:
  friend AAResultBase<SpecAnders>;
  static char ID;
  SpecAnders();
  explicit SpecAnders(char &id);

  virtual bool runOnModule(llvm::Module &M);

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  /* FIXME: Wire this into the actual AA infrastructure... later */
  /*
  void *getAdjustedAnalysisPointer(llvm::AnalysisID PI) override {
    if (PI == &llvm::AliasAnalysis::ID) {
      return static_cast<llvm::AliasAnalysis *>(this);
    }
    return this;
  }
  */

  llvm::StringRef getPassName() const override {
    return "SpecAnders";
  }

  /*
  AliasAnalysis::AliasResult alias(const llvm::Value *v1, unsigned v1size,
      const llvm::Value *v2, unsigned v2size) override;
      */

  virtual llvm::AliasResult alias(const llvm::MemoryLocation &L1,
      const llvm::MemoryLocation &L2);

  virtual llvm::ModRefInfo getModRefInfo(llvm::ImmutableCallSite CS,
                             const llvm::MemoryLocation &Loc);
  virtual llvm::ModRefInfo getModRefInfo(llvm::ImmutableCallSite CS1,
                                     llvm::ImmutableCallSite CS2);
  /*
  void getMustAliases(llvm::Value *P,
      std::vector<llvm::Value*> &RetVals);
  */
  // Do not use it.
  bool pointsToConstantMemory(const llvm::MemoryLocation &Loc,
      bool OrLocal = false);

  /*
  virtual void deleteValue(llvm::Value *V);

  virtual void copyValue(llvm::Value *From, llvm::Value *To);
  */

  const AssumptionSet &getSpecAssumptions() const {
    return cp_->getSpecAssumptions();
  }

  ValueMap::Id getRep(ValueMap::Id id) {
    // Convert input objID to rep ObjID:
    /*
    auto rep_id = id;
    auto val = omap_.valueAtID(id);
    const llvm::Value *old_val = nullptr;
    while (!ObjectMap::isSpecial(id) && val != old_val) {
      old_val = val;
      rep_id = omap_.getValue(val);
      val = omap_.valueAtID(rep_id);
    }

    return rep_id;
    */
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

 private:
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

#endif  // INCLUDE_SPECANDERS_H_
