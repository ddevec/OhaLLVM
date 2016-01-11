/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_SPECANDERS_H_
#define INCLUDE_SPECANDERS_H_

#include <map>
#include <memory>
#include <vector>

#include "include/AndersHelpers.h"
#include "include/Assumptions.h"
#include "include/ConstraintPass.h"
#include "include/DUG.h"
#include "include/ObjectMap.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"

#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

// The actual SFS module, most of the work is done via the ObjectMap and Def-Use
// Graph (DUG), these methods mostly operate on them.

// Actually HU...
int32_t HVN(ConstraintGraph &cg, ObjectMap &omap);

void HRU(ConstraintGraph &cg, ObjectMap &omap, int32_t min_removed);

class SpecAnders : public llvm::ModulePass,
                public llvm::AliasAnalysis {
 public:
  static char ID;
  SpecAnders();
  explicit SpecAnders(char &id);

  virtual bool runOnModule(llvm::Module &M);

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  virtual void *getAdjustedAnalysisPointer(llvm::AnalysisID PI) {
    if (PI == &AliasAnalysis::ID) {
      // return (llvm::AliasAnalysis *)this;
      return static_cast<llvm::AliasAnalysis *>(this);
    }
    return this;
  }

  const char *getPassName() const override {
    return "SpecAnders";
  }

  /*
  AliasAnalysis::AliasResult alias(const llvm::Value *v1, unsigned v1size,
      const llvm::Value *v2, unsigned v2size) override;
      */

  virtual AliasAnalysis::AliasResult alias(const AliasAnalysis::Location &L1,
      const AliasAnalysis::Location &L2);

  virtual AliasAnalysis::ModRefResult getModRefInfo(llvm::ImmutableCallSite CS,
                             const llvm::AliasAnalysis::Location &Loc);
  virtual AliasAnalysis::ModRefResult getModRefInfo(llvm::ImmutableCallSite CS1,
                                     llvm::ImmutableCallSite CS2);
  /*
  void getMustAliases(llvm::Value *P,
      std::vector<llvm::Value*> &RetVals);
  */
  // Do not use it.
  bool pointsToConstantMemory(const AliasAnalysis::Location &Loc,
      bool OrLocal = false);

  /*
  virtual void deleteValue(llvm::Value *V);

  virtual void copyValue(llvm::Value *From, llvm::Value *To);
  */

  const AssumptionSet &getSpecAssumptions() const {
    return specAssumptions_;
  }

  ObjectMap &getObjectMap() {
    return omap_;
  }

  ObjectMap::ObjID getRep(ObjectMap::ObjID id) {
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
    return omap_.getRep(id);
  }

  const PtstoSet &getPointsTo(ObjectMap::ObjID id) {
    // Convert input objID to rep ObjID:
    auto rep_id = getRep(id);

    return graph_.getNode(rep_id).ptsto();
  }

 private:
  // Takes dynamic pointsto information, as well as hot/cold basic block
  //   information, and trims the edges of the DUG appropriately
  std::map<ObjectMap::ObjID, Bitmap>
  addDynPtstoInfo(llvm::Module &m, DUG &graph, ObjectMap &omap);

  void HCD(ConstraintGraph &, ObjectMap &);

  // Solves the remaining graph, providing full flow-sensitive inclusion-based
  // points-to analysis
  bool solve();

 protected:
  // Optimizes the top-level constraints in the DUG
  // This requires the omap, so it knows which ids are objects, and doesn't
  //   group them
  // It also requires the CFG, because it will change the destination of some
  //   loads
  bool optimizeConstraints(ConstraintGraph &graph, CFG &cfg,
      ObjectMap &omap);

  // Private data {{{
  ObjectMap omap_;
  AndersGraph graph_;

  AssumptionSet specAssumptions_;

  std::map<ObjectMap::ObjID, ObjectMap::ObjID> hcdPairs_;
  //}}}
};

#endif  // INCLUDE_SPECANDERS_H_
