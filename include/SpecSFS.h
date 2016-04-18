/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_SPECSFS_H_
#define INCLUDE_SPECSFS_H_

#include <map>
#include <memory>
#include <vector>

#include "include/Assumptions.h"
#include "include/ConstraintPass.h"
#include "include/DUG.h"
#include "include/ExtInfo.h"
#include "include/ObjectMap.h"
#include "include/SpecAnders.h"
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
class SpecSFS : public llvm::ModulePass,
                public llvm::AliasAnalysis {
 public:
  static char ID;
  SpecSFS();

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
    return "SpecSFS";
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

  virtual void deleteValue(llvm::Value *V);

  virtual void copyValue(llvm::Value *From, llvm::Value *To);

  PtstoSet &getPtstoSet(const llvm::Value *val) {
    return pts_top_.at(omap_.getValue(val));
  }

  const AssumptionSet &getSpecAssumptions() const {
    return specAssumptions_;
  }

  ObjectMap &getObjectMap() {
    return omap_;
  }

  const ExtLibInfo &getLibInfo() const {
    return *extInfo_;
  }

 private:
  // The functions which do the primary (high-level) work of SFS


  // Computes SSA form of the DUG, given its current edge set
  //   Used to compute SSA for top lvl
  void computeSSA(CFG::ControlFlowGraph &cfg);

  // Takes dynamic pointsto information, as well as hot/cold basic block
  //   information, and trims the edges of the DUG appropriately
  std::map<ObjectMap::ObjID, Bitmap>
  addDynPtstoInfo(llvm::Module &m, DUG &graph, CFG &cfg, ObjectMap &omap,
      const ExtLibInfo &ext_info);


  // Computes partitons based on the conservative address-taken info, the
  //   partitions are based on "access-equivalence"
  // NOTE: ObjectMap is required to convert DUG::ObjID to llvm::Value as
  //   Andersens works with llvm::Value's
  bool computePartitions(DUG &dug, CFG &cfg, SpecAnders &aux,
      ObjectMap &omap);

  // Computes the SSA form of each partition
  bool addPartitionsToDUG(DUG &graph, CFG &cfg, const ObjectMap &omap);

  // Solves the remaining graph, providing full flow-sensitive inclusion-based
  // points-to analysis
  bool solve(DUG &dug,
      std::map<ObjectMap::ObjID, Bitmap> dyn_constraints);

 protected:
  /*
  // Optimizes the top-level constraints in the DUG
  // This requires the omap, so it knows which ids are objects, and doesn't
  //   group them
  // It also requires the CFG, because it will change the destination of some
  //   loads
  bool optimizeConstraints(ConstraintGraph &graph, CFG &cfg,
      ObjectMap &omap);
      */

  /*
  // Adds additional indirect call info, given an AUX analysis
  //   (in this case, Andersens analysis)
  bool addIndirectCalls(ConstraintGraph &cg, CFG &cfg,
      SpecAnders &aux, const IndirFunctionInfo *, ObjectMap &omap);
      */

  // Private data {{{
  const ExtLibInfo *extInfo_;
  ObjectMap omap_;
  TopLevelPtsto pts_top_;

  AssumptionSet specAssumptions_;

  /*
  ObjectMap::ObjID getObjIDRep(ObjectMap::ObjID id) {
    auto it = obj_to_rep_.find(id);
    if (it == std::end(obj_to_rep_)) {
      return id;
    }

    it->second = getObjIDRep(it->second);
    return it->second;
  }

  void setObjIDRep(ObjectMap::ObjID id, ObjectMap::ObjID rep) {
    obj_to_rep_[id] = rep;
  }
  */

  std::map<ObjectMap::ObjID, ObjectMap::ObjID> obj_to_rep_;
  //}}}
};

// Optimizes the top-level constraints in the DUG
// This requires the omap, so it knows which ids are objects, and doesn't
//   group them
// It also requires the CFG, because it will change the destination of some
//   loads
bool SFSHU(ConstraintGraph &graph, CFG &cfg,
    ObjectMap &omap);

// Adds additional indirect call info, given an AUX analysis
//   (in this case, Andersens analysis)
bool addIndirectCalls(ConstraintGraph &cg, CFG &cfg,
    SpecAnders &aux, const IndirFunctionInfo *, ObjectMap &omap,
    const ExtLibInfo &ext_info);

#endif  // INCLUDE_SPECSFS_H_
