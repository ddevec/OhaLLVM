/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_SPECSFS_H_
#define INCLUDE_SPECSFS_H_

#include <map>
#include <memory>
#include <vector>

#include "include/Andersens.h"
#include "include/Assumptions.h"
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

extern llvm::cl::opt<bool> do_spec;

// The actual SFS module, most of the work is done via the ObjectMap and Def-Use
// Graph (DUG), these methods mostly operate on them.
class SpecSFS : public llvm::ModulePass,
                public llvm::AliasAnalysis {
 public:
  static char ID;
  SpecSFS();
  explicit SpecSFS(char &id);

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

  ObjectMap &getObjectMap() {
    return omap_;
  }

  PtstoSet &getPtstoSet(const llvm::Value *val) {
    return pts_top_.at(omap_.getValue(val));
  }

  const std::vector<std::unique_ptr<Assumption>> &
  getSpecAssumptions() const {
    return specAssumptions_;
  }

 private:
  // The functions which do the primary (high-level) work of SFS


  // Computes SSA form of the DUG, given its current edge set
  //   Used to compute SSA for top lvl
  void computeSSA(CFG::ControlFlowGraph &cfg);

  // Takes dynamic pointsto information, as well as hot/cold basic block
  //   information, and trims the edges of the DUG appropriately
  std::map<ObjectMap::ObjID, Bitmap>
  addDynPtstoInfo(llvm::Module &m, DUG &graph, CFG &cfg, ObjectMap &omap);


  // Computes partitons based on the conservative address-taken info, the
  //   partitions are based on "access-equivalence"
  // NOTE: ObjectMap is required to convert DUG::ObjID to llvm::Value as
  //   Andersens works with llvm::Value's
  bool computePartitions(DUG &dug, CFG &cfg, Andersens &aux,
      ObjectMap &omap);

  // Computes the SSA form of each partition
  bool addPartitionsToDUG(DUG &graph, CFG &cfg, const ObjectMap &omap);

  // Solves the remaining graph, providing full flow-sensitive inclusion-based
  // points-to analysis
  bool solve(DUG &dug,
      std::map<ObjectMap::ObjID, Bitmap> dyn_constraints);

 protected:
  // Identifies all objects in the module, adds them to graph
  bool identifyObjects(ObjectMap &omap, const llvm::Module &M);

  // Creates constraints for each top-lvel operatioon in the module
  // Also populates Def/Use info for later address-taken constraints
  bool createConstraints(ConstraintGraph &cg, CFG &cfg, ObjectMap &omap,
      const llvm::Module &M, const UnusedFunctions &unused);

  // Optimizes the top-level constraints in the DUG
  // This requires the omap, so it knows which ids are objects, and doesn't
  //   group them
  // It also requires the CFG, because it will change the destination of some
  //   loads
  bool optimizeConstraints(ConstraintGraph &graph, CFG &cfg,
      ObjectMap &omap);

  // Adds additional indirect call info, given an AUX analysis
  //   (in this case, Andersens analysis)
  bool addIndirectCalls(ConstraintGraph &cg, CFG &cfg,
      const Andersens &aux, const IndirFunctionInfo *, ObjectMap &omap);

  // Private data {{{
  ObjectMap omap_;
  TopLevelPtsto pts_top_;

  std::vector<std::unique_ptr<Assumption>> specAssumptions_;

  void addSpeculativeAssumption(std::unique_ptr<Assumption> a) {
    specAssumptions_.emplace_back(std::move(a));
  }

  void identifyAUXFcnCallRetInfo(CFG &cfg,
      ObjectMap &omap, const Andersens &aux,
      const IndirFunctionInfo *dyn_info);
  void scanFcn(const UnusedFunctions &unused_fcns,
      ConstraintGraph &cg, CFG &cfg,
      ObjectMap &omap, const llvm::Function &fcn);

  void processBlock(const UnusedFunctions &unused_fcns,
    ConstraintGraph &cg, CFG &cfg,
    std::map<const llvm::BasicBlock *, CFG::CFGid> &seen,
    ObjectMap &omap, const llvm::BasicBlock &BB, CFG::CFGid parent_id);

  // FIXME: Should put in another entity? oh well...
  // std::map<int, ObjectMap::ObjID> aux_to_obj_;
  std::vector<ObjectMap::ObjID> aux_to_obj_;
  std::map<ObjectMap::ObjID, int> special_aux_;

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

  std::map<ObjectMap::ObjID, ObjectMap::ObjID> obj_to_rep_;
  //}}}
};

#endif  // INCLUDE_SPECSFS_H_
