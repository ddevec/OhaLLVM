/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_SPECSFS_H_
#define INCLUDE_SPECSFS_H_

#include <map>
#include <vector>

#include "include/Andersens.h"
#include "include/DUG.h"
#include "include/ObjectMap.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"

#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

// The actual SFS module, most of the work is done via the ObjectMap and Def-Use
// Graph (DUG), these methods mostly operate on them.
class SpecSFS : public llvm::ModulePass,
                public llvm::AliasAnalysis {
 public:
  static char ID;
  SpecSFS();
  explicit SpecSFS(char &id);

  bool runOnModule(llvm::Module &M) override;

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  virtual void *getAdjustedAnalysisPointer(llvm::AnalysisID PI) {
    if (PI == &AliasAnalysis::ID) {
      return reinterpret_cast<llvm::AliasAnalysis *>(this);
    }
    return this;
  }

  AliasAnalysis::AliasResult alias(const AliasAnalysis::Location &L1,
      const AliasAnalysis::Location &L2);

 private:
  // The functions which do the primary (high-level) work of SFS

  // Optimizes the top-level constraints in the DUG
  // This requires the omap, so it knows which ids are objects, and doesn't
  //   group them
  // It also requires the CFG, because it will change the destination of some
  //   loads
  bool optimizeConstraints(ConstraintGraph &graph, CFG &cfg,
      const ObjectMap &omap);


  // Computes SSA form of the DUG, given its current edge set
  //   Used to compute SSA for top lvl
  CFG::ControlFlowGraph computeSSA(const CFG::ControlFlowGraph &cfg);

  // Takes dynamic pointsto information, as well as hot/cold basic block
  //   information, and trims the edges of the DUG appropriately
  bool addDynPtstoInfo(llvm::Module &m, DUG &graph, CFG &cfg,
      ObjectMap &omap);


  // Computes partitons based on the conservative address-taken info, the
  //   partitions are based on "access-equivalence"
  // NOTE: ObjectMap is required to convert DUG::ObjID to llvm::Value as
  //   Andersens works with llvm::Value's
  bool computePartitions(DUG &dug, CFG &cfg, Andersens &aux,
      ObjectMap &omap);

  // Computes the SSA form of each partition
  bool addPartitionsToDUG(DUG &graph, const CFG &cfg, const ObjectMap &omap);

  // Solves the remaining graph, providing full flow-sensitive inclusion-based
  // points-to analysis
  bool solve(DUG &, ObjectMap &omap);

 protected:
  // Identifies all objects in the module, adds them to graph
  bool identifyObjects(ObjectMap &omap, const llvm::Module &M);

  // Creates constraints for each top-lvel operatioon in the module
  // Also populates Def/Use info for later address-taken constraints
  bool createConstraints(ConstraintGraph &cg, CFG &cfg, ObjectMap &omap,
      const llvm::Module &M, const UnusedFunctions &unused);

  // Adds additional indirect call info, given an AUX analysis
  //   (in this case, Andersens analysis)
  bool addIndirectCalls(ConstraintGraph &cg, CFG &cfg,
      const Andersens &aux, const IndirFunctionInfo *, ObjectMap &omap);

  // Private data {{{
  ObjectMap omap_;
  TopLevelPtsto pts_top_;

  // FIXME: Should put in another entity? oh well...
  std::map<int, ObjectMap::ObjID> aux_to_obj_;
  std::map<ObjectMap::ObjID, int> special_aux_;
  //}}}
};

#endif  // INCLUDE_SPECSFS_H_
