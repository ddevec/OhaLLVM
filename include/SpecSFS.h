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

  bool runOnModule(llvm::Module &M) override;

 private:
  // The functions which do the primary (high-level) work of SFS

  // Identifies all objects in the module, adds them to graph
  bool identifyObjects(ObjectMap &omap, const llvm::Module &M);

  // Creates constraints for each top-lvel operatioon in the module
  // Also populates Def/Use info for later address-taken constraints
  bool createConstraints(ConstraintGraph &cg, CFG &cfg, ObjectMap &omap,
      const llvm::Module &M);

  // Optimizes the top-level constraints in the DUG
  // This requires the omap, so it knows which ids are objects, and doesn't
  //   group them
  // It also requires the CFG, because it will change the destination of some
  //   loads
  bool optimizeConstraints(ConstraintGraph &graph, CFG &cfg,
      const ObjectMap &omap);

  // Adds additional indirect call info, given an AUX analysis
  //   (in this case, Andersens analysis)
  bool addIndirectCalls(ConstraintGraph &cg, CFG &cfg,
      const Andersens &aux, ObjectMap &omap);

  // Computes SSA form of the DUG, given its current edge set
  //   Used to compute SSA for top lvl
  CFG::ControlFlowGraph computeSSA(const CFG::ControlFlowGraph &cfg);

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

  // Private data {{{
  ObjectMap omap_;
  TopLevelPtsto pts_top_;
  //}}}
};

#endif  // INCLUDE_SPECSFS_H_
