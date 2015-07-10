/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_SPECSFS_H_
#define INCLUDE_SPECSFS_H_

#include <vector>

#include "include/Andersens.h"
#include "include/SpecSFS.h"
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
  bool createConstraints(DUG &graph, ObjectMap &omap,
      const llvm::Module &M);

  // Optimizes the top-level constraints in the DUG
  // This requires the omap, so it knows which ids are objects, and doesn't
  //   group them
  bool optimizeConstraints(DUG &graph, const ObjectMap &omap);

  // Adds additional indirect call info, given an AUX analysis
  //   (in this case, Andersens analysis)
  bool addIndirectCalls(DUG &graph, const Andersens &aux,
      ObjectMap &omap);

  // Computes SSA form of the DUG, given its current edge set
  //   Used to compute SSA for top lvl
  bool computeSSA(DUG &graph,
      const std::vector<DUG::CFGEdge> &edges);

  // Fills in conservative address-taken given an conservative AUX
  bool fillAddressTaken(DUG &, const Andersens &) { return false; }

  // Computes partitons based on the conservative address-taken info, the
  // partitions are based on "access-equivalence"
  bool computePartitions(DUG &) { return false; }

  // Computes the SSA form of each partition
  bool computePartSSA(DUG &) { return false; }

  // Solves the remaining graph, providing full flow-sensitive inclusion-based
  // points-to analysis
  bool solve(DUG &) { return false; }
};

#endif  // INCLUDE_SPECSFS_H_
