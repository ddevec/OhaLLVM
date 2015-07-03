/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_SPECSFS_H_
#define INCLUDE_SPECSFS_H_

#include "include/DUG.h"
#include "include/ObjectMap.h"

#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

// Ugh, need to export andersens header... yeeeesh
class Andersens;

class SpecSFS : public llvm::ModulePass {
                // public llvm::AliasAnalysis {
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
  bool optimizeConstraints(DUG &graph) { return false; }

  // Adds additional indirect call info, given an AUX analysis
  //   (in this case, Andersens analysis)
  bool addIndirectCalls(DUG &graph, const Andersens &aux) { return false; }

  // Computes SSA form of the DUG, given its current edge set
  //   Used to compute SSA for top lvl
  bool computeSSA(DUG &graph) { return false; }

  // Fills in conservative address-taken given an conservative AUX
  bool fillAddressTaken(DUG &graph, const Andersens &aux) { return false; }

  // Computes partitons based on the conservative address-taken info, the
  // partitions are based on "access-equivalence"
  bool computePartitions(DUG &graph) { return false; }

  // Computes the SSA form of each partition
  bool computePartSSA(DUG &graph) { return false; }

  // Solves the remaining graph, providing full flow-sensitive inclusion-based
  // points-to analysis
  bool solve(DUG &graph) { return false; }
};

#endif  // INCLUDE_SPECSFS_H_
