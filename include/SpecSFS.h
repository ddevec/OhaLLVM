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

#include "llvm/ADT/SparseBitVector.h"

// Bitmap used in many places (and by Andersen's) to represent ptsto
typedef llvm::SparseBitVector<> Bitmap;

// Required for using a Bitmap as a std::map key (used for ID gathering) {{{
struct BitmapLT {
  bool operator() (const Bitmap &b1, const Bitmap &b2) {
    auto it1 = std::begin(b1);
    auto it2 = std::begin(b2);
    auto en1 = std::end(b1);
    auto en2 = std::end(b2);

    // True if any element b1 < b2
    for (; it1 != en1 && it2 != en2; ++it1, ++it2) {
      // if it1 < it2 : b1 < b2
      if (*it1 < *it2) {
        return true;
      // If it1 > it2 : b1 > b2
      } else if (*it1 > *it2) {
        return false;
      }
      // Otherwise, they are equal, try the next element
    }

    // If they are equivalent but b1 is longer b1 is less than it b2
    if (it1 != en1) {
      return true;
    }

    return false;
  }
};
//}}}

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
  DUG::ControlFlowGraph computeSSA(const DUG::ControlFlowGraph &cfg);

  // Computes partitons based on the conservative address-taken info, the
  //   partitions are based on "access-equivalence"
  // NOTE: ObjectMap is required to convert DUG::ObjID to llvm::Value as
  //   Andersens works with llvm::Value's
  bool computePartitions(DUG &, const Andersens &, const ObjectMap &omap);

  // Computes the SSA form of each partition
  bool addPartitionsToDUG(DUG &, const DUG::ControlFlowGraph &cfg);

  // Solves the remaining graph, providing full flow-sensitive inclusion-based
  // points-to analysis
  bool solve(DUG &) { return false; }
};

#endif  // INCLUDE_SPECSFS_H_
