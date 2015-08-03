
#include "include/SpecSFS.h"
#include "include/DUG.h"

bool SpecSFS::Solve(DUG &dug) {
  // Need top-level ptssets
  // Need a worklist
  // Add allocs to ptset
  
  // Add allocs to worklist
  
  // While we have work
  while (!worklist.empty()) {
    // Get the next node
    auto &nd = worklist.pop();

    // Switch type, and process
  }

  return false;
}

void processAlloc(DUG::AllocNode &alloc) {
  // Update the top level variables for this alloc
  // Add all top level variables updated to worklist
}

void processCopy(DUG::CopyNode &cp) {
  // Update the top level variables for this copy
  // Add all updated successors to worklist
}

void processLoad(DUG::LoadNode &ld) {
  // add a ptsto from src to the values contained in our partition set from the
  //    top level varaible dest
  // Add all successors to worklist
}

void processStore(DUG::StoreNode &st) {
  // if strong && concrete
  //   clear all outgoing edges from src from our addr_taken set, 
  //     add edges from top(src) to top(dest)
  // otherwise (not strong):
  //   Add edges from top(src) to top(dest) to our addr_taken set
  // For each partition successor:
  //   add our OUT set to their IN set
  //   Add them to worklist (if their set changed)
}

void processPHI(DUG::PHINode &phi) {
  // For all successors:
  //   IN(succ) U IN(us)
  // add them to worklist (if changed)
}

