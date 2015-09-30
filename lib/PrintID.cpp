/*
 * Copyright (C) 2015 David Devecsery
 */


#include <execinfo.h>

#include <algorithm>
#include <cstdio>
#include <string>
#include <utility>
#include <vector>

#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Analysis/AliasAnalysis.h"

#include "include/SpecSFS.h"

#include "include/Debug.h"
#include "include/ObjectMap.h"
#include "include/lib/UnusedFunctions.h"

using std::swap;


static llvm::cl::opt<std::string>
  PrintIDFilename("id-file", llvm::cl::init("id.out"),
      llvm::cl::value_desc("filename"),
      llvm::cl::desc("Id file loaded by -SpecSFS-ids"));

class PrintID : public SpecSFS {
 public:
    PrintID();

    bool runOnModule(llvm::Module &M);

    std::string filename_;
    static char ID;
};

char PrintID::ID = 0;
// Constructor
PrintID::PrintID() : SpecSFS(ID), filename_(PrintIDFilename) { }

static llvm::RegisterPass<PrintID>
  print_register("print-ids",
      "Prints ids from id.out for SpecSFS", false, false);

// runOnModule, the primary pass
bool PrintID::runOnModule(llvm::Module &M) {
  // Set up our alias analysis
  // -- This is required for the llvm AliasAnalysis interface
  InitializeAliasAnalysis(this);

  // Clear the def-use graph
  // It should already be cleared, but I'm paranoid
  ConstraintGraph cg;
  CFG cfg;
  ObjectMap &omap = omap_;

  if (identifyObjects(omap, M)) {
    abort();
  }

  const UnusedFunctions &unused_fcns =
      getAnalysis<UnusedFunctions>();

  if (createConstraints(cg, cfg, omap, M, unused_fcns)) {
    abort();
  }

  // Also add indirect info... this means we have to wait for Andersen's
  Andersens aux;
  // Get AUX info, in this instance we choose Andersens
  if (aux.runOnModule(M)) {
    // Andersens had better not change M!
    abort();
  }

  // Now, fill in the indirect function calls
  const auto &dyn_indir_info = getAnalysis<IndirFunctionInfo>();
  if (addIndirectCalls(cg, cfg, aux, &dyn_indir_info, omap)) {
    abort();
  }


  llvm::dbgs() << "Here with filename: " << filename_ << "\n";

  // Okay, open the filename:
  FILE *f = fopen(filename_.c_str(), "r");
  if (f == nullptr) {
    perror("fopen");
    abort();
  }

  llvm::dbgs() << "have file: " << f << "\n";

  llvm::dbgs() << "OUTPUT:\n";
  while (!feof(f)) {
    int32_t id;

    int32_t rc = fscanf(f, "%d\n", &id);
    if (rc == 1) {
      llvm::dbgs() << id << ":" << ValPrint(ObjectMap::ObjID(id)) << "\n";
    }
  }

  // Now read out objects to id and id them
  return false;
}

