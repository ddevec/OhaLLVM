/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LIB_CALLCONTEXTPASS_H_
#define INCLUDE_LIB_CALLCONTEXTPASS_H_

#include <unordered_map>
#include <vector>

#include "include/util.h"
#include "include/DUG.h"
#include "include/ObjectMap.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"
#include "include/lib/CsCFG.h"

#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

class CallContextLoader : public llvm::ModulePass {
 public:
  static char ID;
  CallContextLoader();

  virtual bool runOnModule(llvm::Module &m);

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  const char *getPassName() const override {
    return "CallContextLoader";
  }

 private:
  // Get all callsites containing a (non-strict) partial stack
  // Keep sorted, to do prefix lookup
  std::vector<std::vector<CsCFG::Id>> callsites_;

  // Also keep map, to do by-id lookup:
  std::unordered_multimap<CsCFG::Id, std::vector<CsCFG::Id> *> index_;
};

#endif  // INCLUDE_LIB_CALLCONTEXTPASS_H_
