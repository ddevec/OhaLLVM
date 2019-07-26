/*
 * Copyright (C) 2019 David Devecsery
 */

#ifndef INCLUDE_MODULEAARESULTS_H_
#define INCLUDE_MODULEAARESULTS_H_

#include "include/SpecAnders.h"
#include "include/SpecAndersCS.h"

class ModuleAAResults : public llvm::ModulePass {
 public:
  static char ID;
  ModuleAAResults();

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;
  virtual bool runOnModule(llvm::Module &M);

  llvm::StringRef getPassName() const override {
    return "ModuleAAResults";
  }

  llvm::AliasResult alias(const llvm::MemoryLocation &LocA,
      const llvm::MemoryLocation &LocB);

 private:
  SpecAndersWrapperPass *anders_;
  SpecAndersCS *andersCS_;
};

#endif  // INCLUDE_MODULEAARESULTS_H_
