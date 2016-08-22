/*
 * Copyright (C) 2016 David Devecsery
 */

#include "llvm/Pass.h"

#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"
#include "include/lib/CallContextPass.h"

class ProfileDisabler : public llvm::ModulePass {
 public:
  static char ID;
  ProfileDisabler();

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;
  bool runOnModule(llvm::Module &m) override;
};


char ProfileDisabler::ID = 0;
ProfileDisabler::ProfileDisabler() : llvm::ModulePass(ID) { }

void ProfileDisabler::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  usage.addRequired<UnusedFunctions>();
  usage.addRequired<CallContextLoader>();
  usage.addRequired<IndirFunctionInfo>();
  // usage.setPreservesAll();
}

bool ProfileDisabler::runOnModule(llvm::Module &) {
  auto &call_info = getAnalysis<CallContextLoader>();
  auto &used_info = getAnalysis<UnusedFunctions>();
  auto &indir_info = getAnalysis<IndirFunctionInfo>();

  call_info.disable();
  used_info.disable();
  indir_info.disable();

  return false;
}

static llvm::RegisterPass<ProfileDisabler>
X("profile-disable", "ProfileDisabler", false, false);

class ProfileEnabler : public llvm::ModulePass {
 public:
  static char ID;
  ProfileEnabler();

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;
  bool runOnModule(llvm::Module &m) override;
};


char ProfileEnabler::ID = 0;
ProfileEnabler::ProfileEnabler() : llvm::ModulePass(ID) { }

void ProfileEnabler::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  usage.addRequired<UnusedFunctions>();
  usage.addRequired<CallContextLoader>();
  usage.addRequired<IndirFunctionInfo>();
  // usage.setPreservesAll();
}

bool ProfileEnabler::runOnModule(llvm::Module &) {
  auto &call_info = getAnalysis<CallContextLoader>();
  auto &used_info = getAnalysis<UnusedFunctions>();
  auto &indir_info = getAnalysis<IndirFunctionInfo>();

  call_info.enable();
  used_info.enable();
  indir_info.enable();

  return false;
}

static llvm::RegisterPass<ProfileEnabler>
Y("profile-enable", "ProfileEnabler", false, false);
