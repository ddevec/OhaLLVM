/*
 * Copyright (C) 2016 David Devecsery
 */

#ifndef INCLUDE_LIB_EXITINST_H_
#define INCLUDE_LIB_EXITINST_H_

#include "include/Debug.h"

#include "llvm/BasicBlock.h"
#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Function.h"
#include "llvm/GlobalVariable.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Module.h"
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/InstIterator.h"

class ExitInst {
 public:
  ExitInst(llvm::Module &m, llvm::Function *call_on_exit);

  // Replaces all calls to signal/sigaction/_exit/_Exit with our shims
  bool addShims();

 private:
  void setupTypes();

  llvm::Function *getExitFcn();
  llvm::Function *getInitFcn();
  llvm::Function *getSigactionFcn();

  llvm::Module &m_;

  llvm::Type *int32Type_;
  llvm::Type *sigactionPtrType_;
  llvm::Type *voidType_;

  llvm::Function *initFcn_ = nullptr;
  llvm::Function *shimSigaction_ = nullptr;
  llvm::Function *shimExit_ = nullptr;
};

#endif  // INCLUDE_LIB_EXITINST_H_
