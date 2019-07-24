/*
 * Copyright (C) 2016 David Devecsery
 */

#ifndef INCLUDE_LIB_EXITINST_H_
#define INCLUDE_LIB_EXITINST_H_

#include "include/Debug.h"

#include "llvm/Pass.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/Debug.h"

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
