/*
 * Copyright (C) 2016 David Devecsery
 */

#include "include/lib/ExitInst.h"

#include <string>
#include <vector>

#include "include/LLVMHelper.h"


static const std::string InitInstName = "__SignalHandlers_init";

static const std::string SigactionInstName = "__SignalHandlers_sigaction_shim";
static const std::string ExitInstName = "__SignalHandlers_exit_shim";

void ExitInst::setupTypes() {
  int32Type_ = llvm::IntegerType::get(m_.getContext(), 32);
  voidType_ = llvm::Type::getVoidTy(m_.getContext());
  auto sigaction_type = m_.getTypeByName("struct.sigaction");
  if (sigaction_type != nullptr) {
    sigactionPtrType_ =
      llvm::PointerType::get(sigaction_type, 0);
  }
}

llvm::Function *ExitInst::getInitFcn() {
  if (initFcn_ == nullptr) {
    std::vector<llvm::Type *> arg_fcn_args = { };
    auto arg_fcn_type = llvm::FunctionType::get(
        voidType_,
        arg_fcn_args,
        false);
    auto arg_fcn_ptr = llvm::PointerType::get(arg_fcn_type, 0);

    std::vector<llvm::Type *> init_args = { arg_fcn_ptr };
    auto fcn_type = llvm::FunctionType::get(
        voidType_,
        init_args,
        false);
    initFcn_ = llvm::Function::Create(fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        InitInstName, &m_);
  }

  return initFcn_;
}

llvm::Function *ExitInst::getExitFcn() {
  if (shimExit_ == nullptr) {
    std::vector<llvm::Type *> init_args = { int32Type_ };
    auto fcn_type = llvm::FunctionType::get(
        voidType_,
        init_args,
        false);
    shimExit_ = llvm::Function::Create(fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        ExitInstName, &m_);
  }

  return shimExit_;
}

llvm::Function *ExitInst::getSigactionFcn() {
  if (shimSigaction_ == nullptr) {
    std::vector<llvm::Type *> init_args = { int32Type_,
      sigactionPtrType_, sigactionPtrType_ };
    auto fcn_type = llvm::FunctionType::get(
        int32Type_,
        init_args,
        false);
    shimSigaction_ = llvm::Function::Create(fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        SigactionInstName, &m_);
  }

  return shimSigaction_;
}

ExitInst::ExitInst(llvm::Module &m,
    llvm::Function *call_on_exit) : m_(m) {
  setupTypes();

  // Okay, we add a setup here
  // Get the main function
  LLVMHelper::callAtEntry(m, getInitFcn(), { call_on_exit });

  // Handle the "exit normally" cases
  LLVMHelper::callAtExit(m, call_on_exit);
}

// Shim all sigaction functions
bool ExitInst::addShims() {
  // For each call inst
  std::vector<llvm::Instruction *> sigaction_replace;
  std::vector<llvm::Instruction *> exit_replace;
  for (auto &fcn : m_) {
    for (auto &bb : fcn) {
      for (auto &inst : bb) {
        if (auto ci = dyn_cast<llvm::CallInst>(&inst)) {
          auto called_fcn = LLVMHelper::getFcnFromCall(ci);

          // Need to replace
          if (called_fcn != nullptr) {
            if (called_fcn->getName() == "sigaction") {
              sigaction_replace.push_back(ci);
            } else if (called_fcn->getName() == "_exit" ||
                       called_fcn->getName() == "_Exit") {
              exit_replace.push_back(ci);
            }
          }
        }
      }
    }
  }

  bool ret = false;

  for (auto &inst : sigaction_replace) {
    auto ci = cast<llvm::CallInst>(inst);
    llvm::CallSite cs(ci);
    // Put a new call in before this call
    // Then delete this call
    auto shim = getSigactionFcn();

    std::vector<llvm::Value *> args(cs.arg_begin(), cs.arg_end());

    llvm::dbgs() << "have args:\n";
    for (auto arg : args) {
      llvm::dbgs() << "  " << ValPrinter(arg) << "\n";
    }

    llvm::dbgs() << "have fcn: " << *shim << "\n";

    auto new_call = llvm::CallInst::Create(shim, args, "", ci);

    ci->replaceAllUsesWith(new_call);
    ci->eraseFromParent();
    ret = true;
  }

  for (auto &inst : exit_replace) {
    auto ci = cast<llvm::CallInst>(inst);
    llvm::CallSite cs(ci);
    // Put a new call in before this call
    // Then delete this call
    auto shim = getExitFcn();

    std::vector<llvm::Value *> args(cs.arg_begin(), cs.arg_end());

    llvm::CallInst::Create(shim, args, "", ci);

    ci->eraseFromParent();
    ret = true;
  }

  return ret;
}

