/*
 * Copyright (C) 2015 David Devecsery
 *
 */

#ifndef INCLUDE_ALLOCINFO_H_
#define INCLUDE_ALLOCINFO_H_

#include <algorithm>
#include <string>

#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Instructions.h"
#include "llvm/Module.h"
#include "llvm/Pass.h"

#include "include/LLVMHelper.h"

class AllocInfo {
 public:
  static bool fcnIsMalloc(const llvm::Function *callee) {
    if (callee->getName() != "malloc" &&
        callee->getName() != "calloc" &&
        callee->getName() != "valloc" &&
        callee->getName() != "realloc" &&
        callee->getName() != "memalign" &&
        callee->getName() != "fopen" &&
        callee->getName() != "popen" &&
        callee->getName() != "fdopen" &&
        callee->getName() != "fopen64" &&
        callee->getName() != "_Znwj" &&  // operator new(unsigned int)
        callee->getName() != "_Znwm" &&  // operator new(unsigned long)
        callee->getName() != "_Znaj" &&  // operator new[](unsigned int)
        callee->getName() != "_Znam") {  // operator new[](unsigned long)
      return false;
    }

    return true;
  }

  // Returns the size of the malloc
  // NOTE: this may insert instructions to calculate the that value.  All
  //   instructions will be inserted directly before callee
  static llvm::Value *getMallocSizeArg(llvm::Module &m,
      llvm::CallInst *ci, const llvm::Function *callee) {
    bool do_mult = false;
    llvm::Value *ret = nullptr;
    llvm::Instruction *before = nullptr;
    // Arg pos 0
    if (callee->getName() == "malloc" ||
        callee->getName() == "valloc") {
      ret = ci->getArgOperand(0);
      before = ci;
      do_mult = true;
    }

    // Arg pos 1
    if (callee->getName() == "memalign" ||
        callee->getName() == "realloc") {
      ret = ci->getArgOperand(1);
      before = ci;
      do_mult = true;
    }

    // Arg (pos 0 * pos 1)
    if (callee->getName() == "calloc") {
      auto a0 = ci->getArgOperand(0);
      auto a1 = ci->getArgOperand(1);

      ret = llvm::BinaryOperator::Create(
          llvm::Instruction::Mul, a0, a1, "", ci);
      before = cast<llvm::Instruction>(ret);
      do_mult = true;
    }

    // fopen...
    if (callee->getName() == "fopen" ||
        callee->getName() == "fopen64" ||
        callee->getName() == "popen" ||
        callee->getName() == "fdopen") {
      // Allocate a new file struct... calc size of file struct...
      auto file_type = m.getTypeByName("struct._IO_FILE");
      ret = LLVMHelper::calcTypeOffset(m, file_type, ci);
      do_mult = false;
    }

    if (do_mult) {
      auto i64_type = llvm::IntegerType::get(m.getContext(), 64);
      ret = llvm::BinaryOperator::Create(
          llvm::Instruction::Mul, ret, 
          llvm::ConstantInt::get(i64_type, 8),
          "", before);
    }

    llvm::dbgs() << "callee->getName(): " << callee->getName() << "\n";
    assert(ret != nullptr);
    return ret;
  }

  static bool fcnIsFree(const llvm::Function *callee) {
    if (callee->getName() != "free" &&
        callee->getName() != "fclose" &&
        callee->getName() != "realloc" &&
        callee->getName() != "pclose") {
      return false;
    }

    return true;
  }

  static llvm::Value *getFreeArg(llvm::Module &m,
      llvm::CallInst *ci, const llvm::Function *callee) {
    // Arg pos 0
    if (callee->getName() == "free" ||
        callee->getName() == "realloc") {
      return ci->getArgOperand(0);
    }

    // Need to bitcast to i8*...
    if (callee->getName() == "fclose" ||
        callee->getName() == "pclose") {
      auto i8_ptr_type = llvm::PointerType::get(
          llvm::IntegerType::get(m.getContext(), 8), 0);
      auto arg = ci->getArgOperand(0);
      return new llvm::BitCastInst(arg, i8_ptr_type,
          "", ci);
    }

    llvm_unreachable("Unknown free pos?");
    return nullptr;
  }
};

#endif  // INCLUDE_ALLOCINFO_H_

