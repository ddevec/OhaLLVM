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
        // From coreutils src
        callee->getName() != "xrealloc" &&
        callee->getName() != "xmalloc" &&
        callee->getName() != "xnmalloc" &&
        // End coreutils src
        // From zlib src
        callee->getName() != "zcalloc" &&
        // End zlib src
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
    // Arg pos 0
    if (callee->getName() == "malloc" ||
        callee->getName() == "xmalloc" ||
        callee->getName() == "valloc") {
      return ci->getArgOperand(0);
    }

    // Arg pos 1
    if (callee->getName() == "memalign" ||
        callee->getName() == "xrealloc" ||
        callee->getName() == "realloc") {
      return ci->getArgOperand(1);
    }

    // Arg (pos 0 * pos 1)
    if (callee->getName() == "calloc") {
      auto a0 = ci->getArgOperand(0);
      auto a1 = ci->getArgOperand(1);

      return llvm::BinaryOperator::Create(
          llvm::Instruction::Mul, a0, a1, "", ci);
    }

    // fopen...
    if (callee->getName() == "fopen" ||
        callee->getName() == "fdopen") {
      // Allocate a new file struct... calc size of file struct...
      auto file_type = m.getTypeByName("_IO_FILE");
      return LLVMHelper::calcTypeOffset(m, file_type, ci);
    }

    llvm::dbgs() << "callee->getName(): " << callee->getName() << "\n";
    llvm_unreachable("Unknown malloc size?");
    return nullptr;
  }

  static bool fcnIsFree(const llvm::Function *callee) {
    if (callee->getName() != "free" &&
        callee->getName() != "fclose" &&
        callee->getName() != "realloc" &&
        // From coreutils src
        callee->getName() != "xrealloc" &&
        // End coreutils src
        // From zlib src
        callee->getName() != "zcfree") {
      return false;
    }

    return true;
  }

  static llvm::Value *getFreeArg(llvm::Module &m,
      llvm::CallInst *ci, const llvm::Function *callee) {
    // Arg pos 0
    if (callee->getName() == "free" ||
        callee->getName() == "realloc" ||
        callee->getName() == "xrealloc") {
      return ci->getArgOperand(0);
    }

    // Need to bitcast to i8*...
    if (callee->getName() == "fclose") {
      auto i8_ptr_type = llvm::PointerType::get(
          llvm::IntegerType::get(m.getContext(), 8), 0);
      auto arg = ci->getArgOperand(0);
      return new llvm::BitCastInst(arg, i8_ptr_type,
          "", ci);
    }

    // Arg pos 1
    if (callee->getName() == "zcfree") {
      return ci->getArgOperand(1);
    }

    llvm_unreachable("Unknown free pos?");
    return nullptr;
  }



};

#endif  // INCLUDE_ALLOCINFO_H_

