/*
 * Copyright (C) 2015 David Devecsery
 *
 */

#ifndef INCLUDE_ALLOCINFO_H_
#define INCLUDE_ALLOCINFO_H_

#if 0
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
        callee->getName() != "strdup" && // Does malloc of return value...
        callee->getName() != "fopen" &&
        callee->getName() != "tmpfile" &&
        callee->getName() != "popen" &&
        callee->getName() != "fdopen" &&
        callee->getName() != "fopen64" &&
        // callee->getName() != "opendir" &&
        // callee->getName() != "getenv" &&
        callee->getName() != "getaddrinfo" &&
        callee->getName() != "Perl_safesysmalloc" &&
        callee->getName() != "Perl_safesysrealloc" &&
        callee->getName() != "_Znwj" &&  // operator new(unsigned int)
        callee->getName() != "_Znwm" &&  // operator new(unsigned long)
        callee->getName() != "_Znaj" &&  // operator new[](unsigned int)
        callee->getName() != "_Znam") {  // operator new[](unsigned long)
      return false;
    }

    return true;
  }

  static bool mallocNotStruct(const llvm::Function *callee) {
    // Allocates strings, not structures
    if (callee->getName() == "strdup") {
      return true;
    }

    return false;
  }

  // Returns the size of the malloc
  // NOTE: this may insert instructions to calculate the that value.  All
  //   instructions will be inserted directly before callee
  static std::pair<llvm::Value *, llvm::Instruction *> getMallocSizeArg(llvm::Module &m,
      llvm::CallInst *ci, const llvm::Function *callee) {
    auto i64_type = llvm::IntegerType::get(m.getContext(), 64);
    bool do_mult = false;
    llvm::Value *ret = nullptr;
    llvm::Instruction *before = nullptr;

    llvm::Instruction *after = ci;
    // Arg pos 0
    if (callee->getName() == "malloc" ||
        callee->getName() == "Perl_safesysmalloc" ||
        callee->getName() == "valloc") {
      ret = ci->getArgOperand(0);
      before = ci;
      do_mult = true;
    }

    // Arg pos 1
    if (callee->getName() == "memalign" ||
        callee->getName() == "Perl_safesysrealloc" ||
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
      before = cast<llvm::Instruction>(ci);
      do_mult = true;
    }

    // Freaking strdup...
    if (callee->getName() == "strdup") {
      // Now call strlen...
      auto strlen_fcn = m.getFunction("strlen");
      // I may have to create an external linkage for this in some instances...
      //   ugh
      assert(strlen_fcn != nullptr);


      // This means we add a check for nullptr
      // Then if not nullptr we do math
      // We phi together after math
      // Finally, we return the info needed for the alloc function

      // UGH, need to consider nullptr...
      // If ci is nullptr, don't do the following, otherwise, do it
      // First, split the BB after the CI
      auto bb_prev = ci->getParent();
      auto bb_it = llvm::BasicBlock::iterator(ci);
      // Advance to after CI
      ++bb_it;

      // Split
      auto bb_succ = bb_prev->splitBasicBlock(bb_it);
      // Then delete the terminator in pred BB
      auto old_term = bb_prev->getTerminator();
      old_term->eraseFromParent();

      auto i8_ptr_type = llvm::PointerType::get(
          llvm::IntegerType::get(m.getContext(), 8), 0);
      // Add a icmp
      auto icmp = new llvm::ICmpInst(*bb_prev, llvm::CmpInst::Predicate::ICMP_EQ,
          ci, llvm::ConstantPointerNull::get(i8_ptr_type));
      
      auto bb_strlen = llvm::BasicBlock::Create(m.getContext(), "",
          bb_prev->getParent(), bb_succ);

      // Do strlen maths here
      // Phi together result from strlen is succ bb

      // Add branch to pred BB, do strlen iff ci not null
      // Add a iff not null branch
      llvm::BranchInst::Create(bb_succ, bb_strlen, icmp, bb_prev);

      std::vector<llvm::Value *> args;
      args.push_back(ci);

      auto strlen_ret = llvm::CallInst::Create(strlen_fcn, ci, "", bb_strlen);

      // Add 1 for nullptr terminated strings
      auto inc = llvm::BinaryOperator::Create(
          llvm::Instruction::Add,
          strlen_ret, llvm::ConstantInt::get(i64_type, 1),
          "", bb_strlen);

      // Now multiply by 8... b/c I made a mistake early and now I stick w/ it
      after = llvm::BinaryOperator::Create(
          llvm::Instruction::Mul, inc, 
          llvm::ConstantInt::get(i64_type, 8),
          "", bb_strlen);

      // Create terminator
      llvm::BranchInst::Create(bb_succ, bb_strlen);

      // Now, add a phi to bb_succ
      auto phi = llvm::PHINode::Create(i64_type, 2, "", std::begin(*bb_succ));
      phi->addIncoming(after, bb_strlen);
      phi->addIncoming(llvm::ConstantInt::get(i64_type, 0), bb_prev);

      ret = after;
      do_mult = false;
    }

    // fopen...
    if (callee->getName() == "fopen" ||
        callee->getName() == "tmpfile" ||
        callee->getName() == "fopen64" ||
        callee->getName() == "popen" ||
        callee->getName() == "fdopen") {
      // Allocate a new file struct... calc size of file struct...
      auto file_type = m.getTypeByName("struct._IO_FILE");
      ret = LLVMHelper::calcTypeOffset(m, file_type, ci);
      do_mult = false;
    }

    // Directories are opaque types... so... we'll ignore this?
    // diropen...
    if (callee->getName() == "opendir") {
      // Allocate a new file struct... calc size of file struct...
      auto file_type = m.getTypeByName("struct.__dirstream");
      ret = LLVMHelper::calcTypeOffset(m, file_type, ci);
      do_mult = false;
    }

    if (do_mult) {
      ret = llvm::BinaryOperator::Create(
          llvm::Instruction::Mul, ret, 
          llvm::ConstantInt::get(i64_type, 8),
          "", before);
    }

    if (ret == nullptr) {
      llvm::dbgs() << "getMallocSizeArg() has nullptr ret for: " <<
        callee->getName() << "\n";
    }
    assert(ret != nullptr);
    return std::make_pair(ret, after);
  }

  static bool fcnIsFree(const llvm::Function *callee) {
    if (callee->getName() != "free" &&
        callee->getName() != "fclose" &&
        callee->getName() != "freeaddrinfo" &&
        callee->getName() != "realloc" &&
        callee->getName() != "Perl_safesysrealloc" &&
        // callee->getName() != "closedir" &&
        callee->getName() != "pclose") {
      return false;
    }

    return true;
  }

  static llvm::Value *getFreeArg(llvm::Module &m,
      llvm::CallInst *ci, const llvm::Function *callee,
      bool allow_cast = true) {
    // Arg pos 0
    if (callee->getName() == "free" ||
        callee->getName() == "realloc" ||
        callee->getName() == "freeaddrinfo" ||
        callee->getName() == "Perl_safesysrealloc") {
      return ci->getArgOperand(0);
    }

    // Need to bitcast to i8*...
    if (callee->getName() == "fclose" ||
        callee->getName() == "pclose" ||
        callee->getName() == "closedir") {
      auto i8_ptr_type = llvm::PointerType::get(
          llvm::IntegerType::get(m.getContext(), 8), 0);
      auto arg = ci->getArgOperand(0);
      if (allow_cast) {
        return new llvm::BitCastInst(arg, i8_ptr_type,
            "", ci);
      } else {
        return arg;
      }
    }

    llvm_unreachable("Unknown free pos?");
    return nullptr;
  }
};
#endif

#endif  // INCLUDE_ALLOCINFO_H_

