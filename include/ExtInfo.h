/*
 * Copyright (C) 2016 David Devecsery
 *
 */

#ifndef INCLUDE_EXTINFO_H_
#define INCLUDE_EXTINFO_H_

#include <algorithm>
#include <tuple>
#include <string>

#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Instructions.h"
#include "llvm/Module.h"
#include "llvm/Pass.h"

#include "include/ObjectMap.h"
#include "include/LLVMHelper.h"

class ExtInfo {
 public:
  static ObjectMap::ObjID
  returnsExtInfo(const llvm::Function *F) {
    // term info stuffs...
    if (F->getName() == "tigetstr" ||
        F->getName() == "tparm") {
      // Set the output to be terminfo static data
      return ObjectMap::TermInfoObject;
    }

    // c stdlib returning fcns
    if (F->getName() == "strerror" ||
        F->getName() == "gai_strerror" ||
        F->getName() == "gmtime" ||
        F->getName() == "readdir") {
      return ObjectMap::CLibObject;
    }

    // Locale functions
    if (F->getName() == "getlocale" ||
        F->getName() == "setlocale" ||
        F->getName() == "nl_langinfo") {
      return ObjectMap::LocaleObject;
    }

    // Errno
    if (F->getName() == "__errno_location") {
      return ObjectMap::ErrnoObject;
    }

    if (F->getName() == "getenv") {
      return ObjectMap::EnvObject;
    }

    // FIXME: Instead treat it as an alloc, unclear if this is best
    /*
    // getenv -- This is currently linked to argv...
    if (F->getName() == "getenv") {
      cg.add(ConstraintType::AddressOf,
        omap.getValue(CS.getInstruction()),
        ObjectMap::ArgvValueObject);
      return true;
    }
    */
    if (F->getName() == "opendir") {
      return ObjectMap::DirObject;
    }

    // CType Functions
    if (F->getName() == "__ctype_b_loc") {
      return ObjectMap::CTypeObject;
    }

    return ObjectMap::NullValue;
  }

  // tuple<start of data, data size, insert_after>
  static std::tuple<llvm::Value *, llvm::Value *, llvm::Instruction *>
  getExtInfo(llvm::Module &m,
      llvm::Instruction *ci,
      llvm::Instruction *insert_after,
      const llvm::Function *F) {

    auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
    auto i64_type = llvm::IntegerType::get(m.getContext(), 64);
    // term info stuffs...
    if (F->getName() == "tigetstr" ||
        F->getName() == "tparm") {
      // Set the output to be terminfo static data
      llvm::dbgs() << "WARNING: tigetstr/tparm size guessed\n";
      return std::make_tuple(ci, llvm::ConstantInt::get(i64_type, 8*8), ci);
    }

    // c stdlib returning fcns
    if (F->getName() == "strerror" ||
        F->getName() == "gai_strerror" ||
        F->getName() == "gmtime" ||
        F->getName() == "readdir") {
      llvm::dbgs() << "WARNING: strerror/gmtime/readdir size guessed\n";
      return std::make_tuple(ci, llvm::ConstantInt::get(i64_type, 8*8), ci);
    }

    // Locale functions
    if (F->getName() == "getlocale" ||
        F->getName() == "setlocale" ||
        F->getName() == "nl_langinfo") {
      llvm::dbgs() << "WARNING: set/getlocale/nl_langinfo size guessed\n";
      return std::make_tuple(ci, llvm::ConstantInt::get(i64_type, 8*8), ci);
    }

    // Errno
    if (F->getName() == "__errno_location") {
      return std::make_tuple(ci, llvm::ConstantInt::get(i64_type, 4*8), ci);
    }

    if (F->getName() == "getenv") {
      auto strlen_fcn = m.getFunction("strlen");
      assert(strlen_fcn != nullptr);

      auto bb_prev = ci->getParent();
      auto bb_it = llvm::BasicBlock::iterator(ci);
      // Advance to after ci
      ++bb_it;

      // Split
      auto bb_succ = bb_prev->splitBasicBlock(bb_it);
      // THen delete terminator in pred BB
      auto old_term = bb_prev->getTerminator();
      old_term->eraseFromParent();

      auto i8_ptr_type = llvm::PointerType::get(
          llvm::IntegerType::get(m.getContext(), 8), 0);

      auto icmp = new llvm::ICmpInst(*bb_prev, llvm::CmpInst::Predicate::ICMP_EQ,
          ci, llvm::ConstantPointerNull::get(i8_ptr_type));
      auto bb_strlen = llvm::BasicBlock::Create(m.getContext(), "",
          bb_prev->getParent(), bb_succ);

      llvm::BranchInst::Create(bb_succ, bb_strlen, icmp, bb_prev);

      std::vector<llvm::Value *> args;
      args.push_back(ci);

      auto strlen_ret = llvm::CallInst::Create(strlen_fcn, ci, "", bb_strlen);

      auto inc = llvm::BinaryOperator::Create(
          llvm::Instruction::Add,
          strlen_ret, llvm::ConstantInt::get(i64_type, 1),
          "", bb_strlen);

      auto after = llvm::BinaryOperator::Create(
          llvm::Instruction::Mul, inc,
          llvm::ConstantInt::get(i64_type, 8),
          "", bb_strlen);

      llvm::BranchInst::Create(bb_succ, bb_strlen);

      auto phi = llvm::PHINode::Create(i64_type, 2, "", std::begin(*bb_succ));
      phi->addIncoming(after, bb_strlen);
      phi->addIncoming(llvm::ConstantInt::get(i64_type, 0), bb_prev);

      return std::make_tuple(ci, phi, phi);
    }

    if (F->getName() == "opendir") {
      return std::make_tuple(ci, llvm::ConstantInt::get(i64_type, 8*8), ci);
    }

    // CType Functions
    if (F->getName() == "__ctype_b_loc") {
      // subtract 128 from ci (gep for -128)
      std::vector<llvm::Value *> indicies;
      indicies.push_back(llvm::ConstantInt::get(i32_type, -128));
      auto gep = llvm::GetElementPtrInst::Create(ci, indicies);
      gep->insertAfter(insert_after);
      // Return that result
      // Insert the gep after "insert_after"
      // 384 * sizeof(int16_t) * 8(bit/byte)
      return std::make_tuple(gep, llvm::ConstantInt::get(i64_type, 384*2*8), gep);
    }

    llvm_unreachable("Unknown extinfo allocation");
  }
};

#endif  // INCLUDE_ALLOCINFO_H_

