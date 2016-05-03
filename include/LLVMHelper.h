/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LLVMHELPER_H_
#define INCLUDE_LLVMHELPER_H_

#include "include/Debug.h"
#include "include/ObjectMap.h"

#include "llvm/BasicBlock.h"
#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Function.h"
#include "llvm/GlobalVariable.h"
#include "llvm/Instructions.h"
#include "llvm/Module.h"
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/Debug.h"

class LLVMHelper {
 public:
  // No constructor -- static only
  LLVMHelper() = delete;

  static const llvm::Function *getFcnFromCall(const llvm::CallInst *ci) {
    llvm::ImmutableCallSite cs(ci);
    return getFcnFromCall(ci);
  }

  static const llvm::Function *getFcnFromCall(llvm::ImmutableCallSite &cs) {
    const llvm::Function *fcn = cs.getCalledFunction();

    if (fcn == nullptr) {
      auto callee = cs.getCalledValue();

      if (!llvm::isa<llvm::InlineAsm>(callee)) {
        auto ce = dyn_cast<llvm::ConstantExpr>(callee);

        if (ce) {
          if (ce->getOpcode() == llvm::Instruction::BitCast) {
            fcn = dyn_cast<llvm::Function>(ce->getOperand(0));
          }
        }
      }
    }

    return fcn;
  }

  static llvm::Constant *calcTypeOffset(llvm::Module &m, llvm::Type *type,
      llvm::Value *) {
    bool is_array = false;
    int64_t at_size = 1;

    auto i64_type = llvm::IntegerType::get(m.getContext(), 64);

    while (auto at = dyn_cast<llvm::ArrayType>(type)) {
      at_size *= at->getNumElements();
      type = at->getContainedType(0);
      is_array = true;
    }

    auto type_ptr_type = llvm::PointerType::get(type, 0);
    // Get the size with a getelementpointer operation on null...
    //   psize = GEP (type)* NULL, 1
    //   size = ptrtoint (type)* psize to i32
    // TODO(ddevec): I don't need to do this if I get constant values...
    auto ce_null = llvm::ConstantPointerNull::get(type_ptr_type);
    std::vector<llvm::Constant *> gep_ce_indicies =
        { llvm::ConstantInt::get(i64_type, 1) };
    auto gep_ce = llvm::ConstantExpr::getGetElementPtr(ce_null,
        gep_ce_indicies);
        
    auto ce_int_offs = llvm::ConstantExpr::getCast(llvm::Instruction::PtrToInt,
        gep_ce, i64_type);

    if (is_array) {
      ce_int_offs = llvm::ConstantExpr::getMul(ce_int_offs,
          llvm::ConstantInt::get(i64_type, at_size));
    }

    return ce_int_offs;
  }

  static int32_t gepIsArrayAccess(const llvm::User &gep) {
    // This loop is essentially to handle the nested nature of
    //   GEP instructions
    // It basically says, For the outer-layer of the struct
    for (auto gi = llvm::gep_type_begin(gep),
          en = llvm::gep_type_end(gep);
        gi != en; ++gi) {
      auto type = *gi;
      auto struct_type = dyn_cast<llvm::StructType>(type);
      if (struct_type == nullptr) {
        continue;
      }
      return false;
    }

    return true;
  }

  static int32_t getGEPOffs(ObjectMap &omap, const llvm::User &gep) {
    int32_t offs = 0;

    // This loop is essentially to handle the nested nature of
    //   GEP instructions
    // It basically says, For the outer-layer of the struct
    for (auto gi = llvm::gep_type_begin(gep),
          en = llvm::gep_type_end(gep);
        gi != en; ++gi) {
      auto type = *gi;
      auto struct_type = dyn_cast<llvm::StructType>(type);
      // If it isn't a struct field, don't add subfield offsets
      if (struct_type == nullptr) {
        continue;
      }

      auto &si = omap.getStructInfo(cast<llvm::StructType>(type));

      auto operand = gi.getOperand();

      // Get the offset from this const value
      auto cons_op = dyn_cast<llvm::ConstantInt>(operand);
      assert(cons_op);
      uint32_t idx = cons_op ? cons_op->getZExtValue() : 0;

      // Add the translated offset
      offs += si.getFieldOffset(idx);
    }

    return offs;
  }

  static llvm::Type *getLowestType(llvm::Type *type) {
    auto ret = type;
    bool done = false;
    // Strip away any array or contined struct types, to get down to the lowest
    //   basic type
    while (!done) {
      done = true;

      while (auto at = dyn_cast<llvm::ArrayType>(ret)) {
        ret = at->getContainedType(0);
        done = false;
      }

      if (auto ptype = dyn_cast<llvm::PointerType>(ret)) {
        auto rret = ptype->getContainedType(0);
        if (auto at = dyn_cast<llvm::ArrayType>(rret)) {
          ret = llvm::PointerType::get(at->getContainedType(0), 0);
          done = false;
        }

        if (auto st = dyn_cast<llvm::StructType>(rret)) {
          ret = llvm::PointerType::get(*st->element_begin(), 0);
          done = false;
        }
      }
    }

    auto pt = cast<llvm::PointerType>(ret);
    ret = pt->getContainedType(0);

    return ret;
  }

  /*
  static bool isStructGep(llvm::GetElementPtrInst *) {
  }
  */
};

#endif  // INCLUDE_LLVMHELPER_H_
