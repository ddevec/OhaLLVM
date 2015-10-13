/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LLVMHELPER_H_
#define INCLUDE_LLVMHELPER_H_

#include "include/Debug.h"

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
    static llvm::Function *getFcnFromCall(llvm::CallInst *ci) {
      llvm::CallSite cs(ci);

      llvm::Function *fcn = cs.getCalledFunction();

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
      std::vector<llvm::Constant *> gep_ce_indicies;
      gep_ce_indicies.push_back(llvm::ConstantInt::get(i64_type, 8));
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
};

#endif  // INCLUDE_LLVMHELPER_H_
