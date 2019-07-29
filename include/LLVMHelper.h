/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LLVMHELPER_H_
#define INCLUDE_LLVMHELPER_H_

#include <unordered_set>

#include "include/Debug.h"
#include "include/ModInfo.h"
#include "include/lib/UnusedFunctions.h"

#include "llvm/Pass.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/Debug.h"

class LLVMHelper {
 public:
  // No constructor -- static only
  LLVMHelper() = delete;

  static bool isValidCall(llvm::ImmutableCallSite &cs) {
    auto cv = cs.getCalledValue();
    if (llvm::isa<llvm::InlineAsm>(cv)) {
      return false;
    }

    auto cf = cs.getCalledFunction();
    if (cf != nullptr && cf->isIntrinsic()) {
      return false;
    }

    return true;
  }

  static const llvm::Function *getFcnFromCall(const llvm::CallInst *ci) {
    llvm::ImmutableCallSite cs(ci);
    return getFcnFromCall(cs);
  }

  template <typename inst_filter>
  static std::vector<const llvm::Instruction *> findAllPreds(
      const llvm::Instruction *start_inst,
      const UnusedFunctions *dyn_info,
      inst_filter include_inst) {
    std::unordered_set<const llvm::BasicBlock *> visited;

    std::vector<const llvm::Instruction *> ret;

    // First iterate all instructions prior to inst
    auto start_bb = start_inst->getParent();

    util::Worklist<const llvm::BasicBlock *> worklist(
        pred_begin(start_bb), pred_end(start_bb));

    // First, find all instructions before [start(bb), start_inst]
    //     NOTE: start_inst is inclusive
    for (auto it = std::begin(*start_bb),
              en = ++llvm::BasicBlock::const_iterator(start_inst);
        it != en;
        ++it) {
      auto &inst = *it;
      if (include_inst(&inst)) {
        ret.push_back(&inst);
      }
    }

    // Now, iterate all basic blocks in the function prior to start_bb
    while (!worklist.empty()) {
      auto bb = worklist.pop();

      // Only consider used bbs
      if (dyn_info && !dyn_info->isUsed(bb)) {
        continue;
      }

      // Only consider unvisited bbs
      auto rc = visited.emplace(bb);
      if (!rc.second) {
        continue;
      }

      // For the start bb only get btwn start_inst and end
      if (bb == start_bb) {
        for (auto it = ++llvm::BasicBlock::const_iterator(start_inst),
                  en = std::end(*bb);
            it != en;
            ++it) {
          auto &inst = *it;
          if (include_inst(&inst)) {
            ret.push_back(&inst);
          }
        }
        // Don't bother to add preds to worklist for start block...
      } else {
        for (auto &inst : *bb) {
          if (include_inst(&inst)) {
            ret.push_back(&inst);
          }
        }

        worklist.push(pred_begin(bb), pred_end(bb));
      }
    }

    return std::move(ret);
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
    auto gep_ce = llvm::ConstantExpr::getGetElementPtr(type, ce_null,
        gep_ce_indicies);
        
    auto ce_int_offs = llvm::ConstantExpr::getCast(llvm::Instruction::PtrToInt,
        gep_ce, i64_type);

    if (is_array) {
      ce_int_offs = llvm::ConstantExpr::getMul(ce_int_offs,
          llvm::ConstantInt::get(i64_type, at_size));
    }

    return ce_int_offs;
  }

  static bool gepIsArrayAccess(const llvm::User &gep) {
    // This loop is essentially to handle the nested nature of
    //   GEP instructions
    // It basically says, For the outer-layer of the struct
    for (auto gi = llvm::gep_type_begin(gep),
          en = llvm::gep_type_end(gep);
        gi != en; ++gi) {
      auto type = gi.getIndexedType();
      auto struct_type = dyn_cast<llvm::StructType>(type);
      if (struct_type == nullptr) {
        continue;
      }
      return false;
    }

    return true;
  }

  static int32_t getGEPOffs(ModInfo &info, const llvm::User &gep) {
    int32_t offs = 0;

    // This loop is essentially to handle the nested nature of
    //   GEP instructions
    // It basically says, For the outer-layer of the struct
    // llvm::dbgs() << "have gep: " << gep << "\n";
    for (auto gi = llvm::gep_type_begin(gep),
          en = llvm::gep_type_end(gep);
        gi != en; ++gi) {
      auto type = gi.getStructTypeOrNull();
      /*
      if (type) {
        llvm::dbgs() << "type: " << *type << "\n";
      } else {
        llvm::dbgs() << "type: (null)\n";
      }
      */
      auto struct_type = type;
      // If it isn't a struct field, don't add subfield offsets
      if (struct_type == nullptr) {
        continue;
      }

      auto &si = info.getStructInfo(struct_type);

      auto operand = gi.getOperand();
      // llvm::dbgs() << "operand: " << *operand << "\n";

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

  static bool callAtExit(llvm::Module &m, llvm::Function *to_call) {
    // Get atexit
    auto at_exit = m.getFunction("atexit");
    if (at_exit == nullptr) {
      // Cast to_call to voidptr...
      auto void_type = llvm::Type::getVoidTy(m.getContext());

      std::vector<llvm::Type *> type_no_args;
      auto void_fcn_type = llvm::FunctionType::get(
          void_type,
          type_no_args,
          false);

      std::vector<llvm::Type *> atexit_args { void_fcn_type->getPointerTo() };
      auto atexit_type = llvm::FunctionType::get(
          void_type,
          atexit_args,
          false);

      at_exit = llvm::Function::Create(
          atexit_type,
          llvm::GlobalValue::ExternalLinkage,
          "atexit", &m);
    }

    std::vector<llvm::Value *> call_args = { to_call };

    auto first_inst =
      m.getFunction("main")->getEntryBlock().getFirstNonPHIOrDbg();
    llvm::CallInst::Create(at_exit, call_args, "", first_inst);

    return true;
  }

  static bool callAtEntry(llvm::Module &m, llvm::Function *to_call,
      std::initializer_list<llvm::Value *> args) {
    // Get atexit
    std::vector<llvm::Value *> call_args = args;

    auto first_inst =
      m.getFunction("main")->getEntryBlock().getFirstNonPHIOrDbg();
    llvm::CallInst::Create(to_call, call_args, "", first_inst);

    return true;
  }

  static llvm::Function *getOrCreateLibFcn(llvm::Module &m,
      const std::string &name,
      llvm::FunctionType *type) {
    auto fcn = m.getFunction(name.c_str());
    if (fcn == nullptr) {
      fcn = llvm::Function::Create(type,
          llvm::GlobalValue::ExternalLinkage,
          name, &m);
    }
    assert(fcn != nullptr);

    return fcn;
  }
      

  /*
  static bool isStructGep(llvm::GetElementPtrInst *) {
  }
  */
};

class ValPrinter {
 public:
  ValPrinter(const llvm::Value *val) : val_(val) { }

  friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
      const ValPrinter &pr) {
    // If its not in the map, its probably been added later as an indirect
    // object...
    auto val = pr.val_;

    if (val != nullptr) {
      if (auto gv = dyn_cast<const llvm::GlobalValue>(val)) {
        o << gv->getName();
      } else if (auto fcn = dyn_cast<const llvm::Function>(val)) {
        o << fcn->getName();
      } else if (auto bb = dyn_cast<const llvm::BasicBlock>(val)) {
        o << bb->getParent()->getName() << ": " << bb->getName();
      } else if (auto inst = dyn_cast<const llvm::Instruction>(val)) {
        o << inst->getParent()->getParent()->getName() + ", " +
          inst->getParent()->getName() << ": " << *inst;
      } else {
        o << *val;
      }
    } else {
      o << "(null)";
    }
    return o;
  }

 private:
  const llvm::Value *val_;
};

#endif  // INCLUDE_LLVMHELPER_H_
