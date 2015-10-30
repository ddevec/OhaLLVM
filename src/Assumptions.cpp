/*
 * Copyright (C) 2015 David Devecsery
 */


#include "include/Assumptions.h"

#include <cassert>

#include <set>
#include <string>
#include <utility>
#include <vector>

#include "include/AllocInfo.h"
#include "include/LLVMHelper.h"

#include "llvm/Constants.h"
#include "llvm/Function.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Module.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/raw_ostream.h"

static const std::string AllocFcnName = "__specsfs_alloc_fcn";
static const std::string AllocaFcnName = "__specsfs_alloca_fcn";
static const std::string FreeFcnName = "__specsfs_free_fcn";
static const std::string RetFcnName = "__specsfs_ret_fcn";
static const std::string AssignFcnName = "__specsfs_assign_fcn";
static const std::string VisitFcnName = "abort";

static llvm::Function *getAllocaFunction(llvm::Module &m) {
  auto void_type = llvm::Type::getVoidTy(m.getContext());
  auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
  auto i64_type = llvm::IntegerType::get(m.getContext(), 64);
  auto i8_ptr_type = llvm::PointerType::get(
      llvm::IntegerType::get(m.getContext(), 8), 0);

  auto ret = m.getFunction(AllocaFcnName);
  if (ret == nullptr) {
    std::vector<llvm::Type *> ret_fcn_args;
    ret_fcn_args.push_back(i32_type);
    ret_fcn_args.push_back(i8_ptr_type);
    ret_fcn_args.push_back(i64_type);
    auto ret_fcn_type = llvm::FunctionType::get(
        void_type,
        ret_fcn_args,
        false);
    ret = llvm::Function::Create(
        ret_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        AllocaFcnName, &m);
  }

  return ret;
}

static llvm::Function *getAllocFunction(llvm::Module &m) {
  auto void_type = llvm::Type::getVoidTy(m.getContext());
  auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
  auto i64_type = llvm::IntegerType::get(m.getContext(), 64);
  auto i8_ptr_type = llvm::PointerType::get(
      llvm::IntegerType::get(m.getContext(), 8), 0);

  auto ret = m.getFunction(AllocFcnName);
  if (ret == nullptr) {
    std::vector<llvm::Type *> ret_fcn_args;
    ret_fcn_args.push_back(i32_type);
    ret_fcn_args.push_back(i8_ptr_type);
    ret_fcn_args.push_back(i64_type);
    auto ret_fcn_type = llvm::FunctionType::get(
        void_type,
        ret_fcn_args,
        false);
    ret = llvm::Function::Create(
        ret_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        AllocFcnName, &m);
  }

  return ret;
}

static llvm::Function *getRetFunction(llvm::Module &m) {
  auto void_type = llvm::Type::getVoidTy(m.getContext());

  auto ret = m.getFunction(RetFcnName);
  if (ret == nullptr) {
    std::vector<llvm::Type *> ret_fcn_args;
    auto ret_fcn_type = llvm::FunctionType::get(
        void_type,
        ret_fcn_args,
        false);
    ret = llvm::Function::Create(
        ret_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        RetFcnName, &m);
  }
  return ret;
}

static llvm::Function *getFreeFunction(llvm::Module &m) {
  auto void_type = llvm::Type::getVoidTy(m.getContext());
  auto i8_ptr_type = llvm::PointerType::get(
      llvm::IntegerType::get(m.getContext(), 8), 0);

  auto ret = m.getFunction(FreeFcnName);
  if (ret == nullptr) {
    std::vector<llvm::Type *> ret_fcn_args;
    ret_fcn_args.push_back(i8_ptr_type);
    auto ret_fcn_type = llvm::FunctionType::get(
        void_type,
        ret_fcn_args,
        false);
    ret = llvm::Function::Create(
        ret_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        FreeFcnName, &m);
  }
  return ret;
}

static llvm::Function *getAssignFunction(llvm::Module &m) {
  auto void_type = llvm::Type::getVoidTy(m.getContext());
  auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
  auto i8_ptr_type = llvm::PointerType::get(
      llvm::IntegerType::get(m.getContext(), 8), 0);

  auto ret = m.getFunction(AssignFcnName);
  if (ret == nullptr) {
    std::vector<llvm::Type *> ret_fcn_args;
    ret_fcn_args.push_back(i32_type);
    ret_fcn_args.push_back(i8_ptr_type);
    auto ret_fcn_type = llvm::FunctionType::get(
        void_type,
        ret_fcn_args,
        false);
    ret = llvm::Function::Create(
        ret_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        AssignFcnName, &m);
  }
  return ret;
}

// Visit function == "abort"!
static llvm::Function *getVisitFunction(llvm::Module &m) {
  auto void_type = llvm::Type::getVoidTy(m.getContext());
  auto ret = m.getFunction(VisitFcnName);
  if (ret == nullptr) {
    std::vector<llvm::Type *> ret_fcn_args;
    auto ret_fcn_type = llvm::FunctionType::get(
        void_type,
        ret_fcn_args,
        false);
    ret = llvm::Function::Create(
        ret_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        VisitFcnName, &m);
  }
  return ret;
}

bool AllocInst::doInstrument(llvm::Module &m) {
  auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
  auto i64_type = llvm::IntegerType::get(m.getContext(), 64);
  auto i8_ptr_type = llvm::PointerType::get(
      llvm::IntegerType::get(m.getContext(), 8), 0);

  auto fcn = getAllocFunction(m);

  std::vector<llvm::Value *> args;
  // Now we construct the call arguments:
  // Args are:
  //   Allocation ObjectID
  //   Pointer to be allocated
  //   Size of object
  args.push_back(llvm::ConstantInt::get(i32_type, allocObj_.val()));

  auto alloc_ptr = allocInst_;
  if (allocInst_->getType() != i8_ptr_type) {
    alloc_ptr = new llvm::BitCastInst(allocInst_, i8_ptr_type);
    alloc_ptr->insertAfter(allocInst_);
  }

  args.push_back(alloc_ptr);
  // Calculate the argument size
  if (auto ai = dyn_cast<llvm::AllocaInst>(allocInst_)) {
    // If we have an alloca, call the alloca fcn instead of the alloc fcn
    fcn = getAllocaFunction(m);

    auto type_size_ce = LLVMHelper::calcTypeOffset(m,
        ai->getAllocatedType(), allocInst_);

    // Then, get arraysize from the instruction
    auto array_size_val = ai->getArraySize();

    // Convert to int64_t...
    array_size_val = new llvm::SExtInst(array_size_val, i64_type, "",
        allocInst_);

    // Add the mult inst?...
    auto total_size_val =
      llvm::BinaryOperator::Create(llvm::Instruction::Mul, type_size_ce,
        array_size_val, "", allocInst_);

    args.push_back(total_size_val);
  } else {
    auto ci = cast<llvm::CallInst>(allocInst_);
    auto called_fcn = LLVMHelper::getFcnFromCall(ci);
    auto size_val = AllocInfo::getMallocSizeArg(m,
        ci, called_fcn);
    args.push_back(size_val);
  }

  // Get first instruction:
  auto insert_after = alloc_ptr;

  // Do call
  auto ci = llvm::CallInst::Create(fcn, args);

  ci->insertAfter(insert_after);

  return true;
}

bool FreeInst::doInstrument(llvm::Module &m) {
  std::vector<llvm::Value *> args;
  // Now we construct the call arguments:
  // Args are:
  //   Pointer to be freed
  if (auto ci = dyn_cast<llvm::CallInst>(freeInst_)) {
    auto fcn = getFreeFunction(m);

    auto called_fcn = LLVMHelper::getFcnFromCall(ci);

    auto free_arg = AllocInfo::getFreeArg(m, ci, called_fcn);

    args.push_back(free_arg);

    // Get first instruction:
    auto insert_before = freeInst_;

    // Do call
    llvm::CallInst::Create(fcn, args, "", insert_before);
  } else {
    assert(llvm::isa<llvm::ReturnInst>(freeInst_));
    auto fcn = getRetFunction(m);

    // Its a ret... we need to pop the stack
    auto insert_before = freeInst_;

    // Do call
    llvm::CallInst::Create(fcn, args, "", insert_before);
  }

  return true;
}

bool AssignmentInst::doInstrument(llvm::Module &m) {
  auto i32_type = llvm::IntegerType::get(m.getContext(), 32);

  auto fcn = getAssignFunction(m);

  std::vector<llvm::Value *> args;
  // Now we construct the call arguments:
  // Args are:
  //   ObjectID
  //   Pointer to be assigned
  args.push_back(llvm::ConstantInt::get(i32_type, assignVal_.val()));
  args.push_back(assignInst_);

  // Get first instruction:
  auto insert_after = assignInst_;
  // Deal with phi nodes...
  if (llvm::isa<llvm::PHINode>(insert_after)) {
    // If this inst is a phi node, we insert after the phis of this bb:
    auto &bb = *assignInst_->getParent();
    llvm::Instruction *prev_inst = nullptr;
    for (auto &inst : bb) {
      if (!llvm::isa<llvm::PHINode>(inst)) {
        assert(prev_inst != nullptr);
        insert_after = prev_inst;
        break;
      }
      prev_inst = &inst;
    }
  }

  // Do call
  auto ci = llvm::CallInst::Create(fcn, args);

  ci->insertAfter(insert_after);

  return true;
}

bool VisitInst::doInstrument(llvm::Module &m) {
  auto fcn = getVisitFunction(m);

  std::vector<llvm::Value *> args;
  // Now we construct the call arguments:
  // Args are:
  //   NONE

  // Get first instruction:
  auto bb_it = std::begin(*bb_);
  // Doh... we actually need to wait till after the phi nodes...
  while (llvm::isa<llvm::PHINode>(*bb_it)) {
    bb_it++;
  }
  auto first_inst = &(*bb_it);

  // Do call
  llvm::CallInst::Create(fcn, args, "", first_inst);

  return true;
}

// Assumptions {{{
// Calc Assumptions {{{
std::vector<std::unique_ptr<InstrumentationSite>>
PtstoAssumption::calcDependencies(
    const ObjectMap &omap, llvm::Module &,
    const free_location_multimap &free_locations) const {
  std::vector<std::unique_ptr<InstrumentationSite>> ret;
  // First, add the assignment dep
  // Then, add the alloc deps
  // Then, for each ptsto obj, find the frees associated with it
  //    Add a free dep for each of those

  // First create an assignment site for this instruction
  auto ptr_inst = cast<llvm::Instruction>(omap.valueAtID(objID_));
  ret.emplace_back(new AssignmentInst(const_cast<llvm::Instruction *>(ptr_inst),
        objID_));

  // Now, create an allocation site for each ptsto in this instruction
  for (auto &obj_id : ptstos_) {
    auto ptr_inst = dyn_cast<llvm::Instruction>(omap.valueAtID(objID_));
    if (ptr_inst != nullptr) {
      ret.emplace_back(new AllocInst(const_cast<llvm::Instruction *>(ptr_inst),
            obj_id));
    } else {
      // This is either a function call and alloca, or a global variable...
      assert(llvm::isa<llvm::GlobalVariable>(ptr_inst));
    }

    // And the free insts...
    auto free_pr = free_locations.equal_range(obj_id);
    std::for_each(free_pr.first, free_pr.second,
        [&ret, &omap]
        (const std::pair<const ObjectMap::ObjID, ObjectMap::ObjID> &pr) {
      auto free_obj_id = pr.second;
      auto free_inst = cast<llvm::Instruction>(omap.valueAtID(free_obj_id));

      ret.emplace_back(new FreeInst(
          const_cast<llvm::Instruction *>(free_inst)));
    });
  }
  return ret;
}

std::vector<std::unique_ptr<InstrumentationSite>>
DeadCodeAssumption::calcDependencies(
    const ObjectMap &, llvm::Module &,
    const free_location_multimap &) const {
  std::vector<std::unique_ptr<InstrumentationSite>> ret;
  // This is pretty simple, we just create an allocation inst at the point of
  //   visit checking

  ret.emplace_back(new VisitInst(bb_));

  return std::move(ret);
}
//}}}

// Approx Assumptions {{{
std::vector<std::unique_ptr<InstrumentationSite>>
PtstoAssumption::approxDependencies(
    const ObjectMap &omap, const llvm::Module &) const {
  std::vector<std::unique_ptr<InstrumentationSite>> ret;
  // A ptsto assumption depends on the store to the pointer
  // (the instruction at objID_), and the allocation/free sites of all of the
  // potential pointed to objects.  We don't have the free sites for these
  // objects now, so we're going to just approximate frees == allocations, until
  // we've run our ptsto analysis

  // First create an assignment site for this instruction
  auto ptr_inst = cast<llvm::Instruction>(omap.valueAtID(objID_));
  ret.emplace_back(new AssignmentInst(const_cast<llvm::Instruction *>(ptr_inst),
        objID_));

  // Now, create a double allocation site for each ptsto in this instruction
  // NOTE: The double is to approximate the free cost
  for (auto &obj_id : ptstos_) {
    auto ptr_inst = dyn_cast<llvm::Instruction>(omap.valueAtID(objID_));
    if (ptr_inst != nullptr) {
      ret.emplace_back(new DoubleAllocInst(
            const_cast<llvm::Instruction *>(ptr_inst), obj_id));
    } else {
      // This is either a function call and alloca, or a global variable...
      assert(llvm::isa<llvm::GlobalVariable>(ptr_inst));
    }
  }

  /*  FIXME: I'll do this at a higher level...
  // We now need to trim AllocInsts with identical llvm::Instruction's. 
  //   This is because they are structure allocations, and our dynamic 
  //   pass can't handle those individually
  auto sorter = [](const std::unique_ptr<InstrumentationSite> &lhs,
      const std::unique_ptr<InstrumentationSite> &rhs) -> bool {
    if (auto ai_lhs = dyn_cast<AllocInst>(lhs) &&
        auto ai_rhs = dyn_cast<AllocInst>(rhs)) {
      return ai_lhs.getInst() < ai_rhs.getInst();
    }

    return lhs < rhs;
  };

  std::sort(std::begin(ret), std::end(ret), sorter);
  auto it = std::unique(std::begin(ret), std::end(ret), sorter);
  ret.erase(it, std::end(ret));
  */

  return std::move(ret);
}

std::vector<std::unique_ptr<InstrumentationSite>>
DeadCodeAssumption::approxDependencies(
    const ObjectMap &, const llvm::Module &) const {
  std::vector<std::unique_ptr<InstrumentationSite>> ret;
  // This is pretty simple, we just create an allocation inst at the point of
  //   visit checking

  ret.emplace_back(new VisitInst(bb_));

  return std::move(ret);
}
//}}}
//}}}

