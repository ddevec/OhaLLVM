/*
 * Copyright (C) 2015 David Devecsery
 */


#include "include/Assumptions.h"

#include <cassert>

#include <set>
#include <string>
#include <utility>
#include <vector>

#include "include/ExtInfo.h"
#include "include/LLVMHelper.h"

#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

static const std::string AllocFcnName = "__specsfs_alloc_fcn";
static const std::string AllocaFcnName = "__specsfs_alloca_fcn";
static const std::string FreeFcnName = "__specsfs_free_fcn";
static const std::string RetFcnName = "__specsfs_ret_fcn";
static const std::string CallFcnName = "__specsfs_do_call";
static const std::string AssignFcnName = "__specsfs_assign_fcn";
static const std::string SetCheckFcnName = "__specsfs_set_check_fcn";
static const std::string VisitFcnName = "__specsfs_visit_fcn";

// Getting external funcion names {{{
llvm::Function *getAllocaFunction(llvm::Module &m) {
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

llvm::Function *getAllocFunction(llvm::Module &m) {
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

llvm::Function *getRetFunction(llvm::Module &m) {
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

llvm::Function *getFreeFunction(llvm::Module &m) {
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

llvm::Function *getCallFunction(llvm::Module &m) {
  auto void_type = llvm::Type::getVoidTy(m.getContext());

  auto ret = m.getFunction(CallFcnName);
  if (ret == nullptr) {
    std::vector<llvm::Type *> ret_fcn_args;
    auto ret_fcn_type = llvm::FunctionType::get(
        void_type,
        ret_fcn_args,
        false);
    ret = llvm::Function::Create(
        ret_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        CallFcnName, &m);
  }
  return ret;
}

llvm::Function *getSetCheckFunction(llvm::Module &m) {
  auto void_type = llvm::Type::getVoidTy(m.getContext());
  auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
  auto i8_ptr_type = llvm::PointerType::get(
      llvm::IntegerType::get(m.getContext(), 8), 0);
  auto i32_ptr_type = llvm::PointerType::get(
      llvm::IntegerType::get(m.getContext(), 32), 0);

  auto ret = m.getFunction(SetCheckFcnName);
  if (ret == nullptr) {
    std::vector<llvm::Type *> ret_fcn_args;
    // FIXME: for dbg
    ret_fcn_args.push_back(i32_type);
    ret_fcn_args.push_back(i8_ptr_type);
    // We just give it any int32_t array type?
    ret_fcn_args.push_back(i32_ptr_type);
    // size
    ret_fcn_args.push_back(i32_type);
    auto ret_fcn_type = llvm::FunctionType::get(
        void_type,
        ret_fcn_args,
        false);
    ret = llvm::Function::Create(
        ret_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        SetCheckFcnName, &m);
  }
  return ret;
}

llvm::Function *getAssignFunction(llvm::Module &m) {
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

// Visit function == "__specsfs_visit_fcn"!
llvm::Function *getVisitFunction(llvm::Module &m) {
  auto void_type = llvm::Type::getVoidTy(m.getContext());
  auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
  auto ret = m.getFunction(VisitFcnName);
  if (ret == nullptr) {
    std::vector<llvm::Type *> ret_fcn_args;
    ret_fcn_args.push_back(i32_type);
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
//}}}

bool AllocInst::doInstrument(llvm::Module &m, const ExtLibInfo &ext_info) {
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
    llvm::dbgs() << "inst is: " << ValPrinter(allocInst_) << "\n";
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
    llvm::CallSite cs(ci);

    llvm::Instruction *ia = ci;
    auto &info = ext_info.getInfo(ci);
    auto data = info.getAllocData(m, cs,
        *static_cast<ValueMap *>(nullptr), &ia);
    assert(data.size() == 1);
    args.push_back(std::get<1>(data[0]));
  }

  // Get first instruction:
  auto insert_after = alloc_ptr;

  // Do call
  auto ci = llvm::CallInst::Create(fcn, args);

  ci->insertAfter(insert_after);

  return true;
}

bool FreeInst::doInstrument(llvm::Module &m, const ExtLibInfo &ext_info) {
  std::vector<llvm::Value *> args;
  // Now we construct the call arguments:
  // Args are:
  //   Pointer to be freed
  if (auto ci = dyn_cast<llvm::CallInst>(freeInst_)) {
    auto fcn = getFreeFunction(m);

    /*
    auto called_fcn = LLVMHelper::getFcnFromCall(ci);

    auto free_arg = AllocInfo::getFreeArg(m, ci, called_fcn);
    */
    auto &free_info = ext_info.getInfo(ci);
    llvm::Instruction *ia = ci;
    llvm::CallSite cs(ci);
    auto free_vec = free_info.getFreeData(m, cs,
        *static_cast<ValueMap *>(nullptr), &ia);
    assert(free_vec.size() == 1);

    args.push_back(free_vec[0]);

    llvm::dbgs() << "About to instrument free: " << *ci << "\n";
    // Do call
    llvm::CallInst::Create(fcn, args, "", ci);
  } else {
    assert(llvm::isa<llvm::ReturnInst>(freeInst_));
    auto fcn = getRetFunction(m);

    auto parent_fcn = freeInst_->getParent()->getParent();
    setCache_.addRet(parent_fcn);

    // Its a ret... we need to pop the stack
    auto insert_before = freeInst_;

    // Do call
    llvm::CallInst::Create(fcn, args, "", insert_before);
  }

  return true;
}

bool AssignmentInst::doInstrument(llvm::Module &m, const ExtLibInfo &) {
  auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
  auto i8_ptr_type = llvm::PointerType::get(
      llvm::IntegerType::get(m.getContext(), 8), 0);

  auto fcn = getAssignFunction(m);

  std::vector<llvm::Value *> args;
  // Now we construct the call arguments:
  // Args are:
  //   ObjectID
  //   Pointer to be assigned
  args.push_back(llvm::ConstantInt::get(i32_type, assignVal_.val()));

  auto assign_inst = assignInst_;
  if (assignInst_->getType() != i8_ptr_type) {
    assign_inst = new llvm::BitCastInst(assignInst_, i8_ptr_type);
  }

  args.push_back(assign_inst);

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

  if (assign_inst != assignInst_) {
    assign_inst->insertAfter(insert_after);
    insert_after = assign_inst;
  }

  // Do call
  auto ci = llvm::CallInst::Create(fcn, args);

  ci->insertAfter(insert_after);

  return true;
}

static llvm::GlobalVariable *getGlobalSet(llvm::Module &m,
    const std::set<ValueMap::Id> &set,
    SetCache &cache) {
  int32_t id = cache.getID(set);

  // llvm::dbgs() << "Have id: " << id << "\n";

  std::string gv_name = "__specsfs_gv_set" + std::to_string(id);

  /*
  llvm::dbgs() << "Have gv_name: " << gv_name << "\n";

  llvm::dbgs() << "  Set data is:";
  for (auto obj_id : set) {
    llvm::dbgs() << " " << obj_id;
  }
  llvm::dbgs() << "\n";
  */

  auto gv = m.getGlobalVariable(gv_name);
  if (gv == nullptr) {
    auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
    // Create the array type:
    //   Note, its an array of (set.size()) of int32_ts
    auto array_type = llvm::ArrayType::get(i32_type,
        set.size());

    // Create the array initializer:
    //   For each elm : set
    //     arrayInit[i] = elm
    std::vector<llvm::Constant *> initializer;
    // llvm::dbgs() << "  Creating gv: " << gv_name << "\n";
    // llvm::dbgs() << "  With set:";
    for (auto obj_id : set) {
      initializer.push_back(
          llvm::ConstantInt::get(i32_type, obj_id.val()));
      // llvm::dbgs() << " " << obj_id;
    }
    // llvm::dbgs() << "\n";


    auto array_init = llvm::ConstantArray::get(array_type, initializer);

    // Create it
    gv = new llvm::GlobalVariable(m,
        array_type,
        true,
        llvm::GlobalValue::ExternalLinkage,
        array_init,
        gv_name);
  }

  return gv;
}

bool SetCheckInst::doInstrument(llvm::Module &m, const ExtLibInfo &) {
  static int32_t id = 0;
  auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
  auto i8_ptr_type = llvm::PointerType::get(
      llvm::IntegerType::get(m.getContext(), 8), 0);

  auto fcn = getSetCheckFunction(m);

  std::vector<llvm::Value *> args;
  // Now we construct the call arguments:
  // Args are:
  //   Pointer
  //   Pointer Set Array
  //   Pointer Set Size

  // Okay, we have two options here, an argument or an instruction
  auto assign_inst = assignInst_;
  // llvm::dbgs() << " Have asignInst_: " << *assignInst_ << "\n";
  if (assignInst_->getType() != i8_ptr_type) {
    // llvm::dbgs() << "assignInst_ is: " << ValPrinter(assignInst_) << "\n";
    assign_inst = new llvm::BitCastInst(assignInst_, i8_ptr_type, "", site_);
  }

  // FIXME: Debug stuff
  args.push_back(llvm::ConstantInt::get(i32_type, id++));

  // Arg0, pointer
  // llvm::dbgs() << " Have assign_inst: " << *assign_inst << "\n";
  args.push_back(assign_inst);

  llvm::Instruction *first_inst;
  if (auto arg = dyn_cast<llvm::Argument>(assignInst_)) {
    first_inst = arg->getParent()->getEntryBlock().getFirstNonPHIOrDbg();
  } else {
    auto inst = cast<llvm::Instruction>(assignInst_);
    first_inst = inst;
  }

  // llvm::dbgs() << " Have first_inst: " << *first_inst << "\n";

  assert(first_inst != nullptr);

  // Now we get the pointer set array...
  std::vector<llvm::Constant *> idx_list;
  idx_list.push_back(llvm::ConstantInt::get(i32_type, 0));
  idx_list.push_back(llvm::ConstantInt::get(i32_type, 0));
  auto array_ce = getGlobalSet(m, checkSet_, setCache_);
  args.push_back(llvm::ConstantExpr::getGetElementPtr(
        array_ce->getType(), array_ce, idx_list));

  // Set size:
  args.push_back(llvm::ConstantInt::get(i32_type, checkSet_.size()));

  // Get first instruction:
  auto insert_after = first_inst;

  assert(insert_after != nullptr);


  // Do call
  if (site_ != nullptr) {
    llvm::CallInst::Create(fcn, args, "", site_);
  } else {
    auto ci = llvm::CallInst::Create(fcn, args);
    assert(ci != nullptr);
    // llvm::dbgs() << " inserting ci at: " << *insert_after << "\n";
    ci->insertAfter(insert_after);
  }

  return true;
}

bool VisitInst::doInstrument(llvm::Module &m, const ExtLibInfo &) {
  static int32_t visit_id = 0;

  auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
  auto fcn = getVisitFunction(m);

  std::vector<llvm::Value *> args;
  // Now we construct the call arguments:
  // Args are:
  //   NONE
  args.push_back(llvm::ConstantInt::get(i32_type, visit_id));
  visit_id++;

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
    ValueMap &map, llvm::Module &,
    const free_location_multimap &free_locations,
    SetCache &set_cache) const {
  std::vector<std::unique_ptr<InstrumentationSite>> ret;
  // First, add the assignment dep
  // Then, add the alloc deps
  // Then, for each ptsto obj, find the frees associated with it
  //    Add a free dep for each of those

  // First create an assignment site for this instruction
  auto ptr_inst = instOrArg_;
  // This is wrong... Should check that ptr_inst isn't within a set of
  //    values...
  // Must map the values to their ids:
  std::vector<ValueMap::Id> pts_ids;
  for (auto &val : ptstos_) {
    llvm::dbgs() << "Have val: " << ValPrinter(val) << "\n";
    for (auto &id : map.getIds(val)) {
      pts_ids.push_back(id);
    }
  }
  /*
  llvm::dbgs() << "making new setcheck for: " << ValPrinter(ptr_inst) << "\n";
  llvm::dbgs() << "   at site: " << ValPrinter(site_) << "\n";
  */
  ret.emplace_back(new SetCheckInst(ptr_inst, pts_ids, set_cache,
        const_cast<llvm::Instruction *>(site_)));

  // Now, create an allocation site for each ptsto in this instruction
  for (auto &val : ptstos_) {
    // if val is special/null...
    if (val == nullptr) {
      continue;
    }

    auto ptr_inst = dyn_cast<llvm::Instruction>(val);
    for (auto obj_id : map.getIds(val)) {
      if (ptr_inst != nullptr) {
          ret.emplace_back(
              new AllocInst(const_cast<llvm::Instruction *>(ptr_inst),
                obj_id));
      } else {
        // UGH, need to find equivalencies too
        set_cache.addGVUse(obj_id);
      }

      // And the free insts...
      auto free_pr = free_locations.equal_range(obj_id);
      std::for_each(free_pr.first, free_pr.second,
          [&ret, &map, &set_cache]
          (const std::pair<ValueMap::Id, llvm::Value *> &pr) {
        auto &free_inst = pr.second;

        ret.emplace_back(new FreeInst(cast<llvm::Instruction>(free_inst),
            set_cache));
      });
    }
  }
  return ret;
}

std::vector<std::unique_ptr<InstrumentationSite>>
DeadCodeAssumption::calcDependencies(
    ValueMap &, llvm::Module &,
    const free_location_multimap &,
    SetCache &) const {
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
    ValueMap &map, const llvm::Module &) const {
  std::vector<std::unique_ptr<InstrumentationSite>> ret;
  // A ptsto assumption depends on the store to the pointer
  // (the instruction at objID_), and the allocation/free sites of all of the
  // potential pointed to objects.  We don't have the free sites for these
  // objects now, so we're going to just approximate frees == allocations, until
  // we've run our ptsto analysis

  // First create an assignment site for this instruction
  // auto ptr_inst = cast<llvm::Instruction>(map.valueAtID(objID_));
  // assert(map.getValue(inst_).val() != 350);
  static SetCache bleh;
  std::vector<ValueMap::Id> pts_ids;
  for (auto &val : ptstos_) {
    for (auto &id : map.getIds(val)) {
      pts_ids.push_back(id);
    }
  }
  ret.emplace_back(new SetCheckInst(instOrArg_, pts_ids, bleh, nullptr));

  // Now, create a double allocation site for each ptsto in this instruction
  // NOTE: The double is to approximate the free cost
  for (auto &val : ptstos_) {
    if (val == nullptr) {
      llvm::dbgs() << "val unused?\n";
      continue;
    }

    for (auto &obj_id : map.getIds(val)) {
      auto ptr_inst = dyn_cast<llvm::Instruction>(val);
      if (ptr_inst != nullptr) {
        ret.emplace_back(new DoubleAllocInst(
              const_cast<llvm::Instruction *>(ptr_inst), obj_id));
      } else {
        // This is a global variable, or function...
        llvm::dbgs() << "Global assumption? " << FullValPrint(obj_id, map)
          << "\n";
        assert(llvm::isa<llvm::GlobalValue>(val));
      }
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
    ValueMap &, const llvm::Module &) const {
  std::vector<std::unique_ptr<InstrumentationSite>> ret;
  // This is pretty simple, we just create an allocation inst at the point of
  //   visit checking

  ret.emplace_back(new VisitInst(bb_));

  return std::move(ret);
}
//}}}
//}}}

