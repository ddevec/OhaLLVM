/*
 * Copyright (C) 2015 David Devecsery
 */

// We use a good hash...
#include <openssl/sha.h>

#include <algorithm>
#include <functional>
#include <string>
#include <utility>
#include <vector>


#include "llvm/Pass.h"
#include "llvm/PassSupport.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Analysis/AliasAnalysis.h"
// #include "llvm/Analysis/ProfileInfo.h"

#include "include/BloomHash.h"
#include "include/ConstraintPass.h"
#include "include/ExtInfo.h"
#include "include/LLVMHelper.h"
#include "include/SpecAnders.h"
#include "include/SpecAndersCS.h"
#include "include/ValueMap.h"

const int64_t PtrSizeBytes = sizeof(void *);

static const std::string MainInit2Name = "__specsfs_main_init2";
static const std::string MainInit3Name = "__specsfs_main_init3";

static const std::string PushName = "__specsfs_callstack_push";
static const std::string PopName = "__specsfs_callstack_pop";
static const std::string CheckName = "__specsfs_callstack_check";

static const std::string SetJmpName = "__specsfs_do_setjmp_call";
static const std::string LongJmpName = "__specsfs_do_longjmp_call";

static size_t bloom_hash(size_t ukey) {
  union {
    unsigned char raw[SHA_DIGEST_LENGTH];
    size_t ret[2];
  } result;
  /*
  int64_t key = static_cast<int64_t>(ukey);
  key = (~key) + (key << 21);  // key = (key << 21) - key - 1;
  key = key ^ (key >> 24);
  key = (key + (key << 3)) + (key << 8);  // key * 265
  key = key ^ (key >> 14);
  key = (key + (key << 2)) + (key << 4);  // key * 21
  key = key ^ (key >> 28);
  key = key + (key << 31);
  return static_cast<size_t>(key);
  */

  SHA1(reinterpret_cast<unsigned char *>(&ukey), sizeof(ukey), result.raw);

  return result.ret[1];
}


using llvm::AliasAnalysis;
using llvm::AliasResult;
typedef llvm::MemoryLocation Location;

static bool isGiriCall(const llvm::Function *dir_fcn) {
  if (dir_fcn->getName() == "recordLock") {
    return true;
  }

  if (dir_fcn->getName() == "recordUnlock") {
    return true;
  }

  if (dir_fcn->getName() == "recordStartBB") {
    return true;
  }

  if (dir_fcn->getName() == "recordBB") {
    return true;
  }

  if (dir_fcn->getName() == "recordCall") {
    return true;
  }

  if (dir_fcn->getName() == "recordExtCall") {
    return true;
  }

  if (dir_fcn->getName() == "giriCtor") {
    return true;
  }

  if (dir_fcn->getName() == "recordFork") {
    return true;
  }

  if (dir_fcn->getName() == "recordSelect") {
    return true;
  }

  if (dir_fcn->getName() == "recordExtCallRet") {
    return true;
  }

  if (dir_fcn->getName() == "recordLoad") {
    return true;
  }

  if (dir_fcn->getName() == "recordStore") {
    return true;
  }

  if (dir_fcn->getName() == "recordReturn") {
    return true;
  }

  if (dir_fcn->getName() == "recordInit") {
    return true;
  }

  if (dir_fcn->getName() == "recordStrLoad") {
    return true;
  }

  if (dir_fcn->getName() == "recordStrStore") {
    return true;
  }

  if (dir_fcn->getName() == "recordStrcatStore") {
    return true;
  }

  return false;
}

class SpecSFSInstrumenter : public llvm::ModulePass {
 public:
  static char ID;
  SpecSFSInstrumenter();

  bool runOnModule(llvm::Module &M) override;

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const override;

 private:
  void setupTypes(llvm::Module &m);

  llvm::Function *getSetJmpFcn(llvm::Module &m);
  llvm::Function *getLongJmpFcn(llvm::Module &m);
  llvm::Function *getPushFcn(llvm::Module &m);
  llvm::Function *getPopFcn(llvm::Module &m);
  llvm::Function *getCheckFcn(llvm::Module &m);

  llvm::Constant *BloomFilterToPointer(
      llvm::Module &,
      const BloomHasher::BloomFilter &);

  std::pair<llvm::Constant *, llvm::Constant *>
  getCheckData(llvm::Module &m,
      const std::vector<const std::vector<CsCFG::Id> *> &data,
      BloomHasher::BloomFilter *hash_combine);

  void addCallInst(llvm::Module &m,
      CsCFG::Id val,
      llvm::Instruction *cs,
      const std::vector<const std::vector<CsCFG::Id> *> &stacks);

  bool addCallstackChecks(llvm::Module &m,
      SpecAndersCS &aa);

  llvm::Type *int32Type_ = nullptr;
  llvm::Type *int64Type_ = nullptr;
  llvm::Type *int64PtrType_ = nullptr;
  llvm::Type *int32PtrType_ = nullptr;
  llvm::Type *int32PtrPtrType_ = nullptr;
  llvm::Type *int8Type_ = nullptr;
  llvm::Type *int8PtrType_ = nullptr;

  llvm::Type *voidType_ = nullptr;

  llvm::Function *callCheckFcn_ = nullptr;
  llvm::Function *callPopFcn_ = nullptr;
  llvm::Function *callPushFcn_ = nullptr;
  llvm::Function *callSetJmpFcn_ = nullptr;
  llvm::Function *callLongJmpFcn_ = nullptr;
};

void SpecSFSInstrumenter::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  // Because we're an AliasAnalysis
  usage.setPreservesAll();

  // We don't instrument frees in dead code, so we need to get that here
  usage.addRequired<UnusedFunctions>();
  usage.addRequired<IndirFunctionInfo>();

  // We require SpecSFS, to provide assumptions and ObjID->llvm::Value mappings
  // usage.addRequired<llvm::AliasAnalysis>();
}

SpecSFSInstrumenter::SpecSFSInstrumenter() : llvm::ModulePass(ID) { }
char SpecSFSInstrumenter::ID = 0;
namespace llvm {
  static RegisterPass<SpecSFSInstrumenter>
      X("specsfs-do-inst", "Speculative Sparse Flow-sensitive Analysis "
          "Speculative checking instrumentation pass", false, false);
}  // namespace llvm

static free_location_multimap findFreeLocs(llvm::Module &m, UnusedFunctions &uf,
    IndirFunctionInfo &indir_info, Cg &cg, AliasAnalysis &aa) {
  auto &map = cg.vals();
  auto &ext_info = cg.extInfo();

  // The map of all ids freed at an instruction
  free_location_multimap free_locs;
  std::vector<llvm::Instruction *> allocs;

  for (auto &fcn : m) {
    std::vector<llvm::Value *> alloc_insts;
    for (auto &bb : fcn) {
      if (uf.isUsed(bb)) {
        // Now lets iterate some instructions
        for (auto &insn : bb) {
          // All allocs happen at the beginning of a function, so this can be
          //   done in one pass
          if (llvm::isa<llvm::AllocaInst>(insn)) {
            alloc_insts.push_back(&insn);
          // If this instruction is a ret instruction:
          } else if (llvm::isa<llvm::ReturnInst>(insn)) {
            // Each value stacked prior to this point is freed by this insn
            // AKA: for each insn : alloca_list add to free list
            for (auto alloc_inst : alloc_insts) {
              free_locs.emplace(map.getDef(alloc_inst),
                  &insn);
            }
          // Also gather information about all allocs
          } else if (auto ci = dyn_cast<llvm::CallInst>(&insn)) {
            // For now, just gather alloc info
            llvm::ImmutableCallSite cs(ci);

            if (llvm::isa<llvm::InlineAsm>(cs.getCalledValue())) {
              continue;
            }

            auto dir_fcn = LLVMHelper::getFcnFromCall(cs);
            std::vector<const llvm::Function *> targets;
            if (dir_fcn == nullptr) {
              // get from indir info
              llvm::dbgs() << "Getting target for: " << ValPrinter(ci) <<
                "\n";
              for (auto &target : indir_info.getTargets(ci)) {
                targets.push_back(cast<llvm::Function>(target));
              }
            } else {
              // Ignore giri calls!
              if (!isGiriCall(dir_fcn)) {
                targets.push_back(dir_fcn);
              }
            }

            for (auto &fcn : targets) {
              auto &info = ext_info.getInfo(fcn);
              // What I really need here is a mapping of all call sites to free
              //   sites...
              //
              // for each inst:
              //  if inst is free:
              //   for each alloc:
              //    if alias(alloc, free):
              //     add free mapping to alloc
              if (info.canAlloc()) {
                allocs.push_back(ci);
                break;
              }
            }
          }
        }
      }
    }
  }

  for (auto &fcn : m) {
    for (auto &bb : fcn) {
      if (uf.isUsed(bb)) {
        // Now lets iterate some instructions
        for (auto &insn : bb) {
          if (auto ci = dyn_cast<llvm::CallInst>(&insn)) {
            // For now, just gather alloc info
            llvm::CallSite cs(ci);

            if (llvm::isa<llvm::InlineAsm>(cs.getCalledValue())) {
              continue;
            }

            // What about indirect calls???
            auto dir_fcn = LLVMHelper::getFcnFromCall(ci);
            std::vector<const llvm::Function *> targets;
            if (dir_fcn == nullptr) {
              // get from indir info
              for (auto &target : indir_info.getTargets(ci)) {
                targets.push_back(cast<llvm::Function>(target));
              }
            } else {
              // Still ignore giir calls
              if (!isGiriCall(dir_fcn)) {
                targets.push_back(dir_fcn);
              }
            }

            for (auto fcn : targets) {
              auto &info = ext_info.getInfo(fcn);
              llvm::Instruction *ia = ci;
              auto free_info = info.getFreeData(m, cs, map, &ia);
              for (auto &alloc : allocs) {
                for (auto free_arg : free_info) {
                  if (aa.alias(Location(free_arg), Location(alloc)) !=
                      AliasResult::NoAlias) {
                    free_locs.emplace(map.getDef(alloc),
                        free_arg);
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  return std::move(free_locs);
}

void SpecSFSInstrumenter::setupTypes(llvm::Module &m) {
  int32Type_ = llvm::IntegerType::get(m.getContext(), 32);
  int64Type_ = llvm::IntegerType::get(m.getContext(), 64);
  int8Type_ = llvm::IntegerType::get(m.getContext(), 32);

  int64PtrType_ = llvm::PointerType::get(int64Type_, 0);
  int32PtrType_ = llvm::PointerType::get(int32Type_, 0);
  int32PtrPtrType_ = llvm::PointerType::get(int32PtrType_, 0);
  int8PtrType_ = llvm::PointerType::get(int8Type_, 0);

  voidType_ = llvm::Type::getVoidTy(m.getContext());
}

llvm::Function *SpecSFSInstrumenter::getSetJmpFcn(llvm::Module &m) {
  if (callSetJmpFcn_ == nullptr) {
    std::vector<llvm::Type *> jmp_args =
        { int32Type_, int8PtrType_ };
    auto fcn_type = llvm::FunctionType::get(
        voidType_,
        jmp_args,
        false);
    callSetJmpFcn_ = llvm::Function::Create(fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        SetJmpName, &m);
  }
  return callSetJmpFcn_;
}

llvm::Function *SpecSFSInstrumenter::getLongJmpFcn(llvm::Module &m) {
  if (callLongJmpFcn_ == nullptr) {
    std::vector<llvm::Type *> jmp_args =
        { int32Type_, int8PtrType_, int64Type_ };
    auto fcn_type = llvm::FunctionType::get(
        voidType_,
        jmp_args,
        false);
    callLongJmpFcn_ = llvm::Function::Create(fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        LongJmpName, &m);
  }
  return callLongJmpFcn_;
}

llvm::Function *SpecSFSInstrumenter::getPushFcn(llvm::Module &m) {
  if (callPushFcn_ == nullptr) {
    std::vector<llvm::Type *> push_args =
        { int32Type_, int64Type_ };
    auto fcn_type = llvm::FunctionType::get(
        voidType_,
        push_args,
        false);
    callPushFcn_ = llvm::Function::Create(fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        PushName, &m);
  }
  return callPushFcn_;
}

llvm::Function *SpecSFSInstrumenter::getPopFcn(llvm::Module &m) {
  if (callPopFcn_ == nullptr) {
    std::vector<llvm::Type *> pop_args =
        { int32Type_ };
    auto fcn_type = llvm::FunctionType::get(
        voidType_,
        pop_args,
        false);
    callPopFcn_ = llvm::Function::Create(fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        PopName, &m);
  }
  return callPopFcn_;
}

llvm::Function *SpecSFSInstrumenter::getCheckFcn(llvm::Module &m) {
  if (callCheckFcn_ == nullptr) {
    std::vector<llvm::Type *> check_args =
        { int32Type_, int32Type_, int32PtrPtrType_, int64PtrType_ };
    auto fcn_type = llvm::FunctionType::get(
        voidType_,
        check_args,
        false);
    callCheckFcn_ = llvm::Function::Create(fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        CheckName, &m);
  }
  return callCheckFcn_;
}

std::pair<llvm::Constant *, llvm::Constant *>
SpecSFSInstrumenter::getCheckData(llvm::Module &m,
    const std::vector<const std::vector<CsCFG::Id> *> &data,
    BloomHasher::BloomFilter *hash_combine) {
  // Okay, create a type for this data
  // We will return a pair, a size followed by an array of size, data arrays
  // We are ultimately returning an array of i32PtrTypes_
  std::vector<llvm::Constant *> glbl_array_data;
  std::vector<llvm::Value *> stacks;
  for (auto &pstack : data) {
    // Create an array of the stack:
    // Type is: i32_t, size+1
    auto array_type = llvm::ArrayType::get(int32Type_, pstack->size()+1);

    // Now, create the constant array
    // elm 0 is constant of size:
    std::vector<llvm::Constant *> array_data =
        { llvm::ConstantInt::get(int32Type_, pstack->size()) };
    int64_t array_hash = 0x5F5F5F5F5F5F5F5FULL;
    for (auto &id : *pstack) {
      array_data.push_back(llvm::ConstantInt::get(int32Type_,
            static_cast<int32_t>(id)));

      // size_t id_hash = std::hash<CsCFG::Id>()(id);
      size_t id_hash = bloom_hash(static_cast<size_t>(id));
      llvm::dbgs() << "id hash is: " << id_hash << "\n";

      array_hash = BloomHasher::mix_hash(array_hash,
          id_hash);
    }
    BloomHasher::bloom_add(*hash_combine, array_hash);

    // Now, create a constant array
    auto const_array = llvm::ConstantArray::get(array_type, array_data);
    // Now, create the array:
    llvm::GlobalVariable *sub_array = new llvm::GlobalVariable(m,
        array_type, true,
        llvm::GlobalValue::InternalLinkage, const_array,
        "CallStackCheckData_internal");

    std::vector<llvm::Constant *> indicies =
        { llvm::ConstantInt::get(int32Type_, 0),
          llvm::ConstantInt::get(int32Type_, 0) };
    // And bitcast that to an int32PtrType_
    auto gep = llvm::ConstantExpr::getInBoundsGetElementPtr(
        sub_array->getType(),
        sub_array,
        indicies);
    glbl_array_data.push_back(gep);
  }

  auto array_type = llvm::ArrayType::get(int32PtrType_, data.size());

  auto gv_init = llvm::ConstantArray::get(array_type, glbl_array_data);

  // Now, create the array:
  llvm::GlobalVariable *gv = new llvm::GlobalVariable(m, array_type, true,
      llvm::GlobalValue::InternalLinkage, gv_init, "CallStackCheckData");

  // Now, get the pointer to the first element (thats an int32ptrptrtype_)
  std::vector<llvm::Constant *> indicies =
      { llvm::ConstantInt::get(int32Type_, 0),
        llvm::ConstantInt::get(int32Type_, 0) };
  // And bitcast that to an int32PtrType_
  auto gep = llvm::ConstantExpr::getInBoundsGetElementPtr(gv->getType(),
      gv, indicies);

  return std::make_pair(llvm::ConstantInt::get(int32Type_, data.size()), gep);
}

llvm::Constant *SpecSFSInstrumenter::BloomFilterToPointer(
    llvm::Module &m,
    const BloomHasher::BloomFilter &filter) {
  // Convert the data into int 64 types
  auto array_type = llvm::ArrayType::get(int64Type_, filter.size());

  std::vector<llvm::Constant *> array_data;

  for (auto &elm : filter) {
    array_data.push_back(llvm::ConstantInt::get(int64Type_, elm));
  }

  auto array = llvm::ConstantArray::get(array_type, array_data);

  // Now, create the array:
  llvm::GlobalVariable *glbl_array = new llvm::GlobalVariable(m,
      array_type, true,
      llvm::GlobalValue::InternalLinkage, array,
      "CallStackCheckData_bloomfilter");

  std::vector<llvm::Constant *> indicies =
      { llvm::ConstantInt::get(int64Type_, 0),
        llvm::ConstantInt::get(int64Type_, 0) };

  // And bitcast that to an int64PtrType_
  auto array_ptr = llvm::ConstantExpr::getInBoundsGetElementPtr(
      glbl_array->getType(),
      glbl_array,
      indicies);

  return array_ptr;
}

void SpecSFSInstrumenter::addCallInst(llvm::Module &m,
    CsCFG::Id val,
    llvm::Instruction *cs,
    const std::vector<const std::vector<CsCFG::Id> *> &stacks) {
  // First add a call to the push function
  {
    auto push_fcn = getPushFcn(m);

    // we add the push jsut before the call
    // size_t val_hash = std::hash<CsCFG::Id>()(val);
    size_t val_hash = bloom_hash(static_cast<size_t>(val));
    std::vector<llvm::Value *> push_args =
        { llvm::ConstantInt::get(int32Type_, static_cast<int32_t>(val)),
          llvm::ConstantInt::get(int64Type_, val_hash) };
    llvm::CallInst::Create(push_fcn, push_args, "", cs);
  }

  // Then, (if needed), do a call to the check function
  if (stacks.size() > 0) {
    auto check_fcn = getCheckFcn(m);

    // Initialize array to 0
    BloomHasher::BloomFilter stack_hash;
    BloomHasher::bloom_clear(stack_hash);
    auto data_pr = getCheckData(m, stacks, &stack_hash);

    auto array_data = BloomFilterToPointer(m, stack_hash);
    llvm::dbgs() << "array_data is: " << *array_data << "\n";
    std::vector<llvm::Value *> check_args =
        { llvm::ConstantInt::get(int32Type_, static_cast<int32_t>(val)),
          data_pr.first, data_pr.second,
          array_data };
    llvm::CallInst::Create(check_fcn, check_args, "", cs);
  }

  // Finally call the pop function
  {
    auto pop_fcn = getPopFcn(m);

    std::vector<llvm::Value *> pop_args =
        { llvm::ConstantInt::get(int32Type_, static_cast<int32_t>(val)) };
    auto pop_call = llvm::CallInst::Create(pop_fcn, pop_args);
    pop_call->insertAfter(cs);
  }
}

bool SpecSFSInstrumenter::addCallstackChecks(llvm::Module &m,
    SpecAndersCS &aa) {
  bool ret = false;
  // Okay, time to deal w/ callstack checks
  // First, get the list of callsites we need to check
  auto &invalid_stacks = aa.getInvalidStacks();

  // Then, determine our set of possible pred callsites...
  //   Worklist alg here
  util::Worklist<CsCFG::Id> wl;
  std::unordered_set<CsCFG::Id> inst_ids;

  auto &cfg = aa.getCsCFG();

  // Setup our initial worklist, for each id in stack
  for (auto &stack : invalid_stacks) {
    for (auto &id : stack) {
      wl.push(id);
    }
  }

  // Now, add call/ret inst for all pred callsites!
  while (!wl.empty()) {
    auto id = wl.pop();

    auto &node = cfg.getNode(id);
    auto new_id = util::convert_id<CsCFG::Id>(node.id());

    auto rc = inst_ids.emplace(new_id);

    if (rc.second) {
      for (auto &pred_id : node.preds()) {
        // FIXME(ddevec) ugly....
        wl.push(util::convert_id<CsCFG::Id>(pred_id));
      }
    }
  }

  std::unordered_multimap<CsCFG::Id, const std::vector<CsCFG::Id> *>
    invalid_stack_insts;

  // create a mapping from the last id in the stack to the stack
  for (auto &stack : invalid_stacks) {
    invalid_stack_insts.emplace(stack.back(), &stack);
  }

  // UGH: Scan for setjmp/longjmp calls
  std::vector<llvm::CallInst *> setjmps;
  std::vector<llvm::CallInst *> longjmps;
  for (auto &fcn : m) {
    for (auto &bb : fcn) {
      for (auto &inst : bb) {
        if (auto ci = dyn_cast<llvm::CallInst>(&inst)) {
          llvm::CallSite cs(ci);
          auto called_fcn = LLVMHelper::getFcnFromCall(ci);

          if (called_fcn != nullptr &&
              (called_fcn->getName() == "__sigsetjmp" ||
              called_fcn->getName() == "__setjmp" ||
              called_fcn->getName() == "_setjmp")) {
            setjmps.push_back(ci);
          } else if (called_fcn != nullptr &&
              (called_fcn->getName() == "longjmp" ||
              called_fcn->getName() == "siglongjmp")) {
            longjmps.push_back(ci);
          }
        }
      }
    }
  }


  // inst_ids now contains all call sites I need to instrument w/ call/ret info
  for (auto id : inst_ids) {
    // Now instrument all ids
    auto pr = invalid_stack_insts.equal_range(id);

    auto &cs_scc = cfg.getSCC(id);
    for (auto &cs : cs_scc) {
      // Ignore declarations...
      if (cs == nullptr) {
        continue;
      }
      auto ci = cast<llvm::CallInst>(cs);
      auto called_fcn = LLVMHelper::getFcnFromCall(ci);
      if (called_fcn != nullptr) {
        if (called_fcn->isDeclaration()) {
          continue;
        }
      }

      ret = true;
      std::vector<const std::vector<CsCFG::Id> *> check_vec;
      for (auto it = pr.first, en = pr.second; it != en; ++it) {
        check_vec.emplace_back(it->second);
      }
      addCallInst(m, id,
          const_cast<llvm::Instruction *>(cs), check_vec);
    }
  }

  for (auto ci : setjmps) {
    llvm::CallSite cs(ci);

    auto arg = cs.getArgument(0);
    auto i8_ptr_val = arg;
    // Cast the argument to an i8ptr...
    if (arg->getType() != int8PtrType_) {
      i8_ptr_val = new llvm::BitCastInst(arg, int8PtrType_, "", ci);
    }

    std::vector<llvm::Value *> args =
        { llvm::ConstantInt::get(int32Type_, 0), i8_ptr_val };

    // Handle setjump operations here
    // Call the setjmp inst function with our arg
    llvm::CallInst::Create(getSetJmpFcn(m), args, "", ci);
  }

  for (auto ci : longjmps) {
    llvm::CallSite cs(ci);

    auto arg = cs.getArgument(0);
    auto i8_ptr_val = arg;
    if (arg->getType() != int8PtrType_) {
      i8_ptr_val = new llvm::BitCastInst(arg, int8PtrType_, "", ci);
    }

    std::vector<llvm::Value *> args =
        { llvm::ConstantInt::get(int32Type_, 0), i8_ptr_val,
          llvm::ConstantInt::get(int64Type_, 0) };

    // Handle long jump operations here
    llvm::CallInst::Create(getLongJmpFcn(m), args, "", ci);
  }

  return ret;
}

bool SpecSFSInstrumenter::runOnModule(llvm::Module &m) {
  setupTypes(m);

  auto &aa = getAnalysis<llvm::AAResultsWrapperPass>().getAAResults();
  auto &uf = getAnalysis<UnusedFunctions>();
  auto &indir = getAnalysis<IndirFunctionInfo>();

  const AssumptionSet *passumptions = nullptr;
  const ConstraintPass *pcp;

  if (auto panders = getAnalysisIfAvailable<SpecAndersWrapperPass>()) {
    llvm::dbgs() << "Have anders ptsto\n";
    passumptions = &panders->anders().getSpecAssumptions();
    pcp = &panders->anders().getConstraintPass();
  } else if (auto pcsa = getAnalysisIfAvailable<SpecAndersCS>()) {
    llvm::dbgs() << "Have cs anders ptsto\n";
    passumptions = &pcsa->getSpecAssumptions();
    pcp = &pcsa->getConstraintPass();
  } else {
    llvm_unreachable("Don't have valid AA?\n");
  }
  // llvm::dbgs() << "Have " << assumptions.size() << " assumptions\n";
  auto &cp = *pcp;

  auto cg = cp.getCG();
  auto &map = cg.vals();
  auto &ext_info = cg.extInfo();

  std::vector<llvm::Function *> orig_fcns;
  for (auto &fcn : m) {
    orig_fcns.push_back(&fcn);
  }

  // Okay, now that we have the analysis we need to instrument all of the ptsto
  //   operations

  // First thing, we need to make a map of all frees (and returns) to all
  //   possible deallocated objects

  // **This is a mapping of allocation site to all possible free sites
  free_location_multimap free_locs = findFreeLocs(m, uf, indir, cg, aa);

  // Woot, I got my free set... that was exhausting
  //
  // Now, for each assumption, do instrumentation
  // ALSO: grab a measure of how much it really costs... ya know, for good
  //    measure
  // First, get all assumptions for SpecSFS

  if (auto pcsa = getAnalysisIfAvailable<SpecAndersCS>()) {
    // If we have cs analysis, add callstack checks
    addCallstackChecks(m, *pcsa);
  }
  // llvm::dbgs() << "Have " << assumptions.size() << " assumptions\n";

  // Now, get all of the InstrumentationSites from all of the assumptions
  std::vector<std::unique_ptr<InstrumentationSite>> insts;
  SetCache set_cache;

  for (auto &passumption : *passumptions) {
    auto asmp_insts = passumption->getInstrumentation(map, m, free_locs,
        set_cache);

    /*
    std::move(std::begin(asmp_insts), std::end(asmp_insts),
        std::back_inserter(insts));
    */
    for (auto &pinst : asmp_insts) {
      insts.emplace_back(std::move(pinst));
    }
  }

  auto dedup_fcn = [] (const std::unique_ptr<InstrumentationSite> &lhs,
      const std::unique_ptr<InstrumentationSite> &rhs) {
    assert(lhs != nullptr);
    assert(rhs != nullptr);
    auto &lhs_is = *(lhs.get());
    auto &rhs_is = *(rhs.get());
    return lhs_is < rhs_is;
  };

  auto dedup_uni_fcn = [] (const std::unique_ptr<InstrumentationSite> &lhs,
      const std::unique_ptr<InstrumentationSite> &rhs) {
    auto &lhs_is = *lhs;
    auto &rhs_is = *rhs;
    return lhs_is == rhs_is;
  };

  // Now that we have all elements in insts, we should dedup the entries

  /*
  llvm::dbgs() << "that's " << insts.size() << " instrumentation sites "
    "(pre dedup)\n";

  llvm::dbgs() << "Instrumentation is:\n";
  for (auto &pinst : insts) {
    llvm::dbgs() << "  " << *pinst;
  }
  */

  std::stable_sort(std::begin(insts), std::end(insts), dedup_fcn);
  auto it = std::unique(std::begin(insts), std::end(insts), dedup_uni_fcn);
  insts.erase(it, std::end(insts));

  /*
  llvm::dbgs() << "that's " << insts.size() << " instrumentation sites "
    "(post dedup)\n";

  llvm::dbgs() << "New Instrumentation is:\n";
  for (auto &pinst : insts) {
    llvm::dbgs() << "  " << *pinst;
  }
  */

  bool ret = false;
  for (auto &pinst : insts) {
    ret |= pinst->doInstrument(m, ext_info);
  }


  {
    auto i8_ptr_type = llvm::PointerType::get(
        llvm::IntegerType::get(m.getContext(), 8), 0);
    auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
    auto i64_type = llvm::IntegerType::get(m.getContext(), 64);

    auto main_fcn = m.getFunction("main");
    auto malloc_fcn = getAllocFunction(m);
    auto &insert_pos = *std::begin(main_fcn->getEntryBlock());
    for (auto fcn : orig_fcns) {
      if (isGiriCall(fcn)) {
        continue;
      }
      for (auto fcn_id : map.getIds(fcn)) {
        // Can't do indir call to intrinsic?
        if (!fcn->isIntrinsic() && set_cache.gvUsed(fcn_id)) {
          llvm::dbgs() << "Have used gv: " << fcn->getName() << "\n";
          // Cast the fcn to an i8ptr
          std::vector<llvm::Value *> args;
          // The object value
          args.push_back(llvm::ConstantInt::get(i32_type,
                static_cast<int32_t>(fcn_id)));
          // The ptr type
          args.push_back(llvm::ConstantExpr::getBitCast(fcn, i8_ptr_type));
          // The size:
          args.push_back(llvm::ConstantInt::get(i64_type, PtrSizeBytes));
          // The call
          llvm::CallInst::Create(malloc_fcn, args, "", &insert_pos);
        }

        if (set_cache.hasRet(fcn)) {
          // Need to add a call for this fcn:
          auto call_fcn = getCallFunction(m);

          auto &first_inst = *std::begin(fcn->getEntryBlock());

          // Add the call:
          std::vector<llvm::Value *> args;
          llvm::CallInst::Create(call_fcn, args, "", &first_inst);
        }
      }
    }
  }

  // Now handle the global variables...
  {
    auto i8_ptr_type = llvm::PointerType::get(
        llvm::IntegerType::get(m.getContext(), 8), 0);
    auto i32_type = llvm::IntegerType::get(m.getContext(), 32);

    // Get the alloc fcn
    auto malloc_fcn = getAllocFunction(m);

    // Get the instruction to insert before
    auto main_fcn = m.getFunction("main");
    auto &first_inst = *std::begin(main_fcn->getEntryBlock());

    // For each global init:
    std::for_each(m.global_begin(), m.global_end(),
        [&map, &malloc_fcn, &m, &first_inst,
          &i32_type, &i8_ptr_type, &set_cache]
        (llvm::Value &glbl) {
      // Get the obj from the return value
      auto obj_id = map.getDef(&glbl);

      if (set_cache.gvUsed(obj_id)) {
        // Get the arg_pos for the size from the function
        // llvm::dbgs() << "glbl type is: " << *glbl.getType() << "\n";
        auto type = glbl.getType();
        assert(llvm::isa<llvm::PointerType>(type));
        // Strip pointer type:
        type = type->getContainedType(0);
        // llvm::dbgs() << "passed type is: " << *type << "\n";
        auto size_val = LLVMHelper::calcTypeOffset(m,
            type, &first_inst);

        // Make the call
        std::vector<llvm::Value *> args;
        args.push_back(llvm::ConstantInt::get(i32_type, obj_id.val()));
        args.push_back(llvm::ConstantExpr::getBitCast(
              cast<llvm::Constant>(&glbl), i8_ptr_type));
        args.push_back(size_val);
        llvm::CallInst::Create(malloc_fcn, args, "", &first_inst);
      }
    });
  }

  // AND instrumentation for main's args...
  // UGH... again
  // Add main instrumentation call to beginning of main
  //   Need to pass it argv and arvobj values...
  {
    auto i8_ptr_type = llvm::PointerType::get(
        llvm::IntegerType::get(m.getContext(), 8), 0);
    auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
    auto void_type = llvm::Type::getVoidTy(m.getContext());

    auto main_fcn = m.getFunction("main");
    // Create the main functions...
    // MainInit2 {{{
    {
      // Create the args
      std::vector<llvm::Type *> main2_type_args;
      main2_type_args.push_back(i32_type);
      main2_type_args.push_back(i32_type);
      main2_type_args.push_back(i32_type);
      main2_type_args.push_back(i8_ptr_type->getPointerTo());
      // Create the function type
      auto main2_fcn_type = llvm::FunctionType::get(
          void_type,
          main2_type_args,
          false);
      // Create the function
      llvm::Function::Create(main2_fcn_type,
          llvm::GlobalValue::ExternalLinkage,
          MainInit2Name, &m);
    }
    //}}}
    // MainInit3 {{{
    {
      // Create the args
      std::vector<llvm::Type *> main3_type_args;
      main3_type_args.push_back(i32_type);
      main3_type_args.push_back(i32_type);
      main3_type_args.push_back(i32_type);
      main3_type_args.push_back(i8_ptr_type->getPointerTo());
      main3_type_args.push_back(i8_ptr_type->getPointerTo());
      // Create the function type
      auto main3_fcn_type = llvm::FunctionType::get(
          void_type,
          main3_type_args,
          false);
      // Create the function
      llvm::Function::Create(main3_fcn_type,
          llvm::GlobalValue::ExternalLinkage,
          MainInit3Name, &m);
    }
    //}}}

    auto &insert_pos = *std::begin(main_fcn->getEntryBlock());

    // Now, choose which function to use:
    std::vector<llvm::Value *> args;

    args.push_back(llvm::ConstantInt::get(i32_type,
          static_cast<int32_t>(map.getNamed("argv"))));
    args.push_back(llvm::ConstantInt::get(i32_type,
          static_cast<int32_t>(map.getNamed("arg"))));

    std::for_each(main_fcn->arg_begin(), main_fcn->arg_end(),
        [&args] (llvm::Argument &arg) {
      args.push_back(&arg);
    });


    if (args.size() != 2) {
      llvm::Function *main_init_fcn;

      if (args.size() == 3) {
        llvm_unreachable("Main has 1 arg?");
      } else if (args.size() == 4) {
        main_init_fcn = m.getFunction(MainInit2Name);
      } else if (args.size() == 5) {
        main_init_fcn = m.getFunction(MainInit3Name);
      } else {
        llvm_unreachable("Main has more than 3 args?");
      }

      llvm::CallInst::Create(main_init_fcn, args, "", &insert_pos);
    }
  }

  // Also deal with nullptr:
  {
    auto i8_ptr_type = llvm::PointerType::get(
        llvm::IntegerType::get(m.getContext(), 8), 0);
    auto ce_null = llvm::ConstantPointerNull::get(i8_ptr_type);
    auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
    auto i64_type = llvm::IntegerType::get(m.getContext(), 64);

    auto main_fcn = m.getFunction("main");

    auto malloc_fcn = getAllocFunction(m);

    auto &insert_pos = *std::begin(main_fcn->getEntryBlock());

    std::vector<llvm::Value *> args;
    args.push_back(llvm::ConstantInt::get(i32_type,
          static_cast<int32_t>(ValueMap::NullValue)));
    args.push_back(ce_null);
    args.push_back(llvm::ConstantInt::get(i64_type, 4096));

    llvm::CallInst::Create(malloc_fcn, args, "", &insert_pos);
  }

  return ret;
}

