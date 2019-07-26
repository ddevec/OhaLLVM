/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/lib/DynAlias.h"

#include <cstdio>

#include <fstream>
#include <list>
#include <map>
#include <string>
#include <sstream>
#include <tuple>
#include <vector>

#include "llvm/Pass.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/MathExtras.h"

#include "include/LLVMHelper.h"
#include "include/ExtInfo.h"
#include "include/ModuleAAResults.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/PtsNumberPass.h"

static llvm::cl::opt<std::string>
  DynAliasFilename("dyn-alias-file", llvm::cl::init("dyn_alias.log"),
      llvm::cl::value_desc("filename"),
      llvm::cl::desc("Ptsto file saved/loaded by DynPtsto analysis"));

// First and last functions called
static const std::string InitInstName = "__DynAlias_do_init";
static const std::string FinishInstName = "__DynAlias_do_finish";

// Called to initialize the arguments to main
static const std::string MainInit2Name = "__DynAlias_main_init2";
static const std::string MainInit3Name = "__DynAlias_main_init3";

// Called on alloc/free
static const std::string AllocaInstName = "__DynAlias_do_alloca";
static const std::string CallInstName = "__DynAlias_do_call";
static const std::string RetInstName = "__DynAlias_do_ret";
static const std::string MallocInstName = "__DynAlias_do_malloc";
static const std::string FreeInstName = "__DynAlias_do_free";

// For load/store alias support
static const std::string LoadInstName = "__DynAlias_do_load";
static const std::string StoreInstName = "__DynAlias_do_store";

// setjump/longjmp *sigh*
static const std::string SetjmpInstName = "__DynAlias_do_setjmp";
static const std::string LongjmpInstName = "__DynAlias_do_longjmp";

// For GEPs
// static const std::string GEPInstName = "__DynAlias_do_gep";

// Instrument dyn ptsto info {{{
class InstrDynAlias : public llvm::ModulePass {
 public:
    static char ID;

    InstrDynAlias() : llvm::ModulePass(ID) { }

    bool runOnModule(llvm::Module &m) override;

    void getAnalysisUsage(llvm::AnalysisUsage &au) const override;

 private:
    void setupSpecSFSids(llvm::Module &);
    void addExternalFunctions(llvm::Module &);
    void addInitializationCalls(llvm::Module &);
    llvm::Instruction *addMallocCall(llvm::Module &m, ValueMap::Id obj_id,
        llvm::Value *val, llvm::Value *size_val,
        llvm::Instruction *insert_before);

    ValueMap map_;
    const ExtLibInfo *extInfo_;
};

void InstrDynAlias::getAnalysisUsage(llvm::AnalysisUsage &au) const {
  au.addRequired<UnusedFunctions>();
  au.addRequired<PtsNumberPass>();
  // au.addRequired<SpecAnders>();
  au.setPreservesAll();
}

void InstrDynAlias::setupSpecSFSids(llvm::Module &) {
  // Get the ids from the constraint pass
  const auto &num_pass = getAnalysis<PtsNumberPass>();
  map_ = num_pass.vals();

  extInfo_ = &num_pass.extInfo();
}

bool InstrDynAlias::runOnModule(llvm::Module &m) {
  auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
  auto i64_type = llvm::IntegerType::get(m.getContext(), 64);
  auto i8_ptr_type = llvm::PointerType::get(
      llvm::IntegerType::get(m.getContext(), 8), 0);

  // Okay, we identify all allocations:
  //   Static allocations (alloca instrs)
  //   Dynamic allcoations (use Andersens.h for this?)
  // We also need to identify frees:
  //   Return calls
  //   free calls (add to Andersens.h?)

  // Setup Value ids using the ConstraintPass identifiers...
  setupSpecSFSids(m);
  ValueMap &map = map_;

  // Notify module of external functions
  addExternalFunctions(m);

  // int32_t gep_id = 0;

  // Iterate each instruction, keeping lists
  for (auto &fcn : m) {
    // Ignore functions without bodies
    if (fcn.isDeclaration() || fcn.isIntrinsic()) {
      continue;
    }


    int32_t fcn_num_allocas = 0;
    std::vector<llvm::Instruction *> ret_list;

    // FIXME: Need to support context swap!  setcontext swapcontext and
    //    longjmp, siglongjmp...
    // Means I also need to associate contexts...
    //    getcontext swapcontext setjmp, sigsetjmp

    for (auto &bb : fcn) {
      // Create list to hold all malloc/free Value*s that needs instrumenting
      // within this function
      std::vector<llvm::Instruction *> alloca_list;
      std::vector<llvm::Instruction *> setjmp_list;
      std::vector<llvm::Instruction *> jmp_list;
      std::vector<llvm::CallInst *> call_list;
      std::vector<llvm::GetElementPtrInst *> gep_list;

      std::vector<llvm::CallInst *> ext_list;

      std::vector<llvm::Instruction *> load_list;
      std::vector<llvm::Instruction *> store_list;

      // Also create list for all pointer values
      std::vector<llvm::Instruction *> pointer_list;
      std::list<llvm::Instruction *> phi_list;

      // Don't instrument malloc functions!
      auto &ext_info = extInfo_->getInfo(&fcn);
      if (ext_info.canAlloc()) {
        continue;
      }

      for (auto &inst : bb) {
        // Add stack allocation
        if (llvm::isa<llvm::AllocaInst>(&inst)) {
          if (llvm::isa<llvm::PointerType>(inst.getType())) {
            fcn_num_allocas++;
            alloca_list.push_back(&inst);
          }
        // Possible alloc/dealloc or setjmp/longjmp
        } else if (auto ci = dyn_cast<llvm::CallInst>(&inst)) {
          auto fcn = LLVMHelper::getFcnFromCall(ci);

          // FIXME: Use andersens results on nullptr???
          if (fcn != nullptr) {
            auto &info = extInfo_->getInfo(fcn);

            if (!extInfo_->isUnknownFunction(info)) {
              ext_list.push_back(ci);
            }

            // Also check for setjmp/longjmp
            if (fcn->getName() == "__sigsetjmp" ||
                fcn->getName() == "__setjmp") {
              setjmp_list.push_back(&inst);
            }
            if (fcn->getName() == "longjmp" ||
                fcn->getName() == "siglongjmp") {
              jmp_list.push_back(&inst);
            }
          // If fcn is unknown:
          } else {
            call_list.push_back(ci);
          }
        // Add stack deallocation
        } else if (llvm::isa<llvm::ReturnInst>(&inst)) {
          ret_list.push_back(&inst);
        } else if (llvm::isa<llvm::LoadInst>(&inst)) {
          load_list.push_back(&inst);
        } else if (llvm::isa<llvm::StoreInst>(&inst)) {
          store_list.push_back(&inst);
        }

        // Grab ptsto from return
        if (llvm::isa<llvm::PointerType>(inst.getType())) {
          // Deal w/ phi nodes... meh
          if (llvm::isa<llvm::PHINode>(inst)) {
            phi_list.push_front(&inst);
          } else {
            pointer_list.push_back(&inst);
          }
        }

        if (auto gep = dyn_cast<llvm::GetElementPtrInst>(&inst)) {
          // Only add the gep if it is from a structure, and has a known type
          gep_list.push_back(gep);
        }
      }

      // Determine the first non-alloc of the function
      /*
      llvm::Instruction *alloca_insert_start = nullptr;
      for (auto &insn : fcn.getEntryBlock()) {
        if (!llvm::isa<llvm::AllocaInst>(insn)) {
          alloca_insert_start = &insn;
          break;
        }
      }
      */

      // Add instrumentation calls:
      // First, deal w/ the phi nodes (meh)
      // Find the first non-phi of the bb:
      // Get the external function
      // auto visit_fcn = m.getFunction(VisitInstName);

      /*
      auto inst_it = std::begin(bb);
      llvm::Instruction *inst = &(*inst_it);

      while (llvm::isa<llvm::PHINode>(inst_it) && inst_it != std::end(bb)) {
        ++inst_it;
        inst = &(*inst_it);
      }
      */

      // for allocas
      // First get the external function
      auto alloc_fcn = m.getFunction(AllocaInstName);
      // Then, call for each alloc
      for (auto val : alloca_list) {
        auto ai = cast<llvm::AllocaInst>(val);
        // The id is the objid from the omap
        auto obj_id = map.getDef(val);
        /*
        llvm::dbgs() << "val: " << ValPrinter(val) << " returns def: " << obj_id
          << "\n";
        */

        // Insert for static alloca's in the functions entry BB before the first
        //    non-alloca inst
        // llvm::Instruction *insert_pos = alloca_insert_start;
        // If this isn't a static alloca, do instrumentation before it
        // if (!ai->isStaticAlloca()) {
        llvm::Instruction *insert_pos = ai;
        // }
        // The address is returned from the alloc
        // The size is gotten from the alloc...
        //   sizeof(type) * arraysize
        // First, type, then type size
        auto type_size_ce = LLVMHelper::calcTypeOffset(m,
            ai->getAllocatedType(), insert_pos);

        // Then, get arraysize from the instruction
        auto array_size_val = ai->getArraySize();

        // Convert to int64_t...
        array_size_val = new llvm::SExtInst(array_size_val, i64_type, "",
            insert_pos);

        // Add the mult inst?...
        auto total_size_val =
          llvm::BinaryOperator::Create(llvm::Instruction::Mul, type_size_ce,
            array_size_val, "", insert_pos);

        auto i8_ptr_val = new llvm::BitCastInst(val, i8_ptr_type);
        i8_ptr_val->insertAfter(ai);
        // pass the final result to the function
        // Make the call
        std::vector<llvm::Value *> args;
        args.push_back(llvm::ConstantInt::get(i32_type, obj_id.val()));
        args.push_back(total_size_val);
        args.push_back(i8_ptr_val);
        auto call_insn = llvm::CallInst::Create(alloc_fcn, args);
        call_insn->insertAfter(i8_ptr_val);
      }

      // Used to identify jump locations for debugging
      static int32_t jumpcnt = 0;
      auto jmp_fcn = m.getFunction(LongjmpInstName);
      for (auto val : jmp_list) {
        auto ci = cast<llvm::CallInst>(val);

        // Get the arg_pos for the object being freed
        auto jmpvar = ci->getOperand(0);
        auto i8_ptr_val = jmpvar;
        if (jmpvar->getType() != i8_ptr_type) {
          // Add bitcast
          i8_ptr_val = new llvm::BitCastInst(jmpvar, i8_ptr_type, "", ci);
        }

        // Call the instrumentation, before calling free
        std::vector<llvm::Value *> args;
        args.push_back(llvm::ConstantInt::get(i32_type, jumpcnt));
        jumpcnt++;
        args.push_back(i8_ptr_val);
        llvm::CallInst::Create(jmp_fcn,
            args, "", val);
      }

      auto setjmp_fcn = m.getFunction(SetjmpInstName);
      for (auto val : setjmp_list) {
        auto ci = cast<llvm::CallInst>(val);

        // Get the arg_pos for the object being freed
        auto jmpvar = ci->getOperand(0);
        auto i8_ptr_val = jmpvar;
        if (jmpvar->getType() != i8_ptr_type) {
          // Add bitcast
          i8_ptr_val = new llvm::BitCastInst(jmpvar, i8_ptr_type, "", ci);
        }
        // Call the instrumentation, before calling free
        std::vector<llvm::Value *> args;
        args.push_back(llvm::ConstantInt::get(i32_type, jumpcnt));
        jumpcnt++;
        args.push_back(i8_ptr_val);
        llvm::CallInst::Create(setjmp_fcn,
            args, "", val);
      }

      auto free_fcn = m.getFunction(FreeInstName);
      auto malloc_fcn = m.getFunction(MallocInstName);
      for (auto ci : ext_list) {
        // Get the callsite from the inst
        llvm::CallSite cs(ci);

        // Check the extinfo for each ci in the extlist
        auto &ext_info = extInfo_->getInfo(cs);


        llvm::Instruction *ia = ci;
        // Check for free info first
        auto free_info = ext_info.getFreeData(m, cs, map, &ia);

        // Do any freeing
        for (auto free_value : free_info) {
          auto i8_ptr_val = free_value;
          // Call the instrumentation, before calling free
          if (i8_ptr_val->getType() != i8_ptr_type) {
            i8_ptr_val = new llvm::BitCastInst(i8_ptr_val, i8_ptr_type, "", ci);
          }

          std::vector<llvm::Value *> args = { i8_ptr_val };
          llvm::CallInst::Create(free_fcn,
              args, "", ci);
        }

        // Check for alloc info
        auto alloc_info = ext_info.getAllocData(m, cs, map, &ia);

        for (auto &ai : alloc_info) {
          // Figure out if this is a static or non-static allocation
          auto obj_id = std::get<2>(ai);

          // if its non-static, use the object allocated at the ci
          if (obj_id == ValueMap::Id::invalid()) {
            // Make sure we have an i8*
            obj_id = map.getDef(ci);
            /*
            llvm::dbgs() << "val: " << ValPrinter(ci) << " returns def: "
              << obj_id << "\n";
            */
          }

          // Make sure we're passing an i8* to free
          llvm::Value *i8_ptr_val = std::get<0>(ai);
          if (i8_ptr_val->getType() != i8_ptr_type) {
            auto new_i8_ptr_val =
              new llvm::BitCastInst(i8_ptr_val, i8_ptr_type);
            new_i8_ptr_val->insertAfter(ia);
            ia = new_i8_ptr_val;
            i8_ptr_val = new_i8_ptr_val;
          }

          std::vector<llvm::Value *> args = {
            llvm::ConstantInt::get(i32_type, obj_id.val()),
            std::get<1>(ai),
            i8_ptr_val };
          auto malloc_inst_call = llvm::CallInst::Create(
              malloc_fcn, args);
          malloc_inst_call->insertAfter(ia);
          ia = malloc_inst_call;
        }
      }

      // Loads and stores...
      auto load_fcn = m.getFunction(LoadInstName);
      for (auto pinst : load_list) {
        auto li = cast<llvm::LoadInst>(pinst);

        // Call our load tracker on the load result (the value itself)
        // Also include val_id
        auto ptr = li->getOperand(0);
        auto val_id = map.getDef(li);
        /*
        llvm::dbgs() << "val: " << ValPrinter(li) << " returns def: " << val_id
          << "\n";
        */

        std::vector<llvm::Value *> args;

        auto size = LLVMHelper::calcTypeOffset(m,
            cast<llvm::PointerType>(ptr->getType())->getContainedType(0),
            ptr);

        if (ptr->getType() != i8_ptr_type) {
          ptr = new llvm::BitCastInst(ptr, i8_ptr_type, "", li);
        }


        args.push_back(llvm::ConstantInt::get(i32_type, val_id.val()));
        args.push_back(ptr);
        args.push_back(size);

        // Call our do_load function
        llvm::CallInst::Create(load_fcn,
            args, "", li);
      }

      auto store_fcn = m.getFunction(StoreInstName);
      for (auto pinst : store_list) {
        auto si = cast<llvm::StoreInst>(pinst);

        // Call our load tracker on the load result (the value itself)
        // Also include val_id
        auto ptr = si->getOperand(1);
        auto val_id = map.getDef(si);
        /*
        llvm::dbgs() << "val: " << ValPrinter(si) << " returns def: " << val_id
          << "\n";
        */
        auto size = LLVMHelper::calcTypeOffset(m,
            cast<llvm::PointerType>(ptr->getType())->getContainedType(0),
            ptr);

        std::vector<llvm::Value *> args;

        if (ptr->getType() != i8_ptr_type) {
          ptr = new llvm::BitCastInst(ptr, i8_ptr_type, "", si);
        }

        args.push_back(llvm::ConstantInt::get(i32_type, val_id.val()));
        args.push_back(ptr);
        args.push_back(size);

        // Call our do_load function
        llvm::CallInst::Create(store_fcn,
            args, "", si);
      }


      /*
      // GEPs!
      if (!dyn_ptsto_no_gep) {
        auto gep_fcn = m.getFunction(GEPInstName);
        for (auto &pgep : gep_list) {
          auto &gep = *pgep;

          auto offs = LLVMHelper::getGEPOffs(map, gep);
          // If the offset > 0 AND this ISN'T an array access!
          if (offs > 0 && !LLVMHelper::gepIsArrayAccess(gep)) {
            // Okay, add the gep instruction call....
            llvm::Instruction *i8_ptr_val = pgep;

            std::vector<llvm::Value *> args;
            // First, get the gep offset...
            args.push_back(llvm::ConstantInt::get(i32_type,
                  offs));

            // The base pointer
            auto base_ptr = gep.getOperand(0);
            llvm::Instruction *insert_pos = pgep;

            std::vector<llvm::Value *> indicies;
            for (auto it = gep.idx_begin(), en = gep.idx_end();
                it != en; ++it) {
              indicies.push_back(*it);
            }
            indicies.pop_back();
            indicies.push_back(llvm::ConstantInt::get(i32_type, 0));
            base_ptr =
              llvm::GetElementPtrInst::Create(base_ptr, indicies, "", pgep);

            if (base_ptr->getType() != i8_ptr_type) {
              base_ptr = new llvm::BitCastInst(base_ptr, i8_ptr_type);
              cast<llvm::Instruction>(base_ptr)->insertAfter(insert_pos);
              insert_pos = cast<llvm::Instruction>(base_ptr);
            }
            args.push_back(base_ptr);

            if (gep.getType() != i8_ptr_type) {
              i8_ptr_val = new llvm::BitCastInst(pgep, i8_ptr_type);
              i8_ptr_val->insertAfter(insert_pos);
              insert_pos = cast<llvm::Instruction>(i8_ptr_val);
            }
            // Then, the i8_ptr_val
            args.push_back(i8_ptr_val);

            // Finally, the field size...
            auto type_size_ce = LLVMHelper::calcTypeOffset(m,
                LLVMHelper::getLowestType(pgep->getType()), insert_pos);
            args.push_back(type_size_ce);
            args.push_back(llvm::ConstantInt::get(i32_type, gep_id));
            gep_id++;
            // llvm::dbgs() << "gep_id is now: " << gep_id << "\n";

            auto gep_inst_call = llvm::CallInst::Create(
                gep_fcn, args);
            gep_inst_call->insertAfter(insert_pos);
          }
        }
      }
      */
    }


    // If we have one or more allocs, we need a call and ret pair
    if (fcn_num_allocas > 0) {
      // First, for calls
      // Get external function
      auto call_fcn = m.getFunction(CallInstName);
      std::vector<llvm::Value *> args;
      // NOTE: This should be the first function
      //    (before the alloc instr calls)
      auto &first_insn = *std::begin(fcn.getEntryBlock());
      llvm::CallInst::Create(call_fcn,
          args, "", &first_insn);
      // for rets
      // First, get the external function
      auto ret_fcn = m.getFunction(RetInstName);
      // Then, call for each ret
      for (auto val : ret_list) {
        // No args, just pops the last alloc frame...
        llvm::CallInst::Create(ret_fcn,
            args, "", val);
      }
    }

    // Also, add visits for the args
    // NOTE: Main is handled specially
    if (fcn.getName() != "main") {
      // auto visit_fcn = m.getFunction(VisitInstName);
      /*
      std::for_each(fcn.arg_begin(), fcn.arg_end(),
          [&i8_ptr_type, &i32_type, &omap, &fcn]
          (llvm::Argument &arg) {
        if (llvm::isa<llvm::PointerType>(arg.getType())) {
          // The return value is the val
          auto val_id = omap.getValue(&arg);
          auto &ins_pos = *llvm::inst_begin(fcn);

          // Make the call
          auto i8_ptr_val = new llvm::BitCastInst(&arg, i8_ptr_type);
          i8_ptr_val->insertBefore(&ins_pos);

          std::vector<llvm::Value *> args;
          args.push_back(llvm::ConstantInt::get(i32_type, val_id.val()));
          args.push_back(i8_ptr_val);
          auto visit_insn = llvm::CallInst::Create(visit_fcn, args);

          visit_insn->insertAfter(i8_ptr_val);
        }
      });
      */
    }
  }

  // Add global initializers for function pointers
  // AND deal with argc & argv
  {
    auto malloc_fcn = m.getFunction(MallocInstName);

    auto main_fcn = m.getFunction("main");
    auto &first_inst = *std::begin(main_fcn->getEntryBlock());
    for (auto &fcn : m) {
      // Ignore intrinsics
      if (fcn.isIntrinsic()) {
        continue;
      }
      // Get the obj from the function value
      auto obj_id = map.getDef(&fcn);
      /*
      llvm::dbgs() << "val: " << ValPrinter(&fcn) << " returns def: " << obj_id
        << "\n";
      */

      // Get an i8_ptr from the function
      auto i8_ptr_val = new llvm::BitCastInst(&fcn, i8_ptr_type, "",
        &first_inst);

      // calc the size of a pointer
      auto size_val = LLVMHelper::calcTypeOffset(m,
          i8_ptr_type, &first_inst);

      // Make the call
      std::vector<llvm::Value *> args;
      args.push_back(llvm::ConstantInt::get(i32_type, obj_id.val()));
      args.push_back(size_val);
      args.push_back(i8_ptr_val);
      llvm::CallInst::Create(malloc_fcn, args, "", &first_inst);
    }
  }

  // Now, add global initializers to the beignning of main
  {
    // Get the external function
    auto malloc_fcn = m.getFunction(MallocInstName);

    auto main_fcn = m.getFunction("main");
    auto &first_inst = *std::begin(main_fcn->getEntryBlock());

    // For each global init:
    std::for_each(m.global_begin(), m.global_end(),
        [&map, &malloc_fcn, &m, &first_inst,
          &i32_type, &i8_ptr_type]
        (llvm::Value &glbl) {
      // Get the obj from the return value
      auto obj_id = map.getDef(&glbl);
      /*
      llvm::dbgs() << "val: " << ValPrinter(&glbl) << " returns def: " << obj_id
        << "\n";
      */

      // Get the arg_pos for the size from the function
      // llvm::dbgs() << "glbl type is: " << *glbl.getType() << "\n";
      auto type = glbl.getType();
      assert(llvm::isa<llvm::PointerType>(type));
      // Strip pointer type:
      type = type->getContainedType(0);
      // llvm::dbgs() << "passed type is: " << *type << "\n";
      auto size_val = LLVMHelper::calcTypeOffset(m,
          type, &first_inst);

      auto i8_ptr_val = new llvm::BitCastInst(&glbl, i8_ptr_type, "",
        &first_inst);

      // Make the call
      std::vector<llvm::Value *> args;
      args.push_back(llvm::ConstantInt::get(i32_type, obj_id.val()));
      args.push_back(size_val);
      args.push_back(i8_ptr_val);
      llvm::CallInst::Create(malloc_fcn, args, "", &first_inst);
    });
  }

  // Add initialization calls:
  addInitializationCalls(m);

  // We modify all the stuff
  return true;
}

// Adding calls {{{
void InstrDynAlias::addExternalFunctions(llvm::Module &m) {
  auto void_type = llvm::Type::getVoidTy(m.getContext());
  auto i8_ptr_type = llvm::PointerType::get(
      llvm::IntegerType::get(m.getContext(), 8), 0);
  auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
  auto i64_type = llvm::IntegerType::get(m.getContext(), 64);
  // Create external linkages for:
  // AllocaInst(i32 obj_id, i64 size, i8 *ret)
  {
    // Create the args
    std::vector<llvm::Type *> alloc_fcn_type_args;
    alloc_fcn_type_args.push_back(i32_type);
    alloc_fcn_type_args.push_back(i64_type);
    alloc_fcn_type_args.push_back(i8_ptr_type);
    // Create the function type
    auto alloc_fcn_type = llvm::FunctionType::get(
        void_type,
        alloc_fcn_type_args,
        false);
    // Create the function
    llvm::Function::Create(alloc_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        AllocaInstName, &m);
  }

  // CallInst(void)
  {
    // Create the args
    std::vector<llvm::Type *> call_fcn_type_args;
    // Create the function type
    auto call_fcn_type = llvm::FunctionType::get(
        void_type,
        call_fcn_type_args,
        false);
    // Create the function
    llvm::Function::Create(call_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        CallInstName, &m);
  }

  // RetInst(void)
  {
    // Create the args
    std::vector<llvm::Type *> ret_fcn_type_args;
    // Create the function type
    auto ret_fcn_type = llvm::FunctionType::get(
        void_type,
        ret_fcn_type_args,
        false);
    // Create the function
    llvm::Function::Create(ret_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        RetInstName, &m);
  }

  // MallocInst(i32 obj_id, i64 size, i8 *ret)
  {
    // Create the args
    std::vector<llvm::Type *> malloc_fcn_type_args;
    malloc_fcn_type_args.push_back(i32_type);
    malloc_fcn_type_args.push_back(i64_type);
    malloc_fcn_type_args.push_back(i8_ptr_type);
    // Create the function type
    auto malloc_fcn_type = llvm::FunctionType::get(
        void_type,
        malloc_fcn_type_args,
        false);
    // Create the function
    llvm::Function::Create(malloc_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        MallocInstName, &m);
  }

  // FreeInst(i8 *ptr)
  {
    // Create the args
    std::vector<llvm::Type *> free_fcn_type_args;
    free_fcn_type_args.push_back(i8_ptr_type);
    // Create the function type
    auto free_fcn_type = llvm::FunctionType::get(
        void_type,
        free_fcn_type_args,
        false);
    // Create the function
    llvm::Function::Create(free_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        FreeInstName, &m);
  }

  // SetjmpInst(i8 *ptr)
  {
    // Create the args
    std::vector<llvm::Type *> setjmp_fcn_type_args;
    setjmp_fcn_type_args.push_back(i32_type);
    setjmp_fcn_type_args.push_back(i8_ptr_type);
    // Create the function type
    auto setjmp_fcn_type = llvm::FunctionType::get(
        void_type,
        setjmp_fcn_type_args,
        false);
    // Create the function
    llvm::Function::Create(setjmp_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        SetjmpInstName, &m);
  }

  // LongjmpInst(i8 *ptr)
  {
    // Create the args
    std::vector<llvm::Type *> longjmp_fcn_type_args;
    longjmp_fcn_type_args.push_back(i32_type);
    longjmp_fcn_type_args.push_back(i8_ptr_type);
    // Create the function type
    auto longjmp_fcn_type = llvm::FunctionType::get(
        void_type,
        longjmp_fcn_type_args,
        false);
    // Create the function
    llvm::Function::Create(longjmp_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        LongjmpInstName, &m);
  }

  // GEPInst(int32_t field_offs, i8 *ptr, int32_t size)
  /*
  {
    // Create the args
    std::vector<llvm::Type *> gep_fcn_type_args;
    gep_fcn_type_args.push_back(i32_type);
    gep_fcn_type_args.push_back(i8_ptr_type);
    gep_fcn_type_args.push_back(i8_ptr_type);
    gep_fcn_type_args.push_back(i64_type);
    gep_fcn_type_args.push_back(i32_type);
    // Create the function type
    auto gep_fcn_type = llvm::FunctionType::get(
        void_type,
        gep_fcn_type_args,
        false);
    // Create the function
    llvm::Function::Create(gep_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        GEPInstName, &m);
  }
  */

  // StoreInst(i32 val_id, i8 *ptr, i32 size)
  {
    // Create the args
    std::vector<llvm::Type *> store_fcn_type_args;
    store_fcn_type_args.push_back(i32_type);
    store_fcn_type_args.push_back(i8_ptr_type);
    store_fcn_type_args.push_back(i64_type);
    // Create the function type
    auto store_fcn_type = llvm::FunctionType::get(
        void_type,
        store_fcn_type_args,
        false);
    // Create the function
    llvm::Function::Create(store_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        StoreInstName, &m);
  }

  // LoadInst(i32 val_id, i8 *ptr, i32 size)
  {
    // Create the args
    std::vector<llvm::Type *> load_fcn_type_args;
    load_fcn_type_args.push_back(i32_type);
    load_fcn_type_args.push_back(i8_ptr_type);
    load_fcn_type_args.push_back(i64_type);
    // Create the function type
    auto load_fcn_type = llvm::FunctionType::get(
        void_type,
        load_fcn_type_args,
        false);
    // Create the function
    llvm::Function::Create(load_fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        LoadInstName, &m);
  }

  // InitMainArgs2(i32 argc, char **argv)
  {
    // Create the args
    std::vector<llvm::Type *> main2_type_args;
    main2_type_args.push_back(i32_type);
    main2_type_args.push_back(i32_type);
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

  // InitMainArgs3(i32 argv_id, i32 argv_obj_id, i32 envp_id,
  //      i32 env_id, char **argv, char **envp)
  {
    // Create the args
    std::vector<llvm::Type *> main3_type_args;
    main3_type_args.push_back(i32_type);
    main3_type_args.push_back(i32_type);
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
}

void InstrDynAlias::addInitializationCalls(llvm::Module &m) {
  // Var types
  auto void_type = llvm::Type::getVoidTy(m.getContext());
  auto i64_type = llvm::IntegerType::get(m.getContext(), 64);

  // Function types
  std::vector<llvm::Type *> type_no_args;
  auto void_fcn_type = llvm::FunctionType::get(
      void_type,
      type_no_args,
      false);

  auto ptr_void_fcn_type = void_fcn_type->getPointerTo();

  // Create the init/finish functions
  auto init_fcn = llvm::Function::Create(void_fcn_type,
      llvm::GlobalValue::ExternalLinkage,
      InitInstName, &m);
  auto finish_fcn = llvm::Function::Create(void_fcn_type,
      llvm::GlobalValue::ExternalLinkage,
      FinishInstName, &m);

  auto main_fcn = m.getFunction("main");

  // get the first instruction
  auto first_inst = &(*inst_begin(main_fcn));

  // While we're at it, we're going to add the args to main to our set of
  //   objs...
  {
    auto i8_type = llvm::IntegerType::get(m.getContext(), 8);
    auto i8_ptr_type = llvm::PointerType::get(i8_type, 0);
    auto ce_null = llvm::ConstantPointerNull::get(i8_ptr_type);

    // Do one for IntValue
    first_inst = addMallocCall(m, ValueMap::NullValue, ce_null,
        llvm::ConstantInt::get(i64_type, 4096), first_inst);

    // Deal w/ argc, argv, and envp here
    // Detect number of main args
    std::vector<llvm::Value *> main_args;
    // Set first arg to call to be objid for argvval
    auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
    main_args.push_back(llvm::ConstantInt::get(i32_type,
          map_.getNamed("argv").val()));
    main_args.push_back(llvm::ConstantInt::get(i32_type,
          map_.getNamed("arg").val()));
    main_args.push_back(llvm::ConstantInt::get(i32_type,
          map_.getNamed("envp").val()));
    main_args.push_back(llvm::ConstantInt::get(i32_type,
          map_.getNamed("env").val()));

    std::for_each(main_fcn->arg_begin(), main_fcn->arg_end(),
        [&main_args] (llvm::Argument &arg) {
      main_args.push_back(&arg);
    });

    // Note all main_args size comps are +1 due to the obj_id arg
    if (main_args.size() != 4) {
      llvm::Function *main_init_fcn;

      if (main_args.size() == 5) {
        llvm_unreachable("Main has 1 arg?");
      } else if (main_args.size() == 6) {
        main_init_fcn = m.getFunction(MainInit2Name);
      } else if (main_args.size() == 7) {
        main_init_fcn = m.getFunction(MainInit3Name);
      } else {
        llvm_unreachable("Main has more than 3 args?");
      }

      llvm::CallInst::Create(main_init_fcn, main_args, "", first_inst);
    }
  }

  // get "atexit" function
  // Create the "atexit" type
  std::vector<llvm::Type *> atexit_args;
  atexit_args.push_back(ptr_void_fcn_type);
  auto atexit_type = llvm::FunctionType::get(
      void_type,
      atexit_args,
      false);

  auto at_exit = m.getFunction("atexit");
  if (at_exit == nullptr) {
    at_exit = llvm::Function::Create(
        atexit_type,
        llvm::GlobalValue::ExternalLinkage,
        "atexit", &m);
  }

  // Call our function before the first inst:
  std::vector<llvm::Value *> no_args;
  llvm::CallInst::Create(init_fcn, no_args, "", first_inst);
  // Setup our function to call atexit
  std::vector<llvm::Value *> atexit_call_args;
  atexit_call_args.push_back(finish_fcn);
  llvm::CallInst::Create(at_exit, atexit_call_args, "", first_inst);
}

llvm::Instruction *InstrDynAlias::addMallocCall(llvm::Module &m,
    ValueMap::Id obj_id, llvm::Value *val, llvm::Value *size_val,
    llvm::Instruction *insert_before) {
  // Make the call
  auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
  auto malloc_fcn = m.getFunction(MallocInstName);
  auto i8_ptr_type = llvm::PointerType::get(
      llvm::IntegerType::get(m.getContext(), 8), 0);

  auto i8_ptr_val = new llvm::BitCastInst(val, i8_ptr_type, "", insert_before);

  std::vector<llvm::Value *> args;
  args.push_back(llvm::ConstantInt::get(i32_type, obj_id.val()));
  args.push_back(size_val);
  args.push_back(i8_ptr_val);
  auto ret = llvm::CallInst::Create(
      malloc_fcn, args, "", insert_before);

  assert(insert_before != nullptr);

  return ret;
}
//}}}

char InstrDynAlias::ID = 0;

static llvm::RegisterPass<InstrDynAlias> X("insert-alias-profiling",
    "Instruments pointsto sets, for use with SpecSFS",
    false, false);
//}}}

// The dynamic ptsto pass loader {{{
void DynAliasLoader::getAnalysisUsage(llvm::AnalysisUsage &au) const {
  au.addRequired<PtsNumberPass>();
  au.addRequired<ModuleAAResults>();
  au.setPreservesAll();
}

bool DynAliasLoader::runOnModule(llvm::Module &) {
  // Setup omap:
  const auto &cp = getAnalysis<PtsNumberPass>();
  map_ = cp.vals();

  // Now optimize so its related to spec's

  std::ifstream logfile(DynAliasFilename);
  llvm::dbgs() << "Loading DynAliasFile: " << DynAliasFilename << "\n";
  if (!logfile.is_open()) {
    llvm::dbgs() << "DynAliasLoader: no logfile loaded!\n";
    hasInfo_ = false;
  } else {
    llvm::dbgs() << "DynAliasLoader: Successfully Loaded\n";
    hasInfo_ = true;

    for (std::string line; std::getline(logfile, line, ':'); ) {
      auto call_id = ValueMap::Id(stoi(line));

      auto &obj_set = valToObjs_[call_id];

      std::getline(logfile, line);

      std::stringstream converter(line);

      int32_t obj_int_val;
      converter >> obj_int_val;
      while (!converter.fail()) {
        auto obj_id = ValueMap::Id(obj_int_val);

        // If we have a universal value, we don't maintain dyn ptsto constraints
        //   for this variable
        if (obj_id == ValueMap::UniversalValue) {
          obj_id = ValueMap::Id::invalid();
        }

        // Don't add a ptsto for null value
        if (obj_id != ValueMap::NullValue) {
          obj_set.insert(obj_id);
        }


        converter >> obj_int_val;
      }
    }

    /*
    if (print_dyn_ptsto) {
      int64_t total_variables = 0;
      int64_t total_ptstos = 0;

      int32_t num_objects[10] = {};

      size_t max_objects = 0;
      int32_t num_max = 0;

      for (auto &pr : valToObjs_) {
        auto &ptsto = pr.second;
        auto ptsto_size = ptsto.count();
        total_variables++;
        total_ptstos += ptsto_size;

        if (ptsto_size < 10) {
          num_objects[ptsto_size]++;
        }

        if (ptsto_size > max_objects) {
          max_objects = ptsto_size;
          num_max = 0;
        }

        if (ptsto_size == max_objects) {
          num_max++;
        }
      }

      llvm::dbgs() << "Number tracked values: " << total_variables << "\n";
      llvm::dbgs() << "Number tracked ptstos: " << total_ptstos << "\n";

      llvm::dbgs() << "Max ptsto is: " << max_objects << ", with num_max: " <<
        num_max << "\n";

      llvm::dbgs() << "lowest ptsto counts:\n";
      for (int i = 0; i < 10; i++) {
        llvm::dbgs() << "  [" << i << "]:  " << num_objects[i] << "\n";
      }
    }
    */
  }

  return false;
}

char DynAliasLoader::ID = 0;
char DynAliasTester::ID = 0;

void DynAliasTester::getAnalysisUsage(llvm::AnalysisUsage &au) const {
  au.addRequired<ModuleAAResults>();
  au.addRequired<DynAliasLoader>();
  au.addRequired<UnusedFunctions>();

  au.setPreservesAll();
}

bool DynAliasTester::runOnModule(llvm::Module &) {
  // Setup omap:
  dynAA_ = &getAnalysis<DynAliasLoader>();

  auto &aa = getAnalysis<ModuleAAResults>();

  auto &used = getAnalysis<UnusedFunctions>();

  // Now test the load/store aliases for the dynamic alias set

  size_t num_good_load = 0;
  size_t num_load = 0;
  size_t num_good_store = 0;
  size_t num_store = 0;

  for (auto pr : *dynAA_) {
    auto load_id = pr.first;
    auto &store_set = pr.second;
    num_load++;

    if (load_id == ValueMap::Id::invalid()) {
      continue;
    }

    auto load_val = dynAA_->valueAtID(load_id);
    auto li = dyn_cast_or_null<llvm::LoadInst>(load_val);
    if (li == nullptr) {
      llvm::dbgs() << "WARNING: load inst without load value?: " << load_id <<
        " " << FullValPrint(load_id, dynAA_->map()) << "\n";
      continue;
    }

    if (!used.isUsed(li->getParent())) {
      llvm::dbgs() << "WARNING: Unused load inst? " << ValPrinter(li) << "\n";
      continue;
    }

    num_good_load++;
    auto load_src = li->getOperand(0);

    for (auto store_id : store_set) {
      if (store_id == ValueMap::Id::invalid() ||
          store_id == ValueMap::Id(0)) {
        continue;
      }

      num_store++;
      auto store_val = dynAA_->valueAtID(store_id);

      // The load_val should be a load instruction
      // The store val should be a store instruction
      auto si = dyn_cast_or_null<llvm::StoreInst>(store_val);
      if (si == nullptr) {
        llvm::dbgs() << "WARNING: store inst without store value?: " <<
          store_id << FullValPrint(store_id, dynAA_->map()) << "\n";
        continue;
      }

      if (!used.isUsed(si->getParent())) {
        llvm::dbgs() << "WARNING: Unused store inst? " <<
          ValPrinter(si) << "\n";
        continue;
      }
      num_good_store++;
      auto store_dest = si->getOperand(1);


      // If the store value is an allocation site, we could be dealing with an
      // offset within the site.  In that instance, we need to consider all
      // subfields allocated when asking about an alias...
      // To do so,
      //   First, get a list of all store objects associated with this alloc,
      //   Then,
      /*
      static int32_t i = 0;
      if (i == 2298) {
        llvm::dbgs() << "load is: " << ValPrinter(li) << "\n";
        llvm::dbgs() << "store is: " << ValPrinter(si) << "\n";
      }
      llvm::dbgs() << "alias check : " << i++ << "\n";
      */
      if (aa.alias(llvm::MemoryLocation(load_src),
               llvm::MemoryLocation(store_dest)) ==
          llvm::AliasResult::NoAlias) {
        llvm::dbgs() << "DynAlias found load-store alias not in AA\n";

        llvm::dbgs() << "  Store: " << store_id << ": " <<
          FullValPrint(store_id, dynAA_->map()) << "\n";

        llvm::dbgs() << "  Load: " << load_id << ": " <<
          FullValPrint(load_id, dynAA_->map()) << "\n";
      }
    }
  }

  llvm::dbgs() << "num_load: " << num_load << "\n";
  llvm::dbgs() << "num_good_load: " << num_good_load << "\n";

  llvm::dbgs() << "num_store: " << num_store << "\n";
  llvm::dbgs() << "num_good_store: " << num_good_store << "\n";

  return false;
}

namespace llvm {
static RegisterPass<DynAliasLoader> DynAliasLoadReg("real-dyn-loader",
    "loads dynamic ptsto set info, for use with SpecSFS",
    false, false);
static RegisterPass<DynAliasTester> DynAliasTesterReg("dyn-alias-tester",
    "Tests any previously run AAs for load/store alias sets",
    false, false);
}
// }}}

