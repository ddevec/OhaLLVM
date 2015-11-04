/*
 * Copyright (C) 2015 David Devecsery
 */

#include <algorithm>
#include <string>
#include <vector>

#include "llvm/Pass.h"
#include "llvm/PassSupport.h"
#include "llvm/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ProfileInfo.h"

#include "include/SpecSFS.h"

const int64_t PtrSizeBytes = sizeof(void *);
const int64_t BitsPerByte = 8;
const int64_t PtrSizeBits = PtrSizeBytes * BitsPerByte;

static const std::string MainInit2Name = "__specsfs_main_init2";
static const std::string MainInit3Name = "__specsfs_main_init3";

class SpecSFSInstrumenter : public llvm::ModulePass {
 public:
  static char ID;
  SpecSFSInstrumenter();

  bool runOnModule(llvm::Module &M) override;

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const override;
};

void SpecSFSInstrumenter::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  // Because we're an AliasAnalysis
  usage.setPreservesAll();

  // We don't instrument frees in dead code, so we need to get that here
  usage.addRequired<UnusedFunctions>();

  // We require SpecSFS, to provide assumptions and ObjID->llvm::Value mappings
  usage.addRequired<SpecSFS>();
}

SpecSFSInstrumenter::SpecSFSInstrumenter() : llvm::ModulePass(ID) { }
char SpecSFSInstrumenter::ID = 0;
namespace llvm {
  static RegisterPass<SpecSFSInstrumenter>
      X("specsfs-do-inst", "Speculative Sparse Flow-sensitive Analysis "
          "Speculative checking instrumentation pass", false, false);
}  // namespace llvm


bool SpecSFSInstrumenter::runOnModule(llvm::Module &m) {
  auto &sfs = getAnalysis<SpecSFS>();
  auto &uf = getAnalysis<UnusedFunctions>();
  auto &omap = sfs.getObjectMap();

  // Okay, now that we have the analysis we need to instrument all of the ptsto
  //   operations

  // First thing, we need to make a map of all frees (and returns) to all
  //   possible deallocated objects

  // **This is a mapping of allocation site to all possible free sites
  free_location_multimap free_locs;
  for (auto &fcn : m) {
    std::vector<llvm::Value *> alloc_insts;
    for (auto &bb : fcn) {
      if (uf.isUsed(bb)) {
        // Now lets iterate some instructions
        for (auto &insn : bb) {
          if (llvm::isa<llvm::AllocaInst>(insn)) {
            alloc_insts.push_back(&insn);
          // If this instruction is a ret instruction:
          } else if (llvm::isa<llvm::ReturnInst>(insn)) {
            // Each value stacked prior to this point is freed by this insn
            // AKA: for each insn : alloca_list add to free list
            for (auto alloc_inst : alloc_insts) {
              free_locs.emplace(omap.getObject(alloc_inst),
                  &insn);
            }
          } else if (auto ci = dyn_cast<llvm::CallInst>(&insn)) {
            auto fcn = LLVMHelper::getFcnFromCall(ci);
            if (fcn && AllocInfo::fcnIsFree(fcn)) {
              // Okay, have a free function, add it to our free list
              // First though, i need to get all of the values this may free:
              // The free arg is:
              auto free_arg = AllocInfo::getFreeArg(m, ci, fcn, false);

              llvm::dbgs() << "Found free_fcn call: " << *ci << "\n";

              // Now I figure out what this points to:
              auto pts_set = sfs.getPtstoSet(free_arg);

              // Now, for each pointed to object, I add this ci to the free set
              for (auto obj_id : pts_set) {
                free_locs.emplace(obj_id, ci);
                llvm::dbgs() << "  adding obj_id: " << obj_id << "\n";
              }
            }
          }
        }
      }
    }
  }
  // Woot, I got my free set... that was exhausting
  //
  // Now, for each assumption, do instrumentation
  // ALSO: grab a measure of how much it really costs... ya know, for good
  //    measure
  // First, get all assumptions for SpecSFS
  auto &assumptions = sfs.getSpecAssumptions();
  // llvm::dbgs() << "Have " << assumptions.size() << " assumptions\n";

  // Now, get all of the InstrumentationSites from all of the assumptions
  std::vector<std::unique_ptr<InstrumentationSite>> insts;
  SetCache set_cache;

  for (auto &passumption : assumptions) {
    auto asmp_insts = passumption->getInstrumentation(omap, m, free_locs,
        set_cache);

    std::move(std::begin(asmp_insts), std::end(asmp_insts),
        std::back_inserter(insts));
  }

  auto dedup_fcn = [] (const std::unique_ptr<InstrumentationSite> &lhs,
      const std::unique_ptr<InstrumentationSite> &rhs) {
    auto &lhs_is = *lhs;
    auto &rhs_is = *rhs;
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

  std::sort(std::begin(insts), std::end(insts), dedup_fcn);
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
    ret |= pinst->doInstrument(m);
  }


  // ALSO: Need to add in instrumentation for function calls...
  // UGH: This is harder than I thought... work on this... later
  // For each function in module
  //   Add malloc for function address to beginning of main

  {
    auto i8_ptr_type = llvm::PointerType::get(
        llvm::IntegerType::get(m.getContext(), 8), 0);
    auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
    auto i64_type = llvm::IntegerType::get(m.getContext(), 64);

    auto main_fcn = m.getFunction("main");
    auto malloc_fcn = getAllocFunction(m);
    auto &insert_pos = *std::begin(main_fcn->getEntryBlock());
    for (auto &fcn : m) {
      auto fcn_id = omap.getObject(&fcn);
      // Can't do indir call to intrinsic?
      if (!fcn.isIntrinsic() && set_cache.gvUsed(fcn_id)) {
        // Cast the fcn to an i8ptr
        auto val = omap.getObject(&fcn);
        std::vector<llvm::Value *> args;
        // The object value
        args.push_back(llvm::ConstantInt::get(i32_type, val.val()));
        // The ptr type
        args.push_back(llvm::ConstantExpr::getBitCast(&fcn, i8_ptr_type));
        // The size:
        args.push_back(llvm::ConstantInt::get(i64_type, PtrSizeBits));
        // The call
        llvm::CallInst::Create(malloc_fcn, args, "", &insert_pos);
      }

      if (set_cache.hasRet(&fcn)) {
        // Need to add a call for this fcn:
        auto call_fcn = getCallFunction(m);

        auto &first_inst = *std::begin(fcn.getEntryBlock());

        // Add the call:
        std::vector<llvm::Value *> args;
        llvm::CallInst::Create(call_fcn, args, "", &first_inst);
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
        [&omap, &malloc_fcn, &m, &first_inst,
          &i32_type, &i8_ptr_type, &set_cache]
        (llvm::Value &glbl) {
      // Get the obj from the return value
      auto obj_id = omap.getObject(&glbl);

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
          ObjectMap::ArgvValueObject.val()));
    args.push_back(llvm::ConstantInt::get(i32_type,
          ObjectMap::ArgvObjectObject.val()));

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
          ObjectMap::NullValue.val()));
    args.push_back(ce_null);
    args.push_back(llvm::ConstantInt::get(i64_type, 4096 * BitsPerByte));

    llvm::CallInst::Create(malloc_fcn, args, "", &insert_pos);
  }

  return ret;
}

