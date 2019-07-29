/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/lib/CallContextPass.h"

#include <algorithm>
#include <iostream>
#include <set>
#include <string>
#include <sstream>
#include <vector>

#include "include/util.h"
#include "include/LLVMHelper.h"
#include "include/lib/CsCFG.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

static llvm::cl::opt<std::string>
  DynCallGraphFilename("dyn-calls-file", llvm::cl::init("profile.calls"),
      llvm::cl::value_desc("filename"),
      llvm::cl::desc("Ptsto file saved/loaded by CallContextLoader analysis"));

static const std::string InitInstName = "__DynContext_do_init";
static const std::string FinishInstName = "__DynContext_do_finish";

static const std::string CallInstName = "__DynContext_do_call";
static const std::string RetInstName = "__DynContext_do_ret";

static const std::string SetjmpCallInstName = "__DynContext_do_setjmp_call";
static const std::string SetjmpRetInstName = "__DynContext_do_setjmp_ret";

static const std::string LongjmpInstName = "__DynContext_do_longjmp_call";

class CallContextInst : public llvm::ModulePass {
 public:
  static char ID;
  CallContextInst();

  virtual bool runOnModule(llvm::Module &m);

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  llvm::StringRef getPassName() const override {
    return "CallContextInst";
  }

 private:
  void setupGlobals(llvm::Module &m);
  void setupTypes(llvm::Module &m);

  llvm::Function *callFcn_;
  llvm::Function *retFcn_;

  llvm::Function *setjmpCallFcn_;
  // llvm::Function *setjmpRetFcn_;
  llvm::Function *longjmpFcn_;

  llvm::Type *voidType_;
  llvm::Type *i8Type_;
  llvm::Type *i8PtrType_;
  llvm::Type *i32Type_;
  llvm::Type *i64Type_;
};

char CallContextInst::ID = 0;
CallContextInst::CallContextInst() : llvm::ModulePass(ID) { }

namespace llvm {
static RegisterPass<CallContextInst> bX("insert-callstack-profiling",
    "Instruments callsites, for use with StaticSlicer",
    false, false);
}  // namespace llvm


void CallContextInst::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  // Analysis that handles indirect function targets...
  usage.addRequired<CsCFG>();

  // Unused Function Info
  usage.addRequired<UnusedFunctions>();

  // EOM
  usage.setPreservesAll();
}

void CallContextInst::setupTypes(llvm::Module &m) {
  voidType_ = llvm::Type::getVoidTy(m.getContext());
  i8Type_ = llvm::IntegerType::get(m.getContext(), 8);
  i32Type_ = llvm::IntegerType::get(m.getContext(), 32);
  i64Type_ = llvm::IntegerType::get(m.getContext(), 64);
  i8PtrType_ = llvm::PointerType::get(i8Type_, 0);
}

void CallContextInst::setupGlobals(llvm::Module &m) {
  std::vector<llvm::Type *> type_no_args = { };
  auto void_fcn_type = llvm::FunctionType::get(
      voidType_, type_no_args, false);

  std::vector<llvm::Type *> type_i32_args = { i32Type_ };
  auto i32_fcn_type = llvm::FunctionType::get(
      voidType_, type_i32_args, false);

  std::vector<llvm::Type *> type_i32_i8p_args = { i32Type_, i8PtrType_ };
  auto i32_i8p_fcn_type = llvm::FunctionType::get(
      voidType_, type_i32_i8p_args, false);

  callFcn_ = LLVMHelper::getOrCreateLibFcn(m, CallInstName,
      i32_fcn_type);
  retFcn_ = LLVMHelper::getOrCreateLibFcn(m, RetInstName,
      i32_fcn_type);
  setjmpCallFcn_ = LLVMHelper::getOrCreateLibFcn(m, SetjmpCallInstName,
      i32_i8p_fcn_type);
  longjmpFcn_ = LLVMHelper::getOrCreateLibFcn(m, LongjmpInstName,
      i32_i8p_fcn_type);

  auto entry_fcn = LLVMHelper::getOrCreateLibFcn(m, InitInstName,
      void_fcn_type);
  auto exit_fcn = LLVMHelper::getOrCreateLibFcn(m, FinishInstName,
      void_fcn_type);

  // Now add init fcns:
  LLVMHelper::callAtEntry(m, entry_fcn, { });
  LLVMHelper::callAtExit(m, exit_fcn);
}


bool CallContextInst::runOnModule(llvm::Module &m) {
  // Algorithm:
  // First find all calls and rets within the program
  // Then, for each call,
  //   Push our nodeid to the stack (iff it isn't on the top of the stack)
  setupTypes(m);

  std::vector<llvm::CallInst *> call_insts;


  auto &cs_cfg = getAnalysis<CsCFG>();
  auto &dyn_info = getAnalysis<UnusedFunctions>();
  for (auto &fcn : m) {
    if (!dyn_info.isUsed(fcn)) {
      continue;
    }

    for (auto &bb : fcn) {
      if (!dyn_info.isUsed(bb)) {
        continue;
      }

      for (auto &inst : bb) {
        // Now find all returns in the bb
        if (auto ci = dyn_cast<llvm::CallInst>(&inst)) {
          llvm::ImmutableCallSite cs(ci);

          auto fcn = cs.getCalledFunction();
          if (fcn != nullptr && fcn->isIntrinsic()) {
            continue;
          }

          call_insts.push_back(ci);
        }
      }
    }
  }

  // setup globals after scanning for callsites, so we don't scan the sites we
  // added
  setupGlobals(m);

  // For each fcn entry:
  for (auto ci : call_insts) {
    // Call the entry fcn:
    // llvm::dbgs() << "Getting cs for : " << *ci << "\n";

    // If this is a longjmp/setjmp function... freak out
    auto cs_id = cs_cfg.getId(ci);
    assert(cs_id.valid());

    std::vector<llvm::Value *> args =
        { llvm::ConstantInt::get(i32Type_, cs_id.val()) };

    auto fcn = LLVMHelper::getFcnFromCall(ci);
    // Also check for setjmp/longjmp
    if (fcn != nullptr &&
        (fcn->getName() == "__sigsetjmp" ||
        fcn->getName() == "__setjmp" ||
        fcn->getName() == "_setjmp")) {
      llvm::CallSite cs(ci);

      std::vector<llvm::Value *> setjmp_args(args);
      // Cast the argument to an i8ptr...

      auto arg = cs.getArgument(0);
      auto i8_ptr_val = arg;
      if (arg->getType() != i8PtrType_) {
        i8_ptr_val = new llvm::BitCastInst(arg, i8PtrType_, "", ci);
      }
      setjmp_args.push_back(i8_ptr_val);
      // Handle setjump operations here
      // Call the setjmp inst function with our arg
      llvm::CallInst::Create(setjmpCallFcn_, setjmp_args, "", ci);

      // auto call = llvm::CallInst::Create(setjmpRetFcn_, args);
      // call->insertAfter(ci);
    } else if (fcn != nullptr &&
        (fcn->getName() == "longjmp" ||
        fcn->getName() == "siglongjmp")) {
      llvm::CallSite cs(ci);

      std::vector<llvm::Value *> longjmp_args(args);
      auto arg = cs.getArgument(0);
      auto i8_ptr_val = arg;
      if (arg->getType() != i8PtrType_) {
        i8_ptr_val = new llvm::BitCastInst(arg, i8PtrType_, "", ci);
      }
      longjmp_args.push_back(i8_ptr_val);
      // Handle long jump operations here
      llvm::CallInst::Create(longjmpFcn_, longjmp_args, "", ci);
    } else {
      llvm::CallInst::Create(callFcn_, args, "", ci);

      // Now call the ret fcn
      auto call = llvm::CallInst::Create(retFcn_, args);
      call->insertAfter(ci);
    }
  }

  // We do modify the module!
  return true;
}

// Okay, now build a pass which loads the contexts...
char CallContextLoader::ID = 0;
CallContextLoader::CallContextLoader() : llvm::ModulePass(ID) { }

namespace llvm {
static llvm::RegisterPass<CallContextLoader> aX("callstack-loader",
    "Loads callsite info, for use with StaticSlicer",
    false, false);
}  // namespace llvm

void CallContextLoader::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  usage.addRequired<CsCFG>();
  usage.setPreservesAll();
}

// Here is where the magic happens
bool CallContextLoader::runOnModule(llvm::Module &) {
  // Open the loader-file
  std::ifstream logfile(DynCallGraphFilename, std::ifstream::in);

  // If we actually managed to get data...
  if (logfile.good()) {
    llvm::dbgs() << "CallContextLoader: Successfully Loaded!\n";

    auto &cfg = getAnalysis<CsCFG>();

    // Then, load the lines of callstacks
    for (std::string line; std::getline(logfile, line); ) {
      std::stringstream converter(line);


      // All vectors start with 0 id...
      std::vector<CsCFG::Id> vec(1, CsCFG::Id(0));

      vec.insert(std::end(vec),
          std::istream_iterator<CsCFG::Id>(converter),
          std::istream_iterator<CsCFG::Id>());

      callsites_.emplace_back(std::move(vec));

      /*
      callsites_.emplace_back(
          std::istream_iterator<CsCFG::Id>(converter),
          std::istream_iterator<CsCFG::Id>());
      */
      /*
      llvm::dbgs() << "Got stack: " << util::print_iter(callsites_.back()) <<
        "\n";
      */
      loaded_ = true;
    }

    // Then, sort them
    std::sort(std::begin(callsites_), std::end(callsites_));

    // Then, index them
    // Here I can assume there will be no repeated entries
    //   (that would be a cycle)
    for (auto &vec : callsites_) {
      std::set<CsCFG::Id> contained_ids;
      for (auto elm : vec) {
        auto rc = contained_ids.emplace(elm);
        if (!rc.second) {
          llvm::dbgs() << "Have repeated id: " << elm << "\n";
          llvm::dbgs() << "stack is:";
          for (auto elm2 : vec) {
            llvm::dbgs() << "ELM :" << elm2 << "\n";
            for (auto scc_inst : cfg.getSCC(elm2)) {
              if (scc_inst != nullptr) {
                llvm::dbgs() << "  " <<
                  scc_inst->getParent()->getParent()->getName() << " " <<
                  scc_inst->getParent()->getName() << ": " << *scc_inst << "\n";
              } else {
                llvm::dbgs() << "  (null)\n";
              }
            }
            llvm::dbgs() << "\n";
          }
          llvm::dbgs() << "\n";


          llvm_unreachable("Shouldn't have happened");
        }
        index_[elm].emplace_back(&vec);
      }
    }
  } else {
    llvm::dbgs() << "CallContextLoader: no logfile loaded!\n";
  }

  return false;
}

