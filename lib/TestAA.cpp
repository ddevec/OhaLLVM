/*
 * Copyright (C) 2015 David Devecsery
 */

#include <map>
#include <vector>

#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"

#include "llvm/Pass.h"
#include "llvm/PassSupport.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InstIterator.h"


class TestAA : public llvm::ModulePass {
 public:
  static char ID;
  TestAA() : llvm::ModulePass(ID) { }

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const {
    usage.setPreservesAll();
    usage.addRequired<llvm::AAResultsWrapperPass>();
    usage.addRequired<UnusedFunctions>();
  }

  bool runOnModule(llvm::Module &m) override {
    auto main_fcn = m.getFunction("main");
    llvm::Value *first_ptr = nullptr;
    llvm::Value *second_ptr = nullptr;

    for (auto it = inst_begin(main_fcn), en = inst_end(main_fcn);
        it != en; ++it) {
      llvm::Instruction &ptr = *it;
      if (llvm::isa<llvm::PointerType>(ptr.getType())) {
        if (first_ptr != nullptr) {
          second_ptr = &ptr;
          break;
        }
        first_ptr = &ptr;
      }
    }

    auto &aa = getAnalysis<llvm::AAResultsWrapperPass>().getAAResults();

    // aa.deleteValue(first_ptr);

    if (aa.alias(llvm::MemoryLocation(first_ptr, 1),
         llvm::MemoryLocation(second_ptr, 1)) ==
        llvm::AliasResult::MayAlias) {
      llvm::dbgs() << "may alias!!\n";
    }

    return false;
  }
};

char TestAA::ID = 0;
static llvm::RegisterPass<TestAA>
X("TestAA", "testAA", false, false);

