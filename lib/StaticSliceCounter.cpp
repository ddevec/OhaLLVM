/*
 * Copyright (C) 2015 David Devecsery
 */

#include <algorithm>
#include <map>
#include <fstream>
#include <set>
#include <string>
#include <vector>

#include "include/Andersens.h"
#include "include/DUG.h"
#include "include/InstLabeler.h"
#include "include/ObjectMap.h"
#include "include/SpecSFS.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"

#include "llvm/Constants.h"
#include "llvm/Pass.h"
#include "llvm/PassSupport.h"
#include "llvm/Function.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Module.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Analysis/ProfileInfo.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Support/InstIterator.h"

static llvm::cl::opt<std::string>
  infilename("static-slice-file", llvm::cl::init("slices.out"),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("file containing static slice output numbers"));

class StaticSliceCounter : public llvm::ModulePass {
 public:
  static char ID;
  StaticSliceCounter() : llvm::ModulePass(ID) { }

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const {
    usage.addRequired<UnusedFunctions>();
    usage.addRequired<llvm::ProfileInfo>();
    usage.setPreservesAll();
  }

  bool runOnModule(llvm::Module &m) override {
    // Okay, we gotsta check the dynamic count we expect for each
    // instrumentation point in this slice
    // Instrumentation points include:
    //    Beginning of BB
    //    End of BB
    //  visit:
    //    Loads
    //    Select
    //    Stores
    //    Call
    //      "SpecialCall" -- we're ignoring?

    // Load the slice file
    // Find the used bbs
    // for each bb, get a count of insts
    // For each inst:
    //    if load, select, store, call
    //      add to inst count

    std::ifstream in_file(infilename, std::ifstream::in);

    auto &dyn_info = getAnalysis<UnusedFunctions>();
    auto &pi = getAnalysis<llvm::ProfileInfo>();

    InstLabeler lblr(m, &dyn_info);

    int i = 0;
    auto pr = InstReader::Read(in_file, lblr);
    while (pr.first != -1) {
      auto &insts = pr.second;

      int64_t num_insts = 0;
      int64_t num_bb_insts = 0;
      int64_t num_load_insts = 0;
      int64_t num_store_insts = 0;
      int64_t num_select_insts = 0;
      int64_t num_call_insts = 0;

      // Okay, have the insts... now gather the bbs
      std::set<const llvm::BasicBlock *> bbs;

      for (auto inst : insts) {
        bbs.insert(inst->getParent());
      }

      // Now, do bbs:
      for (auto pbb : bbs) {
        // Get edge count of bb
        // 2 insts per bb, one for start one for end
        int64_t inc_amt = static_cast<int64_t>(pi.getExecutionCount(pbb) * 2);
        num_insts += inc_amt;
        num_bb_insts += inc_amt;
      }

      for (auto pinst : insts) {
        if (llvm::isa<llvm::LoadInst>(pinst)) {
          int64_t inc_amt =
            static_cast<int64_t>(pi.getExecutionCount(pinst->getParent()));
          num_insts += inc_amt;
          num_load_insts += inc_amt;
        } else if (llvm::isa<llvm::SelectInst>(pinst)) {
          int64_t inc_amt =
            static_cast<int64_t>(pi.getExecutionCount(pinst->getParent()));
          num_insts += inc_amt;
          num_select_insts += inc_amt;
        } else if (llvm::isa<llvm::StoreInst>(pinst)) {
          int64_t inc_amt =
            static_cast<int64_t>(pi.getExecutionCount(pinst->getParent()));
          num_insts += inc_amt;
          num_store_insts += inc_amt;
        } else if (llvm::isa<llvm::CallInst>(pinst)) {
          int64_t inc_amt =
            static_cast<int64_t>(pi.getExecutionCount(pinst->getParent()));
          num_insts += inc_amt;
          num_call_insts += inc_amt;
        }
      }

      llvm::dbgs() << "slice: " << i << "\n";
      llvm::dbgs() << "  slice_size: " << insts.size() << "\n";
      llvm::dbgs() << "  num_insts: " << num_insts << "\n";
      /*
      llvm::dbgs() << "  num_bb_insts: " << num_bb_insts << "\n";
      llvm::dbgs() << "  num_load_insts: " << num_load_insts << "\n";
      llvm::dbgs() << "  num_store_insts: " << num_store_insts << "\n";
      llvm::dbgs() << "  num_call_insts: " << num_call_insts << "\n";
      llvm::dbgs() << "  num_select_insts: " << num_select_insts << "\n";
      */

      pr = InstReader::Read(in_file, lblr);
      i++;
    }

    return false;
  }
};

char StaticSliceCounter::ID = 0;
static llvm::RegisterPass<StaticSliceCounter>
X("static-slice-counter", "static-slice-counter", false, false);
