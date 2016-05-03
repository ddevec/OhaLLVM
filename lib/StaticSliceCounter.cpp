/*
 * Copyright (C) 2015 David Devecsery
 */

#include <algorithm>
#include <map>
#include <fstream>
#include <set>
#include <string>
#include <vector>

#include "include/DUG.h"
#include "include/InstLabeler.h"
#include "include/ObjectMap.h"
#include "include/SpecSFS.h"
#include "include/InstPrinter.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/DynAlias.h"
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

static llvm::cl::opt<std::string>
  outfilename("slice-reconstruct-outfile", llvm::cl::init(""),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("file containing reconstruction of static slice"));

class StaticSliceCounter : public llvm::ModulePass {
 public:
  static char ID;
  StaticSliceCounter() : llvm::ModulePass(ID) { }

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const {
    usage.addRequired<UnusedFunctions>();
    usage.addRequired<DynAliasLoader>();
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

    // std::map<const llvm::Function *, const llvm::Argument *> fcn_to_arg;
    // std::set<const llvm::GlobalValue *> globals;
    std::unique_ptr<llvm::raw_fd_ostream> poutfile = nullptr;
    if (outfilename != "") {
      std::string error;
      poutfile =
        std14::make_unique<llvm::raw_fd_ostream>(outfilename.c_str(), error);
      if (!error.empty()) {
        llvm::dbgs() << "Error opening file: " << error << "\n";
      }
    }

    while (pr.first != -1) {
      auto &insts = pr.second;

      int64_t num_insts = 0;
      int64_t num_bb_insts = 0;
      int64_t num_load_insts = 0;
      int64_t num_store_insts = 0;
      int64_t num_select_insts = 0;
      int64_t num_call_insts = 0;

      std::map<const llvm::Function *,
            std::set<const llvm::BasicBlock *>>
        fcn_to_bb;
      std::map<const llvm::BasicBlock *,
            std::set<const llvm::Instruction *>>
        bb_to_inst;

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
        auto pr = fcn_to_bb.emplace(pbb->getParent(),
            std::set<const llvm::BasicBlock *>());

        auto it = pr.first;

        it->second.emplace(pbb);
      }

      for (auto pinst : insts) {
        // Add inst in bb to insts
        auto pr = bb_to_inst.emplace(pinst->getParent(),
            std::set<const llvm::Instruction *>());

        auto it = pr.first;

        it->second.emplace(pinst);

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

      if (poutfile != nullptr) {
        auto &outfile = *poutfile;

        auto &dyn_alias = getAnalysis<DynAliasLoader>();

        outfile << "-----------------------------------------------------\n";
        outfile << "Slice : " << i << "\n";
        outfile << "-----------------------------------------------------\n";

        for (auto &fcn_pr : fcn_to_bb) {
          auto pfcn = fcn_pr.first;
          auto &bb_set = fcn_pr.second;

          outfile << "\n" << pfcn->getName() << "\n";
          for (auto &bb : *pfcn) {
            auto pbb = &bb;
            // Don't print bbs not in our set
            if (bb_set.find(&bb) == std::end(bb_set)) {
              continue;
            }

            outfile << "  " << bb.getName() << ":\n";

            auto bb_map_it = bb_to_inst.find(pbb);
            auto &inst_set = bb_map_it->second;
            for (auto &inst : bb) {
              auto pinst = &inst;

              if (inst_set.find(pinst) == std::end(inst_set)) {
                continue;
              }


              outfile << "  " << InstPrinter(pinst) << "\n";

              if (auto li = dyn_cast<llvm::LoadInst>(pinst)) {
                outfile << "      Load Aliases with: " << "\n";
                // Get all aliases from our dyn alias analysis
                auto aliases = dyn_alias.getAliases(li);
                if (aliases.size() == 1 && aliases[0] == nullptr) {
                  outfile << "        Unknown alias set!\n";
                } else {
                  for (auto palias : aliases) {
                    auto si = cast<llvm::StoreInst>(palias);
                    outfile << "      " << FullInstPrinter(si) << "\n";
                  }
                }
              }
            }

            outfile << "\n";
          }
        }
      }


      pr = InstReader::Read(in_file, lblr);
      i++;
    }


    return false;
  }
};

char StaticSliceCounter::ID = 0;
static llvm::RegisterPass<StaticSliceCounter>
X("static-slice-counter", "static-slice-counter", false, false);
