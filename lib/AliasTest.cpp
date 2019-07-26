/*
 * Copyright (C) 2015 David Devecsery
 */

#include <map>
#include <vector>

#include "include/ModuleAAResults.h"
#include "include/lib/DynAlias.h"
#include "include/lib/IndirFcnTarget.h"
#include "include/lib/UnusedFunctions.h"

#include "llvm/Pass.h"
#include "llvm/PassSupport.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InstIterator.h"

static llvm::cl::opt<bool>
  only_load_store("alias-load-store", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc("AliasTest will only test load-store values if true"));

static llvm::cl::opt<bool>
  alias_check("alias-force-dyn", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc("AliasTest will count the dynamic load-store "
        "alias loader"));

class AliasTest : public llvm::ModulePass {
 public:
  static char ID;

  AliasTest() : llvm::ModulePass(ID) { }

  llvm::StringRef getPassName() const override {
    return "AliasTest";
  }

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const override {
    usage.setPreservesAll();
    usage.addRequired<DynAliasLoader>();
    usage.addRequired<ModuleAAResults>();
    getAAResultsAnalysisUsage(usage);
    usage.addRequired<UnusedFunctions>();
  }

  bool runOnModule(llvm::Module &m) {
    llvm::dbgs() << "AliasTest: Start\n";
    std::vector<const llvm::Value *> value_list;
    // Create a list of values to check aliases for
    auto &unused = getAnalysis<UnusedFunctions>();

    std::vector<const llvm::Instruction *> load_list;
    std::vector<const llvm::Instruction *> store_list;

    llvm::dbgs() << "AliasTest: Gathering Values\n";
    // GVs
    for (auto it = m.global_begin(), en = m.global_end(); it != en;
        ++it) {
      value_list.push_back(&(*it));
    }
    // Functions
    for (auto &fcn : m) {
      if (unused.isReallyUsed(&fcn)) {
        value_list.push_back(&fcn);
        // Funciton arguments
        for (auto it = fcn.arg_begin(), en = fcn.arg_end();
            it != en; ++it) {
          if (llvm::isa<llvm::PointerType>(it->getType())) {
            value_list.push_back(&(*it));
          }
        }

        // Instructions
        for (auto &bb : fcn) {
          if (unused.isReallyUsed(&bb)) {
            for (auto &inst : bb) {
              if (llvm::isa<llvm::PointerType>(inst.getType())) {
                value_list.push_back(&inst);
              }

              if (llvm::isa<llvm::LoadInst>(inst)) {
                load_list.push_back(&inst);
              } else if (llvm::isa<llvm::StoreInst>(inst)) {
                store_list.push_back(&inst);
              }
            }
          }
        }
      }
    }

    // Now that we have all of the "used" values in the program, find alias sets

    size_t num_checked = 0;
    size_t num_no_alias = 0;
    size_t num_must_alias = 0;
    size_t num_may_alias = 0;
    size_t num_values = value_list.size();
    if (alias_check) {
      auto &aa = getAnalysis<DynAliasLoader>();

      for (auto li : load_list) {
        for (auto si : store_list) {
          auto alias = aa.loadStoreAlias(cast<llvm::LoadInst>(li),
              cast<llvm::StoreInst>(si));
          if (alias) {
            num_may_alias++;
          } else {
            num_no_alias++;
          }

          num_checked++;
        }
      }
    } else {
      auto &aa = getAnalysis<ModuleAAResults>();
      if (only_load_store) {
        for (auto li : load_list) {
          auto load_src = li->getOperand(0);
          for (auto si : store_list) {
            // Check if the load aliases with a store
            auto store_dest = si->getOperand(1);

            auto alias = aa.alias(llvm::MemoryLocation(load_src, 1),
                 llvm::MemoryLocation(store_dest, 1));

            num_checked++;
            if (alias == llvm::AliasResult::MayAlias) {
              num_may_alias++;
            }

            if (alias == llvm::AliasResult::MustAlias) {
              num_must_alias++;
            }

            if (alias == llvm::AliasResult::NoAlias) {
              num_no_alias++;
            }
          }
        }
      } else {
        llvm::dbgs() << "AliasTest: Counting Aliases\n";
        // Now, iterate the list
        // For each value to check
        {
          util::PerfTimerPrinter t(llvm::dbgs(), "Counting Aliases");
          for (auto it = std::begin(value_list), en = std::end(value_list);
              it != en; ++it) {
            auto base_val = *it;
            // Check against all values not yet checked (O(n^2))
            for (auto it2 = it+1; it2 != en; ++it2) {
              auto check_val = *it2;
              auto alias = aa.alias(llvm::MemoryLocation(base_val, 1),
                   llvm::MemoryLocation(check_val, 1));

              num_checked++;
              if (alias == llvm::AliasResult::MayAlias) {
                num_may_alias++;
              }

              if (alias == llvm::AliasResult::MustAlias) {
                num_must_alias++;
              }

              if (alias == llvm::AliasResult::NoAlias) {
                num_no_alias++;
              }
            }
          }
        }
      }
    }

    llvm::dbgs() << "AliasTest results:\n";
    llvm::dbgs() << "  Num values:     " << num_values << "\n";
    llvm::dbgs() << "  Num stores:     " << store_list.size() << "\n";
    llvm::dbgs() << "  Num loads:      " << load_list.size() << "\n";
    llvm::dbgs() << "  Num checks:     " << num_checked << "\n";
    llvm::dbgs() << "  Num must alias: " << num_must_alias << "\n";
    llvm::dbgs() << "  Num may  alias: " << num_may_alias << "\n";
    llvm::dbgs() << "  Num no   alias: " << num_no_alias << "\n";

    return false;
  }
};

char AliasTest::ID = 0;
static llvm::RegisterPass<AliasTest>
  X("alias-test", "AliasTest", false, true);

