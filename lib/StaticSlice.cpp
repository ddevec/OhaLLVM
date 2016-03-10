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
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"
#include "include/lib/DynPtsto.h"

#include "llvm/Constants.h"
#include "llvm/Pass.h"
#include "llvm/PassSupport.h"
#include "llvm/Function.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Module.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ProfileInfo.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Support/InstIterator.h"


static llvm::cl::opt<std::string>
  fcn_name("slice-debug-fcn", llvm::cl::init("main"),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("The function to debug slicing on, default=main"));

static llvm::cl::opt<std::string>
  outfilename("slice-outfile", llvm::cl::init("slices.out"),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("file containing static slice output numbers"));

static llvm::cl::opt<bool>
  do_main_slice("slice-do-main", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc("Creates slices of \"main\""));

static llvm::cl::opt<bool>
  do_rand_slice("slice-do-random", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc("Creates random slices"));

static llvm::cl::opt<bool>
  do_control_flow("slice-no-control-flow", llvm::cl::init(true),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc("Disables control-flow tracking for slices"));

static llvm::cl::opt<std::string>
  rand_slice_count_str("slice-random-count", llvm::cl::init("10"),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("Random slice count"));

static llvm::cl::opt<std::string>
  rand_slice_seed_str("slice-random-seed", llvm::cl::init("1"),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("Random slice seed"));

class StaticSlice : public llvm::ModulePass {
 public:
  static char ID;
  StaticSlice() : llvm::ModulePass(ID) { }

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const {
    usage.addRequired<llvm::AliasAnalysis>();
    usage.addRequired<UnusedFunctions>();
    usage.addRequired<DynPtstoLoader>();
    usage.addRequired<llvm::DominatorTree>();
    usage.setPreservesAll();
  }

  bool runOnModule(llvm::Module &m) override {
    auto &alias = getAnalysis<llvm::AliasAnalysis>();
    dynInfo_ = &getAnalysis<UnusedFunctions>();

    // Create nearest inverse dominator list?
    // The nearest inverse dominator of a bb is its parent in the dom tree
    // The inverse dominators of a terminator are all direct children in the dom
    //      tree
    for (auto &fcn : m) {
      if (!fcn.isDeclaration()) {
        auto &dom = getAnalysis<llvm::DominatorTree>(fcn);

        for (auto &bb : fcn) {
          auto pnode = dom.getNode(&bb);

          if (pnode != nullptr) {
            auto idom = pnode->getIDom();
            if (idom != nullptr) {
              dom_[&bb] = pnode->getIDom()->getBlock();
            }
          }
        }
      }
    }

    // First, we need CFG info, calc the callsites for each function here
    // Now, calculate which stores provide each load here:
    // That should be all of our indirection....
    std::unordered_map<llvm::Value *, std::set<const llvm::Value *>>
      load_src_to_store_dest;
    std::unordered_map<llvm::Value *, std::set<const llvm::Function *>>
      call_dest_to_fcn;

    // For each store, find all loads which may alias with it
    // For each load, find all functions which may alias with it
    std::vector<llvm::Value *> store_dests;
    std::vector<llvm::Value *> load_srcs;
    std::vector<llvm::Function *> fcns;
    std::vector<llvm::Value *> call_dests;

    llvm::dbgs() << "Scanning for instructions\n";
    for (auto &fcn : m) {
        if (!dynInfo_->isUsed(fcn)) {
          continue;
        }
      // Need to find which fcns an id corresponds to
      fcns.push_back(&fcn);

      // Need to find the ids stored by each store
      // Need both the indirect function call list, and the list of ids stored
      //   by each load
      for (auto &bb : fcn) {
        if (!dynInfo_->isUsed(bb)) {
          continue;
        }
        for (auto &inst : bb) {
          if (auto si = dyn_cast<llvm::StoreInst>(&inst)) {
            // We only care about stores of pointers...
            if (llvm::isa<llvm::PointerType>(si->getOperand(0)->getType())) {
              store_dests.push_back(si);
            // OR if we just cast a ptr to an int...
            } else if (llvm::ConstantExpr *ce =
                dyn_cast<llvm::ConstantExpr>(si->getOperand(0))) {
              if (ce->getOpcode() == llvm::Instruction::PtrToInt) {
                llvm::dbgs() << "FIXME: unsupported constexpr cast to int"
                  " then store\n";
              }
            }
          } else if (llvm::isa<llvm::ReturnInst>(&inst)) {
            retsOfFunc_[&fcn].insert(&inst);
          } else if (auto li = dyn_cast<llvm::LoadInst>(&inst)) {
            load_srcs.push_back(li);
          } else if (auto ci = dyn_cast<llvm::CallInst>(&inst)) {
            // Functions without known callsites -- track their args
            if (LLVMHelper::getFcnFromCall(ci) == nullptr) {
              llvm::CallSite cs(ci);

              call_dests.push_back(cs.getCalledValue());
            }
          }
        }
      }
    }

    // Now make mappings
    llvm::dbgs() << "Making load mappings\n";
    int32_t count = 0;
    for (auto i : load_srcs) {
      auto li = cast<llvm::LoadInst>(i);
      if ((count % 1000) == 0) {
        llvm::dbgs() << "  count: " << count << " of " <<
          load_srcs.size() << "\n";
      }
      /*
      if (count == 268) {
        llvm::dbgs() << "  Load is: " <<
          li->getParent()->getParent()->getName() << ": " <<
          li->getParent()->getName() << " - " <<
          *li << "\n";
      }
      */
      auto load = li->getOperand(0);
      count++;
      auto &load_set = load_src_to_store_dest[load];
      int32_t st_count = 0;
      for (auto i : store_dests) {
        auto si = cast<llvm::StoreInst>(i);
        /*
        llvm::dbgs() << "    st_count: " << st_count << " of " <<
          store_dests.size() << "\n";
        if (st_count == 530) {
          llvm::dbgs() << "    Store is: " <<
            si->getParent()->getParent()->getName() << ": " <<
            si->getParent()->getName() << " - " <<
            *si << "\n";
        }
        */

        auto store = si->getOperand(1);
        st_count++;
        if (alias.alias(llvm::AliasAnalysis::Location(load, 1),
              llvm::AliasAnalysis::Location(store, 1)) !=
              llvm::AliasAnalysis::NoAlias) {
          load_set.insert(store);
        }
      }
    }

    count = 0;
    llvm::dbgs() << "Handling indirect calls\n";
    for (auto &call : call_dests) {
      if ((count++ % 1000) == 0) {
        llvm::dbgs() << "  count: " << count << " of " <<
          call_dests.size() << "\n";
      }
      auto &call_fcn = call_dest_to_fcn[call];
      for (auto &fcn : fcns) {
        if (alias.alias(llvm::AliasAnalysis::Location(call, 1),
              llvm::AliasAnalysis::Location(fcn, 1)) !=
              llvm::AliasAnalysis::NoAlias) {
          call_fcn.insert(fcn);
        }
      }
    }

    // For each inst in fcn:
    llvm::dbgs() << "Setting up internal structures\n";
    for (auto &fcn : m) {
      for (auto &bb : fcn) {
        for (auto &inst : bb) {
          if (llvm::isa<llvm::LoadInst>(&inst)) {
            // get ptsto of loaded addr
            loadToStores_[&inst] =
              load_src_to_store_dest[inst.getOperand(0)];
          }
          // For each call inst, if its indirect, look up what functions it may
          //   point to
          if (auto ci = dyn_cast<llvm::CallInst>(&inst)) {
            llvm::CallSite cs(ci);

            auto fcn = LLVMHelper::getFcnFromCall(ci);

            // Then make a mapping from each operand to each argument
            if (fcn != nullptr && !fcn->isDeclaration()) {
              auto cs_argi = cs.arg_begin();
              auto cs_arge = cs.arg_end();
              auto argi = fcn->arg_begin();
              auto arge = fcn->arg_end();
              for (; cs_argi != cs_arge; ++cs_argi) {
                if (argi == arge) {
                  // llvm::dbgs() << "numoperands != arg count?\n";
                  break;
                }
                auto operand = cs_argi->get();
                auto &arg = *argi;
                ++argi;

                // Copy operand into argi
                fcnToCallsite_[&arg].insert(operand);
              }
              callsiteToFcns_[ci].insert(fcn);
            } else {
              // Get the functions associated with those ids
              for (auto &fcn : call_dest_to_fcn[cs.getCalledValue()]) {
                if (!fcn->isDeclaration()) {
                  auto cs_argi = cs.arg_begin();
                  auto cs_arge = cs.arg_end();
                  auto argi = fcn->arg_begin();
                  auto arge = fcn->arg_end();
                  // Fill out the argument mappings
                  for (; cs_argi != cs_arge; ++cs_argi) {
                    if (argi == arge) {
                      // llvm::dbgs() << "numoperands != arg count?\n";
                      break;
                    }
                    auto operand = cs_argi->get();
                    auto &arg = *argi;
                    ++argi;

                    // Copy operand into argi
                    fcnToCallsite_[&arg].insert(operand);
                  }

                  callsiteToFcns_[ci].insert(fcn);
                }
              }
            }
          }
        }
      }
    }

    llvm::dbgs() << "SLICING\n";
    if (do_rand_slice) {
      InstLabeler lblr(m, dynInfo_);

      llvm::dbgs() << "Total Insts: " << lblr.totalInsts() << "\n";
      llvm::dbgs() << "Total USED Insts: " << lblr.totalUsedInsts() << "\n";

      std::ofstream out_file(outfilename, std::ofstream::out);

      int num_slices = std::stoi(rand_slice_count_str);
      int rand_seed = std::stoi(rand_slice_seed_str);

      std::uniform_int_distribution<int> dist(0, lblr.getNumUsedFcns()-1);

      std::minstd_rand rgen(rand_seed);
      for (int i = 0; i < num_slices; i++) {
        auto fcn_num = dist(rgen);
        int64_t num_insts = 0;
        // Create a slice for each instruction in main?
        auto &insts = lblr.getUsedInsts(fcn_num);
        num_insts = insts.size();

        std::uniform_int_distribution<int> inst_dist(0, num_insts-1);
        auto inst_num = inst_dist(rgen);

        auto &inst = *insts[inst_num];
        // Create a slice of this instruction:
        llvm::dbgs() << "Slicing: " << inst << "\n";
        auto slice_set = getSlice(&inst);
        int64_t slice_insts = 0;
        for (auto val : slice_set) {
          auto inst = dyn_cast<llvm::Instruction>(val);
          if (inst != nullptr) {
            slice_insts++;
          }
        }
        llvm::dbgs() << "slice num: " << i << "\n";
        llvm::dbgs() << "  slice name: " <<
          inst.getParent()->getParent()->getName() << ": " <<
          inst.getParent()->getName() << "->" << inst << "\n";
        llvm::dbgs() << "  slice insts: " << slice_insts << "\n";
        /*
        llvm::dbgs() << "Have slice:\n";
        for (auto val : slice_set) {
          llvm::dbgs() << "  " << *val << "\n";
        }
        */

        // and write out the slice, for later analysis:
        InstWriter::Write(out_file, i,
            std::begin(slice_set), std::end(slice_set),
            lblr);
      }
    }

    if (do_main_slice) {
      auto main_fcn = m.getFunction(fcn_name);

      // Create a slice for each instruction in main?
      for (auto &bb : *main_fcn) {
        for (auto &inst : bb) {
          // Create a slice of this instruction:
          llvm::dbgs() << "Slicing: " << inst << "\n";
          auto slice_set = getSlice(&inst);
          llvm::dbgs() << "Have slice:\n";
          for (auto val : slice_set) {
            llvm::dbgs() << "  " << *val << "\n";
          }
        }
      }
    }

    return false;
  }

  std::vector<const llvm::Value *> getSources(const llvm::Value *v) {
    // Now, for each type of instructions:
    // Instructions I need to care about:
    //   Unary
    //   Binary
    //   cmp
    //   gep
    //   phi
    //   Select
    //  Hard(er):
    //   Store
    //   Load
    //   Call
    //   Invoke?
    //   VAArg?
    //   Return
    // Instructions I can safely ignore
    //   Fence
    std::vector<const llvm::Value *> ret;

    // If its an instruction:
    if (auto pinst = dyn_cast<llvm::Instruction>(v)) {
      // If this is in an unused BB, ignore
      if (!dynInfo_->isUsed(pinst->getParent())) {
        return ret;
      }

      if (auto ri = dyn_cast<llvm::ReturnInst>(pinst)) {
        auto val = ri->getReturnValue();
        if (val != nullptr) {
          ret.push_back(val);
        }
      } else if (llvm::isa<llvm::InvokeInst>(pinst)) {
        // Add any args to our op list
        /*
        for (auto &val : ii->arg_operands()) {
          ret.push_back(&val);
        }
        */
        llvm_unreachable("Invoke not supported");
      } else if (auto ci = dyn_cast<llvm::CallInst>(pinst)) {
        bool do_skip = false;
        if (llvm::isa<llvm::IntrinsicInst>(ci)) {
          do_skip = true;
        }
        /*
        if (auto fcn = dyn_cast<llvm::Function>(ci->getOperand(0))) {
          llvm::dbgs() << "have fcn: " << fcn->getName() << "\n";
          if (fcn->isIntrinsic()) {
            llvm::dbgs() << "Is intrinsic??\n";
            do_skip = true;
          }
        }
        */
        if (!do_skip) {
          // Add any args to our op list
          llvm::CallSite cs(const_cast<llvm::CallInst *>(ci));


          auto &fcns = callsiteToFcns_[ci];
          for (auto fcn : fcns) {
            if (cast<llvm::Function>(fcn)->isDeclaration()) {
              auto argi = cs.arg_begin();
              auto arge = cs.arg_end();
              for (; argi != arge; ++argi) {
                // llvm::dbgs() << "Have operand: " << *argi->get() << "\n";
                ret.push_back(argi->get());
              }
            } else {
              for (auto &ret_inst : retsOfFunc_[fcn]) {
                ret.push_back(ret_inst);
              }
            }
          }
        }
      } else if (llvm::isa<llvm::AllocaInst>(pinst)) {
        // Don't have any sources for alloc insts, so ignore them
      } else if (llvm::isa<llvm::LoadInst>(pinst)) {
        // Add all sources which may supply this load...
        // Add each source from our map
        for (auto &val : loadToStores_[pinst]) {
          ret.push_back(val);
        }
      } else if (auto si = dyn_cast<llvm::StoreInst>(pinst)) {
        // Add the operands (both?) to our op list
        ret.push_back(si->getOperand(0));
        ret.push_back(si->getOperand(1));
      } else if (auto gep = dyn_cast<llvm::GetElementPtrInst>(pinst)) {
        // Add the pointed to struct to our op list
        ret.push_back(gep->getOperand(0));
      } else if (auto si = dyn_cast<llvm::SelectInst>(pinst)) {
        ret.push_back(si->getOperand(1));
        ret.push_back(si->getOperand(2));
      } else if (auto phi = dyn_cast<llvm::PHINode>(pinst)) {
        // Add each phi source to our op list
        int num_vals = phi->getNumIncomingValues();
        for (int i = 0; i < num_vals; i++) {
          ret.push_back(phi->getIncomingValue(i));
        }
      } else if (auto ui = dyn_cast<llvm::UnaryInstruction>(pinst)) {
        ret.push_back(ui->getOperand(0));
        // Add the op to our op list
      } else if (auto bi = dyn_cast<llvm::BinaryOperator>(pinst)) {
        ret.push_back(bi->getOperand(0));
        ret.push_back(bi->getOperand(1));
        // Add each op to our op list
      } else if (dyn_cast<llvm::FenceInst>(pinst)) {
        // Ignore fence
      } else if (auto ci = dyn_cast<llvm::CmpInst>(pinst)) {
        ret.push_back(ci->getOperand(0));
        ret.push_back(ci->getOperand(1));
      } else if (auto si = dyn_cast<llvm::SwitchInst>(pinst)) {
        ret.push_back(si->getCondition());
      } else if (auto bi = dyn_cast<llvm::BranchInst>(pinst)) {
        if (bi->isConditional()) {
          ret.push_back(bi->getCondition());
        }
      } else {
        llvm::dbgs() << "inst is: " << *pinst << "\n";
        llvm_unreachable("Unsupported inst");
      }

      // Also deal w/ control flow info:
      if (do_control_flow) {
        auto it = dom_.find(pinst->getParent());
        if (it != std::end(dom_)) {
          auto dom = it->second;

          ret.push_back(dom->getTerminator());
        }
      }
      // If its not an instruction it must be an Argument... (i hope)
    } else if (auto cons = dyn_cast<llvm::Constant>(v)) {
      if (llvm::isa<llvm::ConstantInt>(cons)) {
        // Ignore
      } else if (llvm::isa<llvm::ConstantFP>(cons)) {
      } else if (llvm::isa<llvm::UndefValue>(cons)) {
      } else if (llvm::isa<llvm::ConstantPointerNull>(cons)) {
        // Ignore
      } else if (llvm::isa<llvm::Function>(cons)) {
        // Ignore
      } else if (llvm::isa<llvm::GlobalVariable>(cons)) {
        // Ignore
      } else if (llvm::isa<llvm::ConstantExpr>(cons)) {
        // Ignore -- all arguments must be constant... leads nowhere
      } else {
        llvm::dbgs() << "unknown constant?: " << *cons << "\n";
        llvm_unreachable("unknown constant");
      }
    } else {
      auto arg = cast<llvm::Argument>(v);

      for (auto &val : fcnToCallsite_[arg]) {
        ret.push_back(val);
      }
    }

    return std::move(ret);
  }

  std::set<const llvm::Value *> getSlice(const llvm::Value *v) {
    std::set<const llvm::Value *> ret;
    // Add v to our set, and do some work
    std::vector<const llvm::Value *> worklist;
    std::vector<const llvm::Value *> next_worklist;

    worklist.push_back(v);
    ret.insert(v);

    bool ch = true;
    while (ch) {
      ch = false;
      // Now, go to town
      for (auto dest_val : worklist) {
        // Find sources for instruction
        // NOTE: Tricky pts are loads, and calls
        std::vector<const llvm::Value *> srcs = getSources(dest_val);
        // Add those sources to worklist
        for (auto src : srcs) {
          if (src == nullptr) {
            llvm::dbgs() << "dest_val is: " << *dest_val << "\n";
          }
          assert(src != nullptr);
          if (ret.find(src) == std::end(ret)) {
            next_worklist.push_back(src);
            ret.insert(src);
            ch = true;
          }
        }
      }

      std::swap(worklist, next_worklist);
      next_worklist.clear();
    }

    return std::move(ret);
  }

 private:
  const UnusedFunctions *dynInfo_;

  std::map<const llvm::Value *, std::set<const llvm::Value *>> callsiteToFcns_;
  std::map<const llvm::Value *, std::set<const llvm::Value *>> fcnToCallsite_;
  std::map<const llvm::Value *, std::set<const llvm::Value *>> loadToStores_;
  std::map<const llvm::Value *, std::set<const llvm::Value *>> retsOfFunc_;
  std::map<const llvm::BasicBlock *, const llvm::BasicBlock *> dom_;
};

char StaticSlice::ID = 0;
static llvm::RegisterPass<StaticSlice>
X("static-slice", "static-slice", false, false);

