/*
 * Copyright (C) 2015 David Devecsery
 */

#include <gperftools/profiler.h>

#include <algorithm>
#include <fstream>
#include <limits>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "include/util.h"
#include "include/ContextInfo.h"
#include "include/ConstraintPass.h"
#include "include/InstLabeler.h"
#include "include/LLVMHelper.h"
#include "include/Tarjans.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"
#include "include/lib/DynPtsto.h"
#include "include/lib/DynAlias.h"
#include "include/lib/SlicePosition.h"

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
  force_alias("slice-force-dyn-alias", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc("Does load-store aliasing based on the "
        "DynAliasLoader pass"));

static llvm::cl::opt<bool>
  no_control_flow("slice-no-control-flow", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc("Disables control-flow tracking for slices"));

static llvm::cl::opt<bool>
  non_context_sensitive("slice-no-context", llvm::cl::init(false),
      llvm::cl::value_desc("bool"),
      llvm::cl::desc("Disables context sensitive tracking for slices"));

static llvm::cl::opt<std::string>
  rand_slice_count_str("slice-random-count", llvm::cl::init("10"),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("Random slice count"));

static llvm::cl::opt<std::string>
  rand_slice_seed_str("slice-random-seed", llvm::cl::init("1"),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("Random slice seed"));

static llvm::cl::opt<std::string>
  slice_load_str("slice-load-file", llvm::cl::init(""),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("Where the slice number choices will be loaded"));

static llvm::cl::opt<std::string>
  slice_save_str("slice-save-file", llvm::cl::init(""),
      llvm::cl::value_desc("string"),
      llvm::cl::desc("Where the slice number choices will be saved"));


class Position {
  //{{{
 public:
  typedef ContextInfo::Context Context;
  typedef ContextInfo::ContextId ContextId;

  Position() = delete;

  Position(const Position &) = default;
  Position(Position &&) = default;

  Position &operator=(const Position &) = default;
  Position &operator=(Position &&) = default;

  // Initial state
  Position(const ContextInfo &info, ContextId id) : id_(id), info_(info) { }

  const llvm::Value *val() const {
    return info_.getContext(id_).inst();
  }

  const ContextInfo::BBBddSet &predBBs() const {
    assert(id_ != ContextId::invalid());
    return info_.getContext(id_).predBBs();
  }

  ContextInfo::StackId stack() const {
    assert(id_ != ContextId::invalid());
    return info_.getContext(id_).stack();
  }

  const ContextInfo &info() const {
    return info_;
  }

  ContextId id() const {
    return id_;
  }


 private:
  ContextId id_;

  const ContextInfo &info_;
  //}}}
};

[[gnu::unused]]
static llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
    const Position &pos) {
  os << "{ " << pos.id() << " }";
  return os;
}

class StaticSlice : public llvm::ModulePass {
 public:
  static char ID;
  StaticSlice() : llvm::ModulePass(ID) { }

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const {
    usage.addRequired<llvm::AliasAnalysis>();
    usage.addRequired<ContextInfo>();
    usage.addRequired<ConstraintPass>();
    usage.addRequired<UnusedFunctions>();
    usage.addRequired<DynPtstoLoader>();
    usage.addRequired<llvm::DominatorTree>();
    usage.addRequired<CallDests>();
    usage.addRequired<BBNumber>();
    if (force_alias) {
      usage.addRequired<DynAliasLoader>();
    }
    usage.setPreservesAll();
  }

  bool runOnModule(llvm::Module &m) override {
    alias_ = &getAnalysis<llvm::AliasAnalysis>();
    if (force_alias) {
      dynAlias_ = &getAnalysis<DynAliasLoader>();
    }
    dynInfo_ = &getAnalysis<UnusedFunctions>();
    contextInfo_ = &getAnalysis<ContextInfo>();
    auto &cons_pass = getAnalysis<ConstraintPass>();
    map_ = cons_pass.getCG().vals();
    bbNum_ = &getAnalysis<BBNumber>();
    callDests_ = &getAnalysis<CallDests>();

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


    llvm::dbgs() << "SLICING\n";

    std::ofstream slice_writer(slice_save_str, std::ofstream::out);
    std::ifstream slice_reader(slice_load_str, std::ifstream::in);
    InstLabeler lblr(m, dynInfo_);
    std::ofstream out_file(outfilename, std::ofstream::out);

    if (do_rand_slice) {
      util::PerfTimerPrinter X(llvm::dbgs(), "Random Slicing");
      llvm::dbgs() << "Total Insts: " << lblr.totalInsts() << "\n";
      llvm::dbgs() << "Total USED Insts: " << lblr.totalUsedInsts() << "\n";


      int num_slices = std::stoi(rand_slice_count_str);
      int rand_seed = std::stoi(rand_slice_seed_str);

      std::uniform_int_distribution<int> dist(0, lblr.getNumUsedFcns()-1);

      std::minstd_rand rgen(rand_seed);

      ProfilerStart("slice_random.prof");
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

        auto positions = getInitialPositions(&inst);
        llvm::dbgs() << "Slice has: " << positions.size() <<
          " initial positions\n";

        auto slice_set = getSlice(positions);
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


        SlicePosition pos(&inst, m);
        slice_writer << pos << "\n";
      }
      ProfilerStop();
    }

    if (slice_reader.is_open()) {
      std::vector<SlicePosition> slices;

      slices.insert(std::end(slices),
          std::istream_iterator<SlicePosition>(slice_reader),
          std::istream_iterator<SlicePosition>());

      size_t i = 0;
      for (auto &slice_pos : slices) {
        const llvm::Instruction *inst = slice_pos.inst(m);

        // Create a slice of this instruction:
        llvm::dbgs() << "Slicing: " << *inst << "\n";

        auto positions = getInitialPositions(inst);
        llvm::dbgs() << "Slice has: " << positions.size() <<
          " initial positions\n";

        auto slice_set = getSlice(positions);
        int64_t slice_insts = 0;
        for (auto val : slice_set) {
          auto inst = dyn_cast<llvm::Instruction>(val);
          if (inst != nullptr) {
            slice_insts++;
          }
        }
        llvm::dbgs() << "slice num: " << i << "\n";
        llvm::dbgs() << "  slice name: " <<
          inst->getParent()->getParent()->getName() << ": " <<
          inst->getParent()->getName() << "->" << *inst << "\n";
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
        ++i;
      }
    }

    if (do_main_slice) {
      auto main_fcn = m.getFunction(fcn_name);

      // Create a slice for each instruction in main?
      for (auto &bb : *main_fcn) {
        for (auto &inst : bb) {
          // Create a slice of this instruction:
          llvm::dbgs() << "Slicing: " << inst << "\n";
          auto positions = getInitialPositions(&inst);

          auto slice_set = getSlice(positions);
          llvm::dbgs() << "Have slice:\n";
          for (auto val : slice_set) {
            llvm::dbgs() << "  " << *val << "\n";
          }
        }
      }
    }

    return false;
  }

  std::vector<Position> getSources(const Position &pos,
    std::unordered_map<const llvm::Value *,
        ContextInfo::BBBddSet> &inst_to_checked_bbs) {
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
    std::vector<Position> ret;
    auto v = pos.val();

    // If its an instruction:
    if (auto pinst = dyn_cast<llvm::Instruction>(v)) {
      // If this is in an unused BB, ignore
      /*
      if (!dynInfo_->isUsed(pinst->getParent())) {
        return ret;
      }
      */
      assert(dynInfo_->isUsed(pinst->getParent()));

      auto &info = pos.info();
      /*
      llvm::dbgs() << " stack is: {";
      for (auto elm : stack.stack()) {
        llvm::dbgs() << " " << elm;
      }
      llvm::dbgs() << "}\n";
      */

      if (auto ri = dyn_cast<llvm::ReturnInst>(pinst)) {
        auto ret_val = ri->getReturnValue();
        if (ret_val != nullptr) {
          auto id = info.getContext(ret_val, pos.stack());
          ret.emplace_back(info, id);
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

        if (!do_skip) {
          // For a call we add a frame to our stack...
          // llvm::dbgs() << "Getting callsite: " << *ci << "\n";
          // How to detect recursion?
          // -- don't need to explore ret if thier bb set is equivalent to ours
          llvm::ImmutableCallSite cs(ci);
          auto &fcns = callDests_->getDests(cs);
          for (auto fcn : fcns) {
            if (cast<llvm::Function>(fcn)->isDeclaration()) {
              llvm::ImmutableCallSite cs(ci);
              auto argi = cs.arg_begin();
              auto arge = cs.arg_end();
              for (; argi != arge; ++argi) {
                // llvm::dbgs() << "Have operand: " << *argi->get() << "\n";
                auto id = info.getContext(argi->get(), pos.stack());
                ret.emplace_back(info, id);
              }
            } else {
              auto callees = info.stackPush(pos.id(), cs);
              for (auto &id : callees) {
                ret.emplace_back(info, id);
              }
            }
          }
        }
      } else if (llvm::isa<llvm::AllocaInst>(pinst)) {
        // Don't have any sources for alloc insts, so ignore them
      } else if (auto li = dyn_cast<llvm::LoadInst>(pinst)) {
        // First, add the pointer I'm loading from...
        auto id = info.getContext(li->getOperand(0), pos.stack());
        ret.emplace_back(info, id);

        // llvm::dbgs() << "Evaluating load: " << *pinst << "\n";
        auto &bb_set = pos.predBBs();
        /*
        llvm::dbgs() << "predBBs is: " << util::print_iter_cpy(bb_set) << "\n";
        llvm::dbgs() << "pos.stack() is : " << pos.stack() << "\n";
        */
        // llvm::dbgs() << "bb_set size: " << bb_set.count() << "\n";
        auto &visited_set = inst_to_checked_bbs[pinst];
        auto to_visit = bb_set - visited_set;

        // Add the set we're about to visit to our visited set
        visited_set |= to_visit;

        auto ld_src = pinst->getOperand(0);
        /*
        llvm::dbgs() << "ld isnt is: " <<
          pinst->getParent()->getParent()->getName() << ": " <<
          pinst->getParent()->getName() << " -- "
          << *pinst << "\n";
          */

        // Now visit all the bbs we need to
        // llvm::dbgs() << "to_visit size: " << to_visit.count() << "\n";
        for (auto bb_id : to_visit) {
          // llvm::dbgs() << "bb_id: " << bb_id << "\n";
          auto bb = bbNum_->getBB(bb_id);
          // llvm::dbgs() << "got bb: " << bb->getName() << "\n";
          assert(dynInfo_->isUsed(bb));
          for (auto &inst : *bb) {
            if (llvm::isa<llvm::StoreInst>(inst)) {
              auto st_dest = inst.getOperand(1);

              if (llvm::isa<llvm::PointerType>(inst.getOperand(1)->getType())) {
                // If we're forcing using static alias analysis:
                if (force_alias) {
                  if (dynAlias_->loadStoreAlias(cast<llvm::LoadInst>(pinst),
                        cast<llvm::StoreInst>(&inst))) {
                    // Need to get all valid contexts prior to my own that are
                    //   also valid for this context...
                    // FIXME: Do that...
                    // Get contexts...
                    auto prior_contexts = info.getPriorContexts(&inst,
                        pos.id());

                    for (auto context_id : prior_contexts) {
                      ret.emplace_back(info, context_id);
                    }
                  }
                } else {
                  // llvm::dbgs() << "store is: " << inst << "\n";
                  // llvm::dbgs() << "ld is: " << *pinst << "\n";
                  if (alias_->alias(llvm::AliasAnalysis::Location(st_dest),
                          llvm::AliasAnalysis::Location(ld_src)) !=
                        llvm::AliasAnalysis::NoAlias) {
                    // llvm::dbgs() << "Adding inst: " << inst << "\n";
                    // llvm::dbgs() << "  with stack: " << stack << "\n";  // NOLINT
                    auto prior_contexts = info.getPriorContexts(&inst,
                        pos.id());

                    for (auto context_id : prior_contexts) {
                      ret.emplace_back(info, context_id);
                    }
                  }
                }
              // OR if we just cast a ptr to an int...
              } else if (llvm::ConstantExpr *ce =
                  dyn_cast<llvm::ConstantExpr>(inst.getOperand(1))) {
                if (ce->getOpcode() == llvm::Instruction::PtrToInt) {
                  llvm::dbgs() << "FIXME: unsupported constexpr cast to int"
                    " then store\n";
                }
              } else {
                llvm::dbgs() << "FIXME: unsupported load from non-ptr: " <<
                  inst << "\n";
              }
            }
          }
        }

        // llvm::dbgs() << "END LD INST\n";
      } else if (auto si = dyn_cast<llvm::StoreInst>(pinst)) {
        // Add the operands (both?) to our op list
        /*
        llvm::dbgs() << "Creating pos at (0): " << *si->getOperand(0) <<
          " stack is: " << stack << "\n";;
        */
        auto id = info.getContext(si->getOperand(0), pos.stack());
        ret.emplace_back(info, id);
        /*
        llvm::dbgs() << "Creating pos at: " << *si->getOperand(1) <<
          " stack is: " << stack << "\n";  // NOLINT
        */
        auto id2 = info.getContext(si->getOperand(1), pos.stack());
        ret.emplace_back(info, id2);
      } else if (auto gep = dyn_cast<llvm::GetElementPtrInst>(pinst)) {
        // Add the pointed to struct to our op list
        auto id = info.getContext(gep->getOperand(0), pos.stack());
        ret.emplace_back(info, id);
      } else if (auto iv = dyn_cast<llvm::InsertValueInst>(pinst)) {
        // Add the previous struct to our op list
        auto id = info.getContext(iv->getOperand(0), pos.stack());
        ret.emplace_back(info, id);
        // Add the inserted value to our op list
        auto id2 = info.getContext(iv->getOperand(1), pos.stack());
        ret.emplace_back(info, id2);
      } else if (auto ev = dyn_cast<llvm::ExtractValueInst>(pinst)) {
        // Add the previous struct to our op list
        auto id = info.getContext(ev->getOperand(0), pos.stack());
        ret.emplace_back(info, id);
        /*
        // Add the extraced value to our op list
        auto id2 = info.getContext(iv->getOperand(1));
        ret.emplace_back(info, id2);
        */
      } else if (auto si = dyn_cast<llvm::SelectInst>(pinst)) {
        auto id = info.getContext(si->getOperand(1), pos.stack());
        ret.emplace_back(info, id);
        auto id2 = info.getContext(si->getOperand(2), pos.stack());
        ret.emplace_back(info, id2);
      } else if (auto phi = dyn_cast<llvm::PHINode>(pinst)) {
        // Add each phi source to our op list
        int num_vals = phi->getNumIncomingValues();
        for (int i = 0; i < num_vals; i++) {
          auto phi_val = phi->getIncomingValue(i);
          if (auto pinst = dyn_cast<llvm::Instruction>(phi_val)) {
            if (!dynInfo_->isUsed(pinst->getParent())) {
              continue;
            }
          }
          auto id = info.getContext(phi->getIncomingValue(i), pos.stack());
          ret.emplace_back(info, id);
        }
      } else if (auto ui = dyn_cast<llvm::UnaryInstruction>(pinst)) {
        auto id = info.getContext(ui->getOperand(0), pos.stack());
        ret.emplace_back(info, id);
        // Add the op to our op list
      } else if (auto bi = dyn_cast<llvm::BinaryOperator>(pinst)) {
        auto id = info.getContext(bi->getOperand(0), pos.stack());
        ret.emplace_back(info, id);
        auto id2 = info.getContext(bi->getOperand(1), pos.stack());
        ret.emplace_back(info, id2);
        // Add each op to our op list
      } else if (dyn_cast<llvm::FenceInst>(pinst)) {
        // Ignore fence
      } else if (auto ci = dyn_cast<llvm::CmpInst>(pinst)) {
        auto id = info.getContext(ci->getOperand(0), pos.stack());
        ret.emplace_back(info, id);
        auto id2 = info.getContext(ci->getOperand(1), pos.stack());
        ret.emplace_back(info, id2);
      } else if (auto si = dyn_cast<llvm::SwitchInst>(pinst)) {
        auto id = info.getContext(si->getCondition(), pos.stack());
        ret.emplace_back(info, id);
      } else if (auto bi = dyn_cast<llvm::BranchInst>(pinst)) {
        if (bi->isConditional()) {
          auto id = info.getContext(bi->getCondition(), pos.stack());
          ret.emplace_back(info, id);
        }
      } else if (auto cmpxchg = dyn_cast<llvm::AtomicCmpXchgInst>(pinst)) {
        auto id = info.getContext(cmpxchg->getCompareOperand(), pos.stack());
        ret.emplace_back(info, id);
        auto id2 = info.getContext(cmpxchg->getNewValOperand(), pos.stack());
        ret.emplace_back(info, id2);
      } else if (auto armw = dyn_cast<llvm::AtomicRMWInst>(pinst)) {
        // Ignore rmw?
        auto id = info.getContext(armw->getValOperand(), pos.stack());
        ret.emplace_back(info, id);
        auto id2 = info.getContext(armw->getPointerOperand(), pos.stack());
        ret.emplace_back(info, id2);
      } else {
        llvm::dbgs() << "inst is: " << *pinst << "\n";
        llvm_unreachable("Unsupported inst");
      }

      // Also deal w/ control flow info:
      if (!no_control_flow) {
        auto it = dom_.find(pinst->getParent());
        if (it != std::end(dom_)) {
          auto dom = it->second;

          auto id = info.getContext(dom->getTerminator(), pos.stack());
          ret.emplace_back(info, id);
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

      // llvm::dbgs() << "Tracing Argument: " << *arg << "\n";

      // Need to pop stack trace...
      auto &info = pos.info();
      auto caller_vec = info.stackPop(pos.id());
      for (auto caller_id : caller_vec) {
        // Now get the inst of that stack:
        auto &context = info.getContext(caller_id);
        // Get the inst of that context
        auto inst = context.inst();
        // llvm::dbgs() << "  arg has context: " << *inst << "\n";
        // Get the callsite of that inst
        auto ci = cast<llvm::CallInst>(inst);
        // Get the arg...
        llvm::ImmutableCallSite cs(ci);

        // Ignore args beyond the callsites number... they don't come from
        //   anywhere...
        if (cs.arg_size() > arg->getArgNo()) {
          auto val = cs.getArgument(arg->getArgNo());
          auto arg_id = info.getContext(val, context.stack());
          ret.emplace_back(info, arg_id);
        }
      }
    }

    return std::move(ret);
  }

  std::unordered_set<const llvm::Value *>
  getSlice(const std::vector<Position> &positions) {
    std::unordered_set<const llvm::Value *> ret;
    // Add v to our set, and do some work
    util::Worklist<Position> worklist(
        std::begin(positions), std::end(positions));

    // To denote which bbs we've checked for each inst -- avoids unneeded work
    std::unordered_map<const llvm::Value *, ContextInfo::BBBddSet>
      inst_to_checked_bbs;

    for (auto &pos : positions) {
      ret.insert(pos.val());
    }

    // llvm::dbgs() << "Initial stack is: " << pos.stack() << "\n";

    while (!worklist.empty()) {
      auto dest_val = worklist.pop();
      // llvm::dbgs() << "Checking on position: " << dest_val << "\n";
      /*
      if (dest_val.hasContext()) {
        llvm::dbgs() << "worklist stack is: " << dest_val.stack() << "\n";
      }
      */
      // Find sources for instruction
      // NOTE: Tricky pts are loads, and calls
      std::vector<Position> srcs = getSources(dest_val, inst_to_checked_bbs);
      // Add those sources to worklist
      for (auto src : srcs) {
        /*
        if (src.val() == nullptr) {
          llvm::dbgs() << "dest_val is: " << *dest_val.val() << "\n";
        }
        */
        assert(src.val() != nullptr);
        if (ret.find(src.val()) == std::end(ret)) {
          /*
          if (src.hasContext()) {
            llvm::dbgs() << "src_stack is: " << src.stack() << "\n";
          }
          */
          worklist.push(src);
          ret.insert(src.val());
        }
      }
    }

    return std::move(ret);
  }

 private:
  std::vector<Position> getInitialPositions(const llvm::Instruction *inst) {
    std::vector<Position> positions;
    if (non_context_sensitive) {
      auto id = contextInfo_->getNonCons(inst);
      positions.emplace_back(*contextInfo_, id);
    } else {
      // Get all contexts for this Instruction
      auto contexts = contextInfo_->getAllContexts(inst);
      positions.reserve(contexts.size());

      for (auto id : contexts) {
        positions.emplace_back(*contextInfo_, id);
      }
    }

    return std::move(positions);
  }

  const UnusedFunctions *dynInfo_;

  ValueMap map_;
  BBNumber *bbNum_;

  ContextInfo *contextInfo_;
  CallDests *callDests_;

  llvm::AliasAnalysis *alias_;
  DynAliasLoader *dynAlias_;

  std::map<const llvm::BasicBlock *, const llvm::BasicBlock *> dom_;
  std::map<const llvm::Function *, std::vector<const llvm::ReturnInst *>>
    retToFcn_;
};


// New algorithm:
//
// NOTE: Instruction + Context ==> Position
// NOTE: Context contains list of pred BBs & stack
// Given Starting Instruction and Context --
// getSlice(startPos):
//   Make worklist of Position
//   Insert startition pos into worklist
//   while (!worklist.empty()):
//     pos = worklist.next();
//     preds = FindPreds(pos);
//     worklist.insert(preds);
//
//
// FindPreds(Position pos):
//   pred_insts = findDirectPred(pos);
//       Uses context to only search predBBs for sol
//   NOTE:  Determine any stack updates here -- (for call or Ret insts)
//    -- solve w/ some relation if the set of pred BB's doesn't change...
//   if (pred_ins.bb != pos.ins.bb || stack_update)
//     pred_con = getContext(pred_ins.bb, pos.con.stack);
//
//   poses.push_back(pred_ins, pred_con);
//   for (pos : poses)
//     if (!positionSet.contains(pos)):
//       retSet.add(pos)
//
//  return retSet;
//


char StaticSlice::ID = 0;
static llvm::RegisterPass<StaticSlice>
X("static-slice", "static-slice", false, false);

