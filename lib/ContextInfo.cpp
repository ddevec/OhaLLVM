/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/ContextInfo.h"

#include <set>
#include <unordered_set>
#include <vector>

#include "include/util.h"
#include "include/ConstraintPass.h"
#include "include/SEG.h"
#include "include/ValueMap.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"

typedef ContextInfo::StackId StackId;
typedef ContextInfo::ContextId ContextId;

char ContextInfo::ID = 0;
ContextInfo::ContextInfo() : llvm::ModulePass(ID), cache_(info_) { }

/*
 *    How do we determine which stores may provide a load l?
 *      Find all stores S which may have happened prior to l given C
 *    # DOWN PASS
 *    def FindPredBBs(inst, stack)
 *      # Get all local predBBs
 *      FindCurAndCallee(inst, stack)
 *      # Now find all Predecessor PredBBs
 *      (predCS, predStack) = stack.pop();
 *      --predCS  # Get from the instruction before the call
 *      predBBs |= FindPredBBs(predCS, predStack())
 *      return predBBs
 *
 *    # UP PASS
 *    Def FindCurAndCallee(inst, stack):
 *      # Visit all localPredBBs
 *      NOTE: if: fcn is in SCC (recursion) all bbs of SCC are pred BBs
 *            else: Determine statically
 *      bb = inst.bb()
 *      fcn = inst.fcn()
 *      if (fcn.isInSCC()):
 *        for (scc_fcn : fcn.scc()):
 *          for (bb : scc_fcn):
 *            localPredBBs.insert(pred)
 *      else:
 *        for (auto pred : bb):
 *          localPredBBs.insert(pred)
 *
 *      for (CS : localPredBBs) 
 *        Create newstack => {curstack, CS}
 *        if (newstack.valid()):
 *          for (callee_fcn : CS.dests()):
 *            if (callee_fcn.sccID() != fcn.sccID()):
 *              localPredBBs |= FindCurAndCallee(callee_fcn.rets(), newstack)
 *
 *      return localPredBBs
 */

static void traverse_bb(const llvm::BasicBlock *bb,
    const ContextInfo::ExternalInfo &ei,
    ContextInfo::BBBddSet &bbs,
    ContextInfo::StoreBddSet &stores,
    std::vector<llvm::ImmutableCallSite> &calls,
    const UnusedFunctions &dyn_info) {
  assert(dyn_info.isUsed(bb));
  util::Worklist<const llvm::BasicBlock *> worklist({bb});
  auto &bb_num = *ei.bb_num;
  auto &si_num = *ei.si_num;

  while (!worklist.empty()) {
    auto bb = worklist.pop();
    auto bb_id = bb_num.getId(bb);

    // If we haven't visited this bb yet
    //   (NOTE: implicitly inserts into bb_list)
    if (bbs.set(bb_id)) {
      // Insert its preds into our worklist
      assert(dyn_info.isUsed(bb));
      for (auto it = pred_begin(bb), en = pred_end(bb);
          it != en; ++it) {
        if (!dyn_info.isUsed(*it)) {
          continue;
        }
        worklist.push(*it);
      }

      // Also, check for call insts
      for (auto &inst : *bb) {
        if (auto ci = dyn_cast<llvm::CallInst>(&inst)) {
          llvm::ImmutableCallSite cs(ci);
          if (LLVMHelper::isValidCall(cs)) {
            calls.emplace_back(ci);
          }
        } else if (auto ii = dyn_cast<llvm::InvokeInst>(&inst)) {
          llvm::dbgs() << "Invoke unsupporeted: " << *ii << "\n";
          llvm_unreachable("inboke unsupported");
        } else if (auto si = dyn_cast<llvm::StoreInst>(&inst)) {
          stores.set(si_num.getId(si));
        }
      }
    }
  }
}

void ContextInfo::Context::populatePreds() const {
  // Iterate through the entire thing, and follow the magical algorithm of
  //   greatness and prosperity
  // llvm::dbgs() << "populatePreds(): " << id() << "\n";


  if (stack() == StackInfo::NonCons()) {
    predBBs_ = BBBddSet::tautology();
    predStores_ = StoreBddSet::tautology();
    return;
  }

  // First get localpredbbs for this inst:
  populateLocal();

  /*
  llvm::dbgs() << "post populateLocal(): " <<
    util::print_iter_cpy(localPredBBs_) << "\n";
    */

  predBBs_ |= localPredBBs_;
  predStores_ |= localPredStores_;

  auto caller_ctx_vec = info_.stackPop(id());
  for (auto caller_ctx_id : caller_ctx_vec) {
    auto &caller_ctx = info_.getContext(caller_ctx_id);
    predBBs_ |= caller_ctx.predBBs();
    auto &caller_stores = caller_ctx.predStores();
    predStores_ |= caller_stores;
  }
}

void ContextInfo::Context::populateLocal() const {
  localPopulated_ = true;

  if (stack() == StackInfo::NonCons()) {
    localPredBBs_ = BBBddSet::tautology();
    localPredStores_ = StoreBddSet::tautology();
    return;
  }

  if (llvm::isa<llvm::Argument>(inst_)) {
    llvm::dbgs() << "argument?\n";
    return;
  }

  auto inst = cast<llvm::Instruction>(inst_);

  auto bb = inst->getParent();
  auto fcn = bb->getParent();

  auto &fcn_cfg = *info_.info_.cfg;
  auto &dyn_info = *info_.info_.dyn_info;
  auto &bb_num = *info_.info_.bb_num;
  auto &si_num = *info_.info_.si_num;

  // FIXME: Super hacky memoization table
  //   -- Should be struct local
  struct LocalInfo {
    std::vector<llvm::ImmutableCallSite> calls;
    BBBddSet bbs;
    StoreBddSet stores;
  };
  static std::unordered_map<const llvm::Function *, LocalInfo> local_info;

  auto local_it = local_info.find(fcn);

  if (local_it == std::end(local_info)) {
    LocalInfo info;

    auto &scc = fcn_cfg.getSCC(fcn);
    // Add all bbs in the scc
    if (scc.size() != 1) {
      for (auto cfg_fcn : scc) {
        if (!dyn_info.isUsed(cfg_fcn)) {
          continue;
        }
        for (auto &bb : *cfg_fcn) {
          if (!dyn_info.isUsed(bb)) {
            continue;
          }
          info.bbs.set(bb_num.getId(&bb));

          for (auto &inst : bb) {
            if (auto si = dyn_cast<llvm::StoreInst>(&inst)) {
              info.stores.set(si_num.getId(si));
            } else if (auto ci = dyn_cast<llvm::CallInst>(&inst)) {
              // Filter out inline asm and intrinsics
              llvm::ImmutableCallSite cs(ci);
              if (LLVMHelper::isValidCall(cs)) {
                info.calls.emplace_back(ci);
              }
            } else if (auto ii = dyn_cast<llvm::InvokeInst>(&inst)) {
              llvm::dbgs() << "Unexpected invoke: " << *ii << "\n";
              llvm_unreachable("Unsupported invoke inst");
            }
          }
        }
      }
    } else {
      // Actually figure out what bbs are predecessors to this bb...
      traverse_bb(bb, info_.info_, info.bbs, info.stores, info.calls,
        dyn_info);
    }

    auto rc = local_info.emplace(fcn, std::move(info));
    assert(rc.second);
    local_it = rc.first;
  }

  calls_ = local_it->second.calls;
  localPredBBs_ |= local_it->second.bbs;
  localPredStores_ |= local_it->second.stores;

  // We've now populated all callsites, handle that nonsense:
  for (auto &cs : calls_) {
    // Generate a new context for the call:
    /*
    llvm::dbgs() << "Checking callsite: " <<
      ValPrinter(cs.getInstruction()) << "\n";
    */
    assert(cs.getCalledFunction() == nullptr ||
        dyn_info.isUsed(cs.getCalledFunction()));
    assert(dyn_info.isUsed(cs.getInstruction()->getParent()));
    // FIXME: I totally hacked this by statically allocating contexts...
    //   hopefully this doesn't break everything
    // assert(0 &&
    //    "calling stack push from within a context... breaks contexts");
    auto callee_vec = info_.stackPush(id(), cs);

    for (auto callee_ctx_id : callee_vec) {
      // Get the store difference:
      auto &callee_ctx = info_.getContext(callee_ctx_id);
      localPredBBs_ |= callee_ctx.getLocalPredBBs();

      auto &callee_sts = callee_ctx.getLocalPredStores();
      localPredStores_ |= callee_sts;
    }
  }
}

// Constructor... setup noContext_ context
ContextInfo::ContextCache::ContextCache(ExternalInfo &info) : info_(info),
    contextMem_(new int8_t[sizeof(Context) * MaxContexts]),
    contexts_(reinterpret_cast<Context *>(contextMem_.get())) { }

ContextId ContextInfo::ContextCache::find(
    const llvm::Value *val,
    StackId stack,
    const ContextInfo &info) {
  auto id_num = contextSize_;
  auto rc = cache_.emplace(std::piecewise_construct,
      std::make_tuple(val, stack), std::make_tuple(id_num));

  if (rc.second) {
    // contexts_.emplace_back(val, stack, ContextId(id_num), info);
    // This line constructs the context in the array... yeah...
    new (&contexts_[contextSize_]) Context(val, stack, ContextId(id_num), info);
    contextSize_++;
    assert(contextSize_ < MaxContexts);
    assert(contextSize_ == id_num+1);
  }

  auto it = rc.first;
  return ContextId(it->second);
}

StackId ContextInfo::StackCache::find(
    const std::vector<CsCFG::Id> &stack) {
  // Construct a bdd out of it?
  StackSet s;
  // llvm::dbgs() << "Making set\n";
  for (auto &elm : stack) {
    s.set(elm);
  }
  // llvm::dbgs() << "Done making set\n";

  auto val = stackSize_;
  auto rc = cache_.emplace(s.id(), val);
  if (rc.second) {
    // Make entry in stacks_
    /*
    stacks_.emplace_back(stack, StackId(val));
    assert(stacks_.size() == val+1);
    */
    new (&stacks_[stackSize_]) StackInfo(stack, s, StackId(val));
    stackSize_++;
    assert(stackSize_ < MaxStacks);
    assert(stackSize_ == val+1);
  }

  auto it = rc.first;
  return StackId(it->second);
}

StackId ContextInfo::StackInfo::parentId(
    StackCache &cache) const {
  if (parentId_ == StackId::invalid()) {
    // Populate parentId
    auto parent_stack = stack();
    if (parent_stack.size() > 0) {
      parent_stack.pop_back();

      // llvm::dbgs() << "stack is: " << util::print_iter(parent_stack) << "\n";
      parentId_ = cache.find(parent_stack);
    } else {
      parentId_ = id();
    }
  }

  assert(parentId_ != StackId::invalid());

  return parentId_;
}

llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
    const ContextInfo::StackInfo &stack) {
  o << "{";
  for (auto &elm : stack.stack()) {
    o << " " << elm;
  }
  o << " }";
  return o;
}

std::vector<ContextId>
ContextInfo::stackPush(ContextId context_id,
    llvm::ImmutableCallSite &cs) const {
  // We append the frame to the stack,
  //   Frame denoted by callsite dests (CallDests pass)
  // Then check if the stack is valid (according to dyn info)
  //   If so, follow it
  std::vector<ContextId> ret;

  auto &context = getContext(context_id);
  auto stack_id = context.stack();
  auto new_stack_id = stack_id;

  // If we don't have a non-context sensitive analysis, figure out what our
  //   next possible stacks are
  if (stack_id != StackInfo::NonCons()) {
    auto &stack = stackCache_.getStack(stack_id);
    auto stack_vec = stack.stack();

    // Sometimes we can have backpointers... ensure we don't make a stack with
    //   those...
    auto new_id = csCFG_->getId(cs.getInstruction());
    if (stack_vec.back() == new_id) {
      return std::vector<ContextId>();
    }

    // Add the instruction to the stack
    stack_vec.push_back(new_id);

    // Make sure the stack is dynamically valid...
    if (info_.stack_info->hasDynData()) {
      if (!info_.stack_info->isValid(stack_vec)) {
        /*
        llvm::dbgs() << "have dynamically invalid push: " <<
          util::print_iter(stack_vec) << "\n";
        */
        return std::vector<ContextId>();
      }
    }

    new_stack_id = stackCache_.find(stack_vec);
  }
  /*
  llvm::dbgs() << "Got stack " << new_stack_id << " with vec:" <<
    util::print_iter(stack_vec) << "\n";
  */

  for (auto fcn : callDests_->getDests(cs)) {
    // Get the return instruction(s) of this call
    for (auto ret_inst : callDests_->getRets(fcn)) {
      // Create this context...
      ret.push_back(getContext(ret_inst, new_stack_id));
    }
  }

  return std::move(ret);
}

std::vector<ContextId>
ContextInfo::getAllContexts(const llvm::Instruction *inst) const {
  // Return all possible contexts for inst...

  // This should require visiting each node once, but keeping a listing of all
  // possible paths through the graph per node O(n^2), so, O(n^3)... ugh

  // NOTE: We only track contexts for stacks, so we need to figure out the
  //   possible stacks for inst:
  //     This means we convert inst to all callsites which call inst's function

  static std::unordered_map<const llvm::Function *, std::vector<StackId>>
    fcn_to_stacks;

  static std::unordered_map<const llvm::Instruction *, std::vector<ContextId>>
    inst_to_context;

  auto con_it = inst_to_context.find(inst);

  if (con_it == std::end(inst_to_context)) {
    std::set<ContextId> ret;

    auto it = fcn_to_stacks.find(inst->getParent()->getParent());

    if (it == std::end(fcn_to_stacks)) {
      std::vector<StackId> vec;

      // First, find all callsites before inst in this function
      auto callers =
        info_.call_info->getCallers(inst->getParent()->getParent());

      // llvm::dbgs() << "have: " << callers.size() << " callers\n";
      for (auto &ci : callers) {
        assert(llvm::isa<llvm::CallInst>(ci));
        auto &cs_paths = csCFG_->findPathsFromMain(csCFG_->getId(ci));
        // llvm::dbgs() << "  caller has: " << cs_paths.size() << " paths\n";

        // Now, iterate each path in fcn_paths
        // llvm::dbgs() << "cs_paths:\n";
        for (auto &path : cs_paths) {
          // llvm::dbgs() << "  " << util::print_iter(path) << "\n";

          if (info_.stack_info->hasDynData()) {
            if (!info_.stack_info->isValid(path)) {
              /*
              llvm::dbgs() << "    Path dynamically invalid:" <<
                  util::print_iter(path) << "\n";
              */
              continue;
            }
          }

          // Create a stack for this path -- note, since the path is
          //   in functions, this can return a set of stacks
          auto stack_id = stackCache_.find(path);

          if (stack_id == StackId::invalid()) {
            continue;
          }

          // Now, add the context to my return set
          vec.emplace_back(stack_id);
        }
      }

      auto rc = fcn_to_stacks.emplace(inst->getParent()->getParent(),
          std::move(vec));
      assert(rc.second);
      it = rc.first;
    }

    auto &stacks = it->second;
    for (auto &stack_id : stacks) {
      if (stack_id == StackId::invalid()) {
        continue;
      }

      // Now, add the context to my return set
      ret.emplace(getContext(inst, stack_id));
    }

    auto rc = inst_to_context.emplace(std::piecewise_construct,
        std::make_tuple(inst),
        std::make_tuple(std::begin(ret), std::end(ret)));
    assert(rc.second);
    con_it = rc.first;
  }

  // Compare contexts vs those in dyn:
  // First, get contexts from dyn
  return con_it->second;
}

std::vector<ContextId>
ContextInfo::getPriorContexts(const llvm::Instruction *inst,
    ContextId cur_context_id) const {
  // We get all valid contexts for an inst
  // Then, for each context, we check if it's bbs can exist in priorBBs
  //   If so, add to ret vector
  //   Else, ignore
  std::vector<ContextId> ret;

  auto &cur_context = getContext(cur_context_id);
  auto predBBs = cur_context.predBBs();

  if (cur_context.stack() == StackInfo::NonCons()) {
    ret.push_back(getContext(inst, cur_context.stack()));
  } else {
    auto possible_contexts = getAllContexts(inst);

    // Now trim contexts which don't include our cur_contexts prevbb's
    // if context.prevBBs is not subset
    for (auto context_id : possible_contexts) {
      // auto &context = getContext(context_id);

      // if ((context.predBBs() - (predBBs)).empty()) {
        ret.push_back(context_id);
      // }
    }
  }

  return std::move(ret);
}

std::vector<ContextId>
ContextInfo::stackPop(ContextId context_id) const {
  // We pop the top frame from the stack.
  std::vector<ContextId> ret;

  // Get the parent's stackID
  // If it is invalid, we stop
  auto &context = getContext(context_id);
  auto stack_id = context.stack();
  // llvm::dbgs() << "Have stack_id: " << stack_id << "\n";
  if (stack_id == StackId::invalid()) {
    return ret;
  }

  // If we don't need context sensitive info, handle that specially
  if (stack_id == StackInfo::NonCons()) {
    // Get all callsites which can call our current function:
    auto arg = cast<llvm::Argument>(context.inst());

    // Get inst's function:
    auto fcn = arg->getParent();

    // Get all callers of fcn:
    auto &callers = info_.call_info->getCallers(fcn);

    // Return a vector of all possible callers:
    for (auto &ci : callers) {
      ret.push_back(cache_.find(ci, stack_id, *this));
    }

    return std::move(ret);
  }

  auto &stack = stackCache_.getStack(stack_id);
  // llvm::dbgs() << "Have stack: " << util::print_iter(stack.stack()) << "\n";

  auto parent_id = stack.parentId(stackCache_);
  // llvm::dbgs() << "Have parent_id: " << parent_id << "\n";

  if (parent_id == StackId::invalid()) {
    return ret;
  }

  if (stack.stack().size() == 0) {
    // llvm::dbgs() << "Empty stack\n";
    return ret;
  }

  // llvm::dbgs() << "getting contexts\n";
  return getContexts(stack.stack().back(), parent_id);
}

void ContextInfo::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  usage.addRequired<UnusedFunctions>();
  usage.addRequired<ConstraintPass>();
  usage.addRequired<CsCFG>();
  usage.addRequired<FcnCFG>();
  usage.addRequired<CallDests>();
  usage.addRequired<CallContextLoader>();
  usage.addRequired<BBNumber>();
  usage.addRequired<StoreNumber>();

  usage.setPreservesAll();
}

bool ContextInfo::runOnModule(llvm::Module &m) {
  info_.dyn_info = &getAnalysis<UnusedFunctions>();
  csCFG_ = &getAnalysis<CsCFG>();
  info_.cfg = &getAnalysis<FcnCFG>();
  callDests_ = &getAnalysis<CallDests>();
  info_.stack_info = &getAnalysis<CallContextLoader>();
  info_.call_info = callDests_;
  info_.si_num = &getAnalysis<StoreNumber>();
  info_.bb_num = &getAnalysis<BBNumber>();

  BBBddSet::Setup(info_.bb_num->numBBs());
  StoreBddSet::Setup(info_.si_num->numStores());
  llvm::dbgs() << "providing size: " << csCFG_->size() << "\n";
  StackSet::Setup(csCFG_->size());

  mainFcn_ = m.getFunction("main");

  return false;
}

namespace llvm {
static RegisterPass<ContextInfo> dX("-force-context-info",
    "Gathers context-based pred information, for use with context sensitive"
    " information flow analyses (like StaticSlice)",
    false, false);
}  // namespace llvm

// Generate a pred-graph of the function calls
//   Populate each of the function calls w/ used BBs
//   Happens on construction of node

// Then, compress sccs
//   TarjanSCC

// Then, preform a bottom-up traversal, merging callees with callers
//   Handled by addCalleePreds()

// Those are blocks visited by /that/ scc (function set)
// Use this to get pred info -- callers are pred edges (unless stack is given),
//   callees are taken care of by this algorithm

// ALGORITHM for getting pred bbs:


// Okay, now we design the ContextInfo pass:
//   This pass:
//     Defines a context as:
//       tuple<S, stack>
//       { S exists in Instructions, Arguments }
//         No contants
//         No function pointers
//     Determines the pred stores for each
//     Determines the potential callsites for each context (none if not call
//           inst)
//     Determines the predBBs for each instruction (including current bb...
//           although technically not entirely)
//     Determines the set of return sites for each context


/*
 *  FcnCFG := graph(fcn)
 *    Contains a mapping of functions to their SCCs
 *    Queries:
 *      vector<fcn> getSccFcns(fcn)
 *      SccID getSccID(fcn)
 *
 *  STACKINFO := () -- cache of dynamic stack info
 *    Queries:
 *      stack[] getAllStacks(inst):
 *      stack[] push(stack, CS, fcn)
 * 
 *
 *  CONTEXT := (inst, stack)
 *    Contains information about BB set
 *    Queries:
 *      context(inst, stack)
 *      bbSet getPredBBs()
 *        bbSet getUpPredBBs() -- used only by getPredBBs
 *      stack getStack()
 *      inst getInst()
 *      ==(context)
 *
 *  STACK := array(pair(CS, fcn))
 *    Contains information about prior callsites
 *    May have dynamic information
 *    Queries:
 *      -- FALSE, by StackInfo -- Stack push(CS, fcn)
 *      (CS, stack) pop()
 *      ==(stack)
 *
 * General plan:
 *    Calculate context-sensitive slicing information:
 *       Requires:
 *         Relate Arguments to Callsite Args
 *         Relate Callsite Value to Ret Insts
 *         Relate Loads to prior Stores
 *    All queries conducted with a "context"
 *      Ask which {cs.arg, ret, store} provided this, given context C
 *
 *    arg -> Callsite Args:
 *      if no more frames:
 *        get all possible callsites
 *        return set(fcn.allCallsites().args(), emptystack)
 *      else:
 *        (CS, prevstack) = stack.pop()
 *        return set(CS.args(), prevstack)
 *
 *    Callsite Value -> Ret Inst:
 *      for (fcn : CS.dests()):
 *        newstack = stack.push(cs, fcn)
 *        if newstack invalid:
 *          Ignore
 *        ret.push(fcn.getRet(), newstack)
 *      return ret
 *
 *    Loads -> prior Stores:
 *      predBBs = FindPredBBs(load, stack)
 *      for (bb : predBBs):
 *        for (inst : bb):
 *          if (inst.isStore()):
 *            stores.insert(inst)
 *
 *    How do we determine which stores may provide a load l?
 *      Find all stores S which may have happened prior to l given C
 *    # DOWN PASS
 *    def FindPredBBs(inst, stack)
 *      # Get all local predBBs
 *      FindCurAndCallee(inst, stack)
 *      # Now find all Predecessor PredBBs
 *      (predCS, predStack) = stack.pop();
 *      --predCS  # Get from the instruction before the call
 *      predBBs |= FindPredBBs(predCS, predStack())
 *      return predBBs
 *
 *    # UP PASS
 *    Def FindCurAndCallee(inst, stack):
 *      # Visit all localPredBBs
 *      NOTE: if: fcn is in SCC (recursion) all bbs of SCC are pred BBs
 *            else: Determine statically
 *      bb = inst.bb()
 *      fcn = inst.fcn()
 *      if (fcn.isInSCC()):
 *        for (scc_fcn : fcn.scc()):
 *          for (bb : scc_fcn):
 *            localPredBBs.insert(pred)
 *      else:
 *        for (auto pred : bb):
 *          localPredBBs.insert(pred)
 *
 *      for (CS : localPredBBs) 
 *        Create newstack => {curstack, CS}
 *        if (newstack.valid()):
 *          for (callee_fcn : CS.dests()):
 *            if (callee_fcn.sccID() != fcn.sccID()):
 *              localPredBBs |= FindCurAndCallee(callee_fcn.rets(), newstack)
 *
 *      return localPredBBs
 */


