/*
 * Copyright (C) 2015 David Devecsery
 *
 */

#ifndef INCLUDE_CONTEXTINFO_H_
#define INCLUDE_CONTEXTINFO_H_

#include <algorithm>
#include <functional>
#include <limits>
#include <map>
#include <set>
#include <unordered_map>
#include <vector>

#include "include/util.h"
#include "include/SEG.h"
#include "include/ValueMap.h"
#include "include/lib/BBNumber.h"
#include "include/lib/BddSet.h"
#include "include/lib/CallContextPass.h"
#include "include/lib/CallDests.h"
#include "include/lib/CsCFG.h"
#include "include/lib/FcnCFG.h"
#include "include/lib/StoreNumber.h"
#include "include/lib/UnusedFunctions.h"

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"

// Pass determining call/return context info for each function
class ContextInfo : public llvm::ModulePass {
  // Class representing the control flow graph context
  //     Defines a context as:
  //       tuple<S, stack>
  //       { S exists in Instructions, Arguments }
  //         No contants
  //         No function pointers
 private:
  struct cons_id_tag {};
  struct stack_id_tag {};
  struct store_bdd_tag { };
  struct bb_bdd_tag { };
  struct stack_set_tag { };

  class StackCache;


 public:
  // FIXME: Technically not part of the external interface...
  struct ExternalInfo {
    const UnusedFunctions *dyn_info = nullptr;
    const CallDests *call_info = nullptr;
    const FcnCFG *cfg = nullptr;
    const CallContextLoader *stack_info = nullptr;
    const BBNumber *bb_num = nullptr;
    const StoreNumber *si_num = nullptr;
  };

  typedef util::ID<cons_id_tag, uint32_t,
          std::numeric_limits<uint32_t>::max()> ContextId;
  typedef util::ID<stack_id_tag, uint32_t,
          std::numeric_limits<uint32_t>::max()> StackId;

  typedef BddSet<StoreNumber::Id, store_bdd_tag> StoreBddSet;
  typedef BddSet<BBNumber::Id, bb_bdd_tag> BBBddSet;
  typedef BddSet<CsCFG::Id, stack_set_tag> StackSet;

  class StackInfo {
    //{{{
   public:
    static StackInfo EmptyStack() {
      return emptyStack_;
    }

    static StackId NonCons() {
      return StackId(0);
    }

    StackInfo() = delete;
    StackInfo(std::vector<CsCFG::Id> stack, StackSet set,
        StackId id) : stack_(std::move(stack)), set_(set), id_(id) { }

    const std::vector<CsCFG::Id> &stack() const {
      return stack_;
    }

    StackId id() const {
      return id_;
    }

    StackId parentId(StackCache &cache) const;

    bool operator==(const StackInfo &rhs) const {
      return (id() == rhs.id());
    }

   private:
    std::vector<CsCFG::Id> stack_;

    StackSet set_;

    // Cache of ParentId?
    mutable StackId parentId_;
    // StackId?
    StackId id_;

    static StackInfo emptyStack_;
    //}}}
  };

  // Exists mostly to cache intermediate results...
  class Context {
    //{{{
   public:
    Context() = delete;
    Context(const llvm::Value *inst, StackId id, ContextId cid,
          const ContextInfo &info) :
        inst_(inst), stack_(id), id_(cid), info_(info) {
      assert(inst != nullptr);
      assert(!llvm::isa<llvm::Instruction>(inst) ||
          info_.info_.dyn_info->isUsed(
            cast<llvm::Instruction>(inst)->getParent()));
    }

    const llvm::Value *inst() const {
      return inst_;
    }

    StackId stack() const {
      return stack_;
    }

    ContextId id() const {
      return id_;
    }

    const BBBddSet &predBBs() const {
      if (!predsPopulated_) {
        populatePreds();
        predsPopulated_ = true;
      }

      return predBBs_;
    }

    const StoreBddSet &predStores() const {
      if (!predsPopulated_) {
        populatePreds();
        predsPopulated_ = true;
      }

      return predStores_;
    }

   private:
    void populatePreds() const;
    void populateLocal() const;

    const BBBddSet &getLocalPredBBs() const {
      // Populate only the current and any callee's BBs / SIs
      if (!localPopulated_) {
        populateLocal();
      }

      return localPredBBs_;
    }

    const StoreBddSet &getLocalPredStores() const {
      // Populate only the current and any callee's BBs / SIs
      if (!localPopulated_) {
        populateLocal();
      }

      return localPredStores_;
    }

    // May also be an arg...
    const llvm::Value *inst_;
    const StackId stack_;

    const ContextId id_;

    const ContextInfo &info_;

    // Cached data
    mutable bool predsPopulated_ = false;
    mutable BBBddSet predBBs_;
    mutable StoreBddSet predStores_;
    mutable bool localPopulated_ = false;
    mutable BBBddSet localPredBBs_;
    mutable StoreBddSet localPredStores_;
    mutable std::vector<llvm::ImmutableCallSite> calls_;
    //}}}
  };

  static char ID;
  ContextInfo();

  virtual bool runOnModule(llvm::Module &m);

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  llvm::StringRef getPassName() const override {
    return "ContextInfo";
  }

  // Context Creations/acquisition functions {{{
  std::vector<ContextId> getAllContexts(const llvm::Instruction *) const;

  ContextId getNonCons(const llvm::Instruction *inst) const {
    return getContext(inst, StackInfo::NonCons());
  }

  std::vector<ContextId> getContexts(CsCFG::Id val, StackId id) const {
    std::vector<ContextId> ret;
    for (auto ins : csCFG_->getSCC(val)) {
      // nullptr for mainNode_
      if (ins != nullptr) {
        ret.push_back(cache_.find(ins, id, *this));
      }
    }

    return ret;
  }

  ContextId getContext(const llvm::Value *val, StackId id) const {
    return cache_.find(val, id, *this);
  }
  //}}}

  // Context manipulation functions {{{
  std::vector<ContextId>
  stackPush(ContextId context, llvm::ImmutableCallSite &cs) const;

  std::vector<ContextId>
  getPriorContexts(const llvm::Instruction *inst,
      ContextId cur_context) const;

  std::vector<ContextId> stackPop(ContextId context) const;
  //}}}

  // Context/Stack Accessors {{{
  const Context &getContext(ContextId id) const {
    return cache_.getContext(id);
  }
  //}}}

 private:
  class ContextCache {
    //{{{
   public:
    static const size_t MaxContexts = 50000000;

    explicit ContextCache(ExternalInfo &info);

    ContextId find(const llvm::Value *, StackId, const ContextInfo &info);

    ContextId getNoContext() const {
      return noContext_;
    }

    const Context &getContext(ContextId id) const {
      assert(static_cast<size_t>(id) < contextSize_);
      return contexts_[static_cast<size_t>(id)];
    }

   private:
    struct ContextKey {
      struct hasher {
        size_t operator()(const ContextKey &k1) const {
          auto ret = StackId::hasher()(k1.stack);

          ret ^= ret << 11;
          ret ^= std::hash<decltype(k1.instruction)>()(k1.instruction);

          return ret;
        }
      };

      ContextKey(const llvm::Value *ins, StackId i) :
        instruction(ins), stack(i) { }

      bool operator==(const ContextKey &rhs) const {
        return instruction == rhs.instruction && stack == rhs.stack;
      }

      const llvm::Value *instruction;
      StackId stack;
    };

    ExternalInfo &info_;

    std::unordered_map<ContextKey, size_t, ContextKey::hasher> cache_;
    size_t contextSize_ = 0;
    std::unique_ptr<int8_t[]> contextMem_;
    Context *contexts_;

    ContextId noContext_;
    //}}}
  };

  class StackCache {
    //{{{
   public:
    static const size_t MaxStacks = 50000000;

    StackCache() :
      stackMem_(new int8_t[sizeof(StackInfo) * MaxStacks]),
      stacks_(reinterpret_cast<StackInfo *>(stackMem_.get())) { }

    StackId find(const std::vector<CsCFG::Id> &stack);

    const StackInfo &getStack(StackId id) const {
      assert(static_cast<size_t>(id) < stackSize_);
      return stacks_[static_cast<size_t>(id)];
    }

   private:
    static size_t stackHashCombine(size_t hash, CsCFG::Id frame) {
      return hash ^ (hash >> 11) ^ CsCFG::Id::hasher()(frame);
    }

    struct StackHasher {
      size_t operator()(const std::vector<CsCFG::Id> &stack)
            const {
        size_t hash = 0;
        for (CsCFG::Id frame : stack) {
          hash = stackHashCombine(hash, frame);
        }
        return hash;
      }
    };

    std::unordered_map<int, size_t> cache_;  // NOLINT
    // std::vector<StackInfo> stacks_;
    size_t stackSize_ = 1;
    std::unique_ptr<int8_t[]> stackMem_;
    StackInfo *stacks_;
    //}}}
  };

  ExternalInfo info_;

  llvm::Function *mainFcn_;

  mutable CallDests *callDests_;
  mutable CsCFG *csCFG_;

  // Made mutable, because its actually a cache, all we really do is read the
  //   file.  The cache just makes our reading not stupid slow
  mutable ContextCache cache_;
  mutable StackCache stackCache_;
};

#endif  // INCLUDE_CONTEXTINFO_H_

