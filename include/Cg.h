/*
 * Copyright (C) 2016 David Devecsery
 */

#ifndef INCLUDE_CG_H_
#define INCLUDE_CG_H_

#include <cassert>
#include <cstdint>

#include <map>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"

#include "include/CgOpt.h"

#include "include/CallInfo.h"
#include "include/CsFcnCFG.h"
#include "include/DynamicInfo.h"
#include "include/ExtInfo.h"
#include "include/ModInfo.h"
#include "include/ValueMap.h"
#include "include/lib/BasicFcnCFG.h"
#include "include/lib/CsCFG.h"
#include "include/lib/IndirFcnTarget.h"
#include "include/lib/UnusedFunctions.h"

enum class ConstraintType { Copy = 0, Load = 1, Store = 2, AddressOf = 3 };
class Constraint {
  //{{{
 public:
    typedef typename ValueMap::Id Id;

    struct SrcDestCmp {
      bool operator()(const Constraint &lhs, const Constraint &rhs) const {
        if (lhs.src() == rhs.src()) {
          return lhs.dest() < rhs.dest();
        }

        return lhs.src() < rhs.src();
      }
    };

    // Constructors {{{
    Constraint(Id s, Id d, ConstraintType t) :
        Constraint(s, d, t, 0) {
    }

    Constraint(Id s, Id d,
          ConstraintType t, int32_t o) :
        // Note, when rep not specified, rep is dest
        Constraint(t, s, d, d, o) {
      assert(t != ConstraintType::Load && t != ConstraintType::Store);
    }

    Constraint(ConstraintType type, Id src, Id dest, Id rep) :
          Constraint(type, src, dest, rep, 0) { }

    Constraint(ConstraintType type, Id src, Id dest, Id rep,
        int32_t offs) :
        src_(src), dest_(dest), rep_(rep), type_(type), offs_(offs) {
      // assert(rep.val() != 191751);

      // assert(src != Id(53) || dest != Id(49));
      /*
      if (dest.val() == 2822 || src.val() == 2822) {
        llvm::dbgs() << "!!Have 2822 cons: " << *this << "\n";
      }
      */

      /*
      if (dest == ObjectMap::NullValue) {
        llvm::dbgs() << "Have dest of null in cons: " << *this << "\n";
      }

      if (src == ObjectMap::NullValue) {
        llvm::dbgs() << "Have src of null in cons: " << *this << "\n";
      }
      */

      /*
      if (dest == ObjectMap::IntValue) {
        llvm::dbgs() << "Have dest of intval in cons: " << *this << "\n";
      }

      if (dest == ObjectMap::UniversalValue) {
        llvm::dbgs() << "Have dest of UniveralVal in cons: " << *this << "\n";
      }

      if (src == ObjectMap::IntValue) {
        llvm::dbgs() << "Have src of intval in cons: " << *this << "\n";
      }
      */

      if (src == ValueMap::UniversalValue) {
        /*
        static size_t cnt = 0;
        cnt++;
        */
        llvm::dbgs() << "Have src of UniveralVal in cons: " << *this << "\n";
        // assert(cnt != 2);
      }

      // We shouldn't copy from the UV to null val... its bad
      assert(!(type == ConstraintType::Copy &&
          src == ValueMap::UniversalValue &&
          dest == ValueMap::NullValue));
    }

    // copy / moves {{{
    Constraint(const Constraint &) = default;
    Constraint &operator=(const Constraint &) = default;

    Constraint(Constraint &&) = default;
    Constraint &operator=(Constraint&&) = default;
    //}}}
    //}}}

    // Accessors {{{
    Id src() const {
      return src_;
    }

    Id offsSrc() const {
      return ValueMap::getOffsID(src(), offs());
    }

    Id dest() const {
      return dest_;
    }

    Id rep() const {
      return rep_;
    }

    void updateRep(Id new_rep) {
      rep_ = new_rep;
    }

    void retarget(Id src, Id dest) {
      src_ = src;
      dest_ = dest;
    }

    ConstraintType type() const {
      return type_;
    }

    int32_t offs() const {
      return offs_;
    }

    bool operator<(const Constraint &cons_rhs) const {
      if (type() != cons_rhs.type()) {
        return type() < cons_rhs.type();
      }

      if (dest() != cons_rhs.dest()) {
        return dest() < cons_rhs.dest();
      }

      if (src() != cons_rhs.src()) {
        return src() < cons_rhs.src();
      }

      if (offs() != cons_rhs.offs()) {
        return offs() < cons_rhs.offs();
      }

      return false;
    }

    // For LLVM RTTI {{{
    static bool classof(const Constraint *) {
      return true;
    }
    //}}}
    //}}}

    // Remap {{{
    void remap(const util::ObjectRemap<Id> &remap) {
      auto src_remap = remap[src_];
      assert(src_remap != Id::invalid());
      src_ = src_remap;
      auto dest_remap = remap[dest_];
      assert(dest_remap != Id::invalid());
      dest_ = dest_remap;

      auto rep_remap = remap[rep_];
      assert(rep_remap != Id::invalid());
      rep_ = rep_remap;
    }
    // }}}

    // Print helper {{{
    void print_label(dbg_ostream &ofil, const ValueMap &) const {
      switch (type()) {
        case ConstraintType::Copy:
          ofil << "copy";
          break;
        case ConstraintType::AddressOf:
          ofil << "addr_of";
          break;
        case ConstraintType::Load:
          ofil << "load";
          break;
        case ConstraintType::Store:
          ofil << "store";
          break;
        default:
          unreachable("Constraint with unexpected type!");
          ofil << "BLEH";
      }
    }

    static constexpr const char *getTypeName(ConstraintType t) {
      return (t == ConstraintType::Copy) ? "copy" :
             (t == ConstraintType::AddressOf) ? "address_of" :
             (t == ConstraintType::Load) ? "load" :
             (t == ConstraintType::Store) ?  "store" :
             "ERROR UNKNOWN CONST EXPR";
    }

    friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
        const Constraint &cons) {
      o << cons.rep() << ": " << getTypeName(cons.type()) << ", (" <<
          cons.src() << ", " << cons.dest() << ") + " << cons.offs();
      return o;
    }
    //}}}

 private:
    // Private Data {{{
    Id src_;
    Id dest_;
    Id rep_;

    ConstraintType type_;

    int32_t offs_ = 0;
    //}}}
  //}}}
};

// Class responsible for storing local constraint information for a function
class CgCache;
class AssumptionSet;
class Cg {
  //{{{
 public:
  typedef ValueMap::Id Id;

  Cg() = delete;

  // Populate in constructor?
  Cg(const llvm::Function *fcn,
      const DynamicInfo &dyn_info,
      AssumptionSet &as,
      ModInfo &mod_info,
      ExtLibInfo &ext_info,
      CsCFG &cs_cfg);

  Cg(const Cg &) = default;
  Cg(Cg &&) = default;

  static const int32_t ALLOC_SIZE_UNKOWN = -1;

  // Clone interface {{{
  Cg clone(std::vector<std::vector<CsCFG::Id>> cur_stacks) const {
    Cg ret(*this);
    ret.curStacks_ = std::move(cur_stacks);
    return ret;
  }
  //}}}

  // Cg manipulation functions {{{
  void optimize();
  void addGlobalConstraints(const llvm::Module &m);
  void resolveCalls(CgCache &cg_cache, CgCache &call_cache);
  void lowerAllocs();
  //}}}

  // CG accessors {{{
  const Constraint &getCons(Id id) const {
    return constraints_[static_cast<size_t>(id)];
  }

  const CallInfo &getCallInfo(const llvm::Function *fcn) const {
    return callInfo_.at(fcn).first;
  }

  const std::vector<std::tuple<Id, CallInfo, CsFcnCFG::Id>> &
  indirCalls() const {
    return indirCalls_;
  }

  ModInfo &modInfo() {
    return modInfo_;
  }

  const ValueMap &vals() const {
    return vals_;
  }

  ValueMap &vals() {
    return vals_;
  }

  const CsCFG &csCFG() const {
    return csCFG_;
  }

  ExtLibInfo &extInfo() {
    return extInfo_;
  }

  const ExtLibInfo &extInfo() const {
    return extInfo_;
  }

  const std::vector<Constraint> &constraints() const {
    return constraints_;
  }

  CsFcnCFG &localCFG() {
    return localCFG_;
  }

  const CsFcnCFG &localCFG() const {
    return localCFG_;
  }

  const std::set<std::vector<CsCFG::Id>> invalidStacks() const {
    return invalidStacks_;
  }
  //}}}

  // Deal with the constraints {{{
  Id add(ConstraintType type, Id source, Id dest, int32_t offs = 0) {
    return add(type, dest, source, dest, offs);
  }

  Id add(ConstraintType type, Id rep, Id src, Id dest,
      int32_t offs = 0) {
    assert(rep < vals_.maxId() &&
        src < vals_.maxId() &&
        dest < vals_.maxId());
    assert(rep != Id::invalid() &&
        src != Id::invalid() &&
        dest != Id::invalid());
    constraints_.emplace_back(type, src, dest, rep, offs);
    /*
    if (type == ConstraintType::Copy) {
      llvm::dbgs() << "new cons: " << constraints_.back() << "\n";
    }
    */
    return Id(constraints_.size());
  }

  Id addAlloc(Id rep, Id source, Id dest, int32_t size);

  Id getMaxAlloc() const {
    return vals_.getMaxAlloc();
  }

  void constraintStats() const;

  const std::unordered_map<Id, Id> hcdPairs() const {
    return hcdPairs_;
  }
  //}}}

  // Maps in (used for context sensitive calls)
  std::map<const llvm::Function *, std::pair<CallInfo, CsFcnCFG::Id>>
      mapIn(const Cg &rhs);

  // Merges Cgs (used for context insensitive calls)
  void mergeCg(const Cg &rhs);

  // Must be called from AndersGraph to indirect handle ext calls...
  bool addConstraintsForExternalCall(llvm::ImmutableCallSite &cs,
      const llvm::Function *called_fcn,
      const CallInfo &call_info);

 private:
  friend class CgCache;
  friend class CallInfo;


  typedef std::tuple<llvm::ImmutableCallSite, const llvm::Function *, CallInfo *> call_tuple;  // NOLINT
  // Private helpers {{{
  Id getConstValue(const llvm::Constant *c);
  Id getDef(const llvm::Value *val);
  void addConstraintForType(ConstraintType ctype,
      const llvm::Type *type, Id dest,
      Id src_obj, size_t &count);

  void addConstraintsForDirectCall(llvm::ImmutableCallSite &cs,
      const llvm::Function *callee_fcn,
      const CallInfo &caller_info,
      const CallInfo &callee_info);

  void addConstraintsForIndirectCall(llvm::ImmutableCallSite &cs,
      const CallInfo &call_info);

  std::vector<std::vector<CsCFG::Id>> getCalleeStacks(
      llvm::ImmutableCallSite &cs,
      std::vector<std::vector<CsCFG::Id>> *pinvalid_stacks);

  void resolveDirCyclicCall(llvm::ImmutableCallSite &cs,
    const llvm::Function *called_fcn, CallInfo &caller_info,
    CallInfo &callee_info, CsFcnCFG::Id callee_node_id,
    std::vector<std::vector<CsCFG::Id>> new_stacks);
  void resolveDirAcyclicCall(CgCache &base_cgs, CgCache &full_cgs,
    llvm::ImmutableCallSite &cs,
    const llvm::Function *called_fcn, CallInfo &caller_info,
    std::vector<std::vector<CsCFG::Id>> new_stacks,
    std::vector<std::vector<CsCFG::Id>> invalid_stacks);

  void resolveDirCalls(CgCache &base_cgs, CgCache &full_cgs,
      std::vector<call_tuple> &dir_calls);

  bool addConstraintsForCall(llvm::ImmutableCallSite &cs);

  void addGlobalInit(Id src_id, Id dest_id);

  Id getGlobalInitializer(const llvm::GlobalValue &glbl);

  int32_t addGlobalInitializerConstraints(Id dest,
      const llvm::Constant *C);

  void addConstraintForType(ConstraintType ctype,
      const llvm::Type *type, Id dest,
      Id src_obj);

  void idRetInst(const llvm::Instruction &inst);
  bool idCallInst(const llvm::Instruction &inst);
  void idAllocaInst(const llvm::Instruction &inst);
  void idLoadInst(const llvm::Instruction &inst);
  void idStoreInst(const llvm::Instruction &inst);
  void idGEPInst(const llvm::Instruction &inst);
  void idI2PInst(const llvm::Instruction &inst);
  void idBitcastInst(const llvm::Instruction &inst);
  void idPhiInst(const llvm::Instruction &inst);
  void idSelectInst(const llvm::Instruction &inst);
  void idVAArgInst(const llvm::Instruction &);
  void idExtractInst(const llvm::Instruction &inst);
  void idInsertInst(const llvm::Instruction &inst);

  void populateConstraints(AssumptionSet &as);
  void scanBB(const llvm::BasicBlock *bb,
      AssumptionSet &as, std::set<const llvm::BasicBlock *> &seen);
  void addGlobalConstraintForType(ConstraintType ctype,
      const llvm::Type *type, ValueMap::Id dest,
      ValueMap::Id src_obj);

  void mergeCalls(const std::vector<CallInfo> &calls,
      std::vector<CallInfo> &new_calls,
    const std::map<const llvm::Function *,
        std::pair<CallInfo, CsFcnCFG::Id>> &call_remap);
  void mergeScc(const Cg &rhs);


  // Used for optimizations...
  Id getMaxId() const {
    return vals_.maxId();
  }
  void HRU(size_t min_removed);
  void HR(size_t min_removed);
  size_t HVN();
  size_t HU();
  void HCD();
  size_t updateConstraints(OptGraph &);
  size_t updateHCDConstraints(HCDGraph &);
  //}}}

  // Private variables {{{
  // Mapping of fcns exported by this SCC to callinfo
  std::map<const llvm::Function *, std::pair<CallInfo, CsFcnCFG::Id>> callInfo_;

  // List of any external calls made by the Cg
  std::vector<CallInfo> calls_;
  // Tuple is: CallInst_id, CallInfo, localCFG_id
  std::vector<std::tuple<Id, CallInfo, CsFcnCFG::Id>> indirCalls_;

  // The actual constraints in this Cg
  std::vector<Constraint> constraints_;

  // The current call stack...
  CsCFG &csCFG_;
  std::vector<std::vector<CsCFG::Id>> curStacks_;
  std::set<std::vector<CsCFG::Id>> invalidStacks_;

  // For speculative assumptions
  DynamicInfo dynInfo_;
  AssumptionSet &as_;

  // The object numberer for this constraint graph...
  ValueMap vals_;

  // The CFG of the local subgraph
  CsFcnCFG localCFG_;
  CsFcnCFG::Id cfgId_;

  // For module level data (eg. structs) shared btwn fcns
  ModInfo &modInfo_;

  // Handles mapping constraints for external functions
  ExtLibInfo &extInfo_;

  std::unordered_map<Id, Id> hcdPairs_;

  //}}}
  //}}}
};

class CgCache {
  //{{{
 public:
  CgCache() = delete;
  explicit CgCache(const BasicFcnCFG &cfg) : cfg_(cfg) { }
  CgCache(const llvm::Module &m,
      const DynamicInfo &di,
      const BasicFcnCFG &cfg,
      ModInfo &mod_info,
      ExtLibInfo &ext_info,
      AssumptionSet &as,
      CsCFG &cs_cfg);

  Cg &getCg(const llvm::Function *fcn) {
    auto id = cfg_.getId(fcn);
    return map_.at(id);
  }

  const Cg &getCg(const llvm::Function *fcn) const {
    return map_.at(cfg_.getId(fcn));
  }

  const Cg *tryGetCg(const llvm::Function *fcn) const {
    auto it = map_.find(cfg_.getId(fcn));
    if (it != std::end(map_)) {
      return &it->second;
    }
    return nullptr;
  }

  template <typename... va_args>
  void addCg(const llvm::Function *fcn, va_args&&... args) {
    auto id = cfg_.getId(fcn);
    if_debug_enabled(auto rc =)
      map_.emplace(id, std::forward<va_args>(args)...);
    assert(rc.second);
  }

 private:
  std::map<BasicFcnCFG::Id, Cg> map_;
  BasicFcnCFG cfg_;
  //}}}
};

#endif  // INCLUDE_CG_H_
