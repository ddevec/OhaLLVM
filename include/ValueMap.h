/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_VALUEMAP_H_
#define INCLUDE_VALUEMAP_H_

#include <cassert>

#include <set>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "include/Debug.h"
#include "include/util.h"

// Don't use llvm includes in unit tests
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

class ValueMap {
 private:
  struct id_tag { };

 public:
  static const int32_t AllocReserveCount = 10000000;
  typedef util::ID<id_tag, int32_t, -1> Id;

  // Constants {{{
  enum class IdEnum : int32_t {
    eNullValue = 0,
    eIntValue = 1,
    eUniversalValue = 2,
    eAggregateValue = 3,
    eNumDefaultIds
  } DefaultI;

  static const Id NullValue;
  static const Id IntValue;
  static const Id AggregateValue;
  static const Id UniversalValue;
  //}}}

  // Constructors {{{
  ValueMap();

  ValueMap(const ValueMap &) = default;
  ValueMap(ValueMap &&) = default;

  ValueMap &operator=(const ValueMap &) = default;
  ValueMap &operator=(ValueMap &&) = default;
  //}}}

  // Id generation {{{
  Id createPhonyID(const llvm::Value *val) {
    auto ret = createMapping(val);
    return ret;
  }

  Id createPhonyID() {
    auto ret = createMapping(nullptr);
    return ret;
  }

  Id createAlloc(const llvm::Value *val, int32_t size) {
    assert(size >= 0);
    auto ret = nextId();
    if (maxAllocId_ == Id::invalid()) {
      // llvm::dbgs() << "alloc nextId() " << ret << " size: " << size << "\n";
      // llvm::dbgs() << "  Orig map_.size(): " << map_.size() << "\n";
      for (int i = 0; i < size; ++i) {
        auto id = createMapping(val);
        allocRevMap_[val].push_back(id);
        auto max_offs = size - (i + 1);
        allocs_.emplace_back(id, max_offs);
      }
    } else {
      ret = maxAllocId_;
      for (int32_t i = 0; i < size; ++i) {
        auto id = maxAllocId_ + Id(i);
        auto max_offs = size - (i + 1);
        map_[static_cast<size_t>(id)] = val;
        allocs_.emplace_back(id, max_offs);
      }
      maxAllocId_ = Id(static_cast<size_t>(maxAllocId_) + size);
      assert(maxAllocId_ < maxReserveAllocId_);
    }
    // llvm::dbgs() << "  End map_.size(): " << map_.size() << "\n";

    return ret;
  }

  Id allocNamed(int32_t size, const std::string &name) {
    assert(size > 0);
    auto ret = nextId();
#ifndef NDEBUG
    auto rc =
#endif
      named_.emplace(name, nextId());
    assert(rc.second);
    for (int32_t i = 0; i <  size; ++i) {
      createMapping(nullptr);
    }
    return ret;
  }
  //}}}

  // Population/special {{{
  // Used when reading the function, if val does not exist, will create val, if
  //   it does exist will return the only id of val, if val has multiple ids
  //   will error in debug mode.
  Id getDef(const llvm::Value *val) {
    // lb will be end when revMap is emtpy...
    auto it = revMap_.find(val);
    if (it == std::end(revMap_)) {
      auto id = createMapping(val);
      it = revMap_.emplace(val, id);
    }

    assert(revMap_.count(val) == 1);

    return it->second;
  }
  //}}}

  // Accessors {{{
  Id getNamed(const std::string &name) const {
    auto it = named_.find(name);
    assert(it != std::end(named_));

    return it->second;
  }

  std::set<Id>
  getIds(const llvm::Value *val) const {
    std::set<Id> ret;

    if (auto c = dyn_cast<llvm::Constant>(val)) {
      auto it = constMap_.find(c);
      if (it == std::end(constMap_)) {
        llvm::dbgs() << "No entry for constant: " << *c << "\n";
        // assert(0);
        llvm_unreachable("unknown contant");
      }
      ret.emplace(it->second);
    } else {
      auto pr = revMap_.equal_range(val);
      for (auto it = pr.first, en=pr.second;
          it != en; ++it) {
        auto rep_id = getRep(it->second);
        ret.emplace(rep_id);
      }
    }

    return ret;
  }

  const llvm::Value *getValue(Id id) const {
    assert(static_cast<size_t>(id) < map_.size());
    return map_[static_cast<size_t>(id)];
  }

  Id maxId() const {
    return nextId();
  }

  Id getRep(Id id) const {
    return reps_.find(id);
  }
  //}}}

  // Merge/manipulation {{{
  void merge(Id lhs, Id rhs) {
    reps_.merge(lhs, rhs);
  }

  util::ObjectRemap<Id> import(const ValueMap &rhs);
  util::ObjectRemap<Id> lowerAllocs();
  //}}}

  // Misc {{{
  static constexpr Id getOffsID(Id id, int32_t offs) {
    return Id(id.val() + offs);
  }

  static bool isSpecial(Id id) {
    assert(static_cast<int32_t>(id) >= 0);
    return static_cast<int32_t>(id) <
        static_cast<int32_t>(IdEnum::eNumDefaultIds);
  }

  static void printSpecial(llvm::raw_ostream &o, Id id) {
    if (id == NullValue) {
      o << "(NullValue)";
    } else if (id == IntValue) {
      o << "(IntValue)";
    } else if (id == AggregateValue) {
      o << "(AggregateValue)";
    } else if (id == UniversalValue) {
      o << "(UniversalValue)";
    } else {
      llvm_unreachable("not special");
    }
  }

  Id getMaxAlloc() const {
    return maxAllocId_;
  }

  Id getMaxReservedAlloc() const {
    return maxReserveAllocId_;
  }

  const std::vector<std::pair<Id, uint32_t>> &allocSizes() const {
    return allocs_;
  }

  std::pair<bool, Id> getConst(const llvm::Constant *c) {
    auto next_id = nextId();
    auto ret_pr = constMap_.emplace(c, next_id);

    // If the element didn't exist in our map, update the mappings
    if (ret_pr.second) {
      /*
      llvm::dbgs() << "Creating Mapping: ";
      if (auto pfcn = dyn_cast<llvm::Function>(c)) {
        llvm::dbgs() << pfcn->getName();
      } else {
        llvm::dbgs() << *c;
      }
      llvm::dbgs() << " -> " << next_id << "\n";
      */
      // And add to revmap
      createMapping(c);
    }

    // Return either the emplaced value, or the value that used to live there
    return std::make_pair(ret_pr.second, ret_pr.first->second);
  }
  //}}}

 private:
  // Private helpers {{{
  Id nextId() const {
    return Id(map_.size());
  }

  Id createMapping(const llvm::Value *val) {
    auto next_id = nextId();
    map_.emplace_back(val);
    // assert(next_id != Id(44));
    if_debug_enabled(auto rep_id =)
      reps_.add();
    assert(rep_id == next_id);
    // assert(static_cast<int32_t>(next_id) != 103446);
    return next_id;
  }
  //}}}

  // Global values are noted
  std::unordered_map<std::string, Id> named_;

  // Allocation sites, pair(id, max_offset)
  std::vector<std::pair<Id, uint32_t>> allocs_;
  Id maxAllocId_;
  Id maxReserveAllocId_;

  std::unordered_map<const llvm::Constant *, Id> constMap_;
  std::unordered_multimap<const llvm::Value *, Id> revMap_;
  std::unordered_map<const llvm::Value *, std::vector<Id>> allocRevMap_;
  std::vector<const llvm::Value *> map_;


  // Must be mutable as "find" techincally (but not logically) modifies it...
  mutable util::UnionFind<Id> reps_;
};

class ValPrint {
  //{{{
 public:
    ValPrint(ValueMap::Id id, const ValueMap &map) : id_(id),
        map_(map) { }

    friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
        const ValPrint &pr) {
      // If its not in the map, its probably been added later as an indirect
      // object...
      auto val = pr.map_.getValue(pr.id_);

      if (val != nullptr) {
        if (auto gv = dyn_cast<const llvm::GlobalValue>(val)) {
          o << gv->getName();
        } else if (auto fcn = dyn_cast<const llvm::Function>(val)) {
          o << fcn->getName();
        } else if (auto bb = dyn_cast<const llvm::BasicBlock>(val)) {
          o << bb->getParent()->getName() << ": " << bb->getName();
        } else {
          o << *val;
        }
      } else {
        // If its a special value:
        if (ValueMap::isSpecial(pr.id_)) {
          ValueMap::printSpecial(o, pr.id_);
        } else {
          o << "(null)";
        }
      }
      return o;
    }

 private:
    ValueMap::Id id_;
    const ValueMap &map_;
  //}}}
};

class FullValPrint {
  //{{{
 public:
    FullValPrint(ValueMap::Id id, const ValueMap &map) : id_(id),
        map_(map) { }

    friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
        const FullValPrint &pr) {
      // If its not in the map, its probably been added later as an indirect
      // object...
      auto val = pr.map_.getValue(pr.id_);

      if (val != nullptr) {
        if (auto gv = dyn_cast<const llvm::GlobalValue>(val)) {
          o << gv->getName();
        } else if (auto fcn = dyn_cast<const llvm::Function>(val)) {
          o << fcn->getName();
        } else if (auto bb = dyn_cast<const llvm::BasicBlock>(val)) {
          o << bb->getParent()->getName() << ": " << bb->getName();
        } else if (auto arg = dyn_cast<const llvm::Argument>(val)) {
          o << arg->getParent()->getName() << ": " << *val;
        } else if (auto ins = dyn_cast<const llvm::Instruction>(val)) {
          o << ins->getParent()->getParent()->getName() << ": " << *val;
        } else {
          o << *val;
        }
      } else {
        // If its a special value:
        if (ValueMap::isSpecial(pr.id_)) {
          ValueMap::printSpecial(o, pr.id_);
        } else {
          o << "(null)";
        }
      }
      return o;
    }

 private:
    ValueMap::Id id_;
    const ValueMap &map_;
  //}}}
};

#endif  // INCLUDE_VALUEMAP_H_
