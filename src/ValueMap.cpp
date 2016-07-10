/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/ValueMap.h"

#include <cassert>

#include <algorithm>
#include <set>
#include <unordered_set>
#include <vector>

#include "include/util.h"

typedef ValueMap::Id Id;

const Id  ValueMap::NullValue =
    Id(static_cast<int32_t>(ValueMap::IdEnum::eNullValue));

const Id  ValueMap::IntValue =
    Id(static_cast<int32_t>(ValueMap::IdEnum::eIntValue));

const Id  ValueMap::UniversalValue =
    Id(static_cast<int32_t>(ValueMap::IdEnum::eUniversalValue));

const Id  ValueMap::AggregateValue =
    Id(static_cast<int32_t>(ValueMap::IdEnum::eAggregateValue));

ValueMap::ValueMap() {
  for (int32_t i = 0; i < static_cast<int32_t>(IdEnum::eNumDefaultIds);
      ++i) {
    createMapping(nullptr);
  }
}

util::ObjectRemap<Id> ValueMap::import(const ValueMap &rhs) {
  util::ObjectRemap<Id> remap(rhs.map_.size());

  // Special values are not copied, they are equivalent between the two
  // This is baseline specials (aggregate values)
  // AND named values (which are globals)
  // AND global variables

  // First, handle special remaps (no motion here)
  Id remap_id(0);
  for (Id i(0); i < Id(static_cast<int32_t>(IdEnum::eNumDefaultIds)); ++i) {
    remap.set(i, remap_id);
    assert(i == remap_id);
    ++remap_id;
  }

  // Now, if allocs are setup, handle moving the allocs
  if (getMaxAlloc() != Id::invalid()) {
    for (auto &pr : rhs.allocRevMap_) {
      auto &lhs_vec = allocRevMap_[pr.first];
      auto &rhs_vec = pr.second;

      for (auto id : rhs_vec) {
        lhs_vec.push_back(maxAllocId_);
        remap.set(id, maxAllocId_);
        maxAllocId_++;
        /*
        llvm::dbgs() << "Remap alloc: " << pr.second <<
            " -> " << maxAllocId_ << "\n";
        */
      }
    }

    assert(maxAllocId_ <= getMaxReservedAlloc());
    remap_id = getMaxReservedAlloc();
  }

  // Then, handle named remaps (add any missing named variables)
  for (auto &pr : rhs.named_) {
    auto rc = named_.emplace(pr.first, nextId());
    if (rc.second) {
      createMapping(nullptr);
    }

    /*
    llvm::dbgs() << "Remap named: " << pr.second << " -> "
        << rc.first->second << "\n";
    */
    remap.set(pr.second, rc.first->second);
  }


  // Third, transfer globals, remap existing ones
  for (auto &pr : rhs.constMap_) {
    auto rc = constMap_.emplace(pr.first, nextId());
    if (rc.second) {
      createMapping(pr.first);
    }

    /*
    llvm::dbgs() << "Remap const: " << pr.second << " -> "
        << rc.first->second << "\n";
    */
    remap.set(pr.second, rc.first->second);
  }

  // Finally, handle the transfer of all other ids
  for (Id rhs_max(rhs.map_.size()), rhs_id(0); rhs_id < rhs_max; ++rhs_id) {
    // If I haven't set up this id yet
    if (remap[rhs_id] == Id::invalid()) {
      auto id = nextId();
      // llvm::dbgs() << "Remap: " << rhs_id <<" -> " << id << "\n";
      createMapping(rhs.map_[static_cast<size_t>(rhs_id)]);
      remap.set(rhs_id, id);
    }
  }

  // Now, update our reps
  for (Id rhs_id(0); rhs_id < Id(rhs.map_.size()); ++rhs_id) {
    auto rep_id = rhs.reps_.find(rhs_id);
    if (rep_id != rhs_id) {
      auto my_rep_id = reps_.find(remap[rep_id]);
      auto my_rhs_id = reps_.find(remap[rhs_id]);
      reps_.merge(my_rep_id, my_rhs_id);
    }
  }

  // Now, update revMap_ and allocRevMap_
  for (auto &pr : rhs.revMap_) {
    revMap_.emplace(pr.first, remap[pr.second]);
  }

  for (auto &pr : rhs.allocRevMap_) {
    auto &lhs_vec = allocRevMap_[pr.first];
    auto &rhs_vec = pr.second;

    for (auto rhs_id : rhs_vec) {
      lhs_vec.push_back(remap[rhs_id]);
    }
  }

  // After we have the remap, Allocs are remapped and transferred
  for (auto &pr : rhs.allocs_) {
    /*
    llvm::dbgs() << "Remapping alloc from: " << pr.first << " -> "<<
      remap[pr.first] << " val: " << ValPrint(pr.first, rhs) << "\n";
    */
    allocs_.emplace_back(remap[pr.first], pr.second);
  }

  return std::move(remap);
}

util::ObjectRemap<Id> ValueMap::lowerAllocs() {
  util::ObjectRemap<Id> remap(map_.size() + AllocReserveCount);

  llvm::dbgs() << "Init map_.size() is: " << map_.size() << "\n";

  std::unordered_set<Id> seen;
  auto update_seen = [&seen] (const Id &id) {
    auto rc = seen.emplace(id);
    return rc.second;
  };

  // First, handle special remaps (no motion here)
  Id remap_id(0);
  for (Id i(0); i < Id(static_cast<int32_t>(IdEnum::eNumDefaultIds)); ++i) {
    remap.set(i, remap_id);
    assert(i == remap_id);
    if_debug_enabled(bool check =)
      update_seen(i);
    assert(check);
    ++remap_id;
  }

  // Now, move all allocs down
  for (auto &pr : allocs_) {
    auto id = pr.first;
    if_debug_enabled(bool check =)
      update_seen(id);
    assert(check);

    remap.set(id, remap_id);
    ++remap_id;
  }

  // Now, set the max alloc id
  maxAllocId_ = remap_id;
  remap_id = Id(static_cast<int32_t>(remap_id) + AllocReserveCount);
  maxReserveAllocId_ = remap_id;

  // Now, handle the map...
  for (Id id(0); id < Id(map_.size()); ++id) {
    bool add = update_seen(id);

    if (add) {
      remap.set(id, remap_id);
      remap_id++;
    }
  }
  // We're done with seen now
  seen.clear();


  // Now that we've finished updating our remap tree, go and remap everything
  std::vector<const llvm::Value *> new_map(map_.size() + AllocReserveCount);
  // Grow reps to be the size of new_map
  while (reps_.size() < new_map.size()) {
    reps_.add();
  }
  // Then remap the ids in new reps
  reps_.remap(remap);

  // Now remap new_map
  llvm::dbgs() << "New map size is: " << new_map.size() << "\n";
  for (Id id(0); id < Id(map_.size()); ++id) {
    auto remap_id = remap[id];
    // llvm::dbgs() << "remap: " << id << " -> " << remap_id << "\n";
    new_map[static_cast<size_t>(remap_id)] = map_[static_cast<size_t>(id)];
  }
  map_ = std::move(new_map);
  // llvm::dbgs() << "map_'s new size is: " << map_.size() << "\n";

  // Now update our constMap
  for (auto &pr : constMap_) {
    pr.second = remap[pr.second];
  }
  // revMap
  for (auto &pr : revMap_) {
    pr.second = remap[pr.second];
  }
  // allocRevMap
  for (auto &pr : allocRevMap_) {
    for (auto &id : pr.second) {
      id = remap[id];
    }
  }
  // named
  for (auto &pr : named_) {
    pr.second = remap[pr.second];
  }
  for (auto &pr : allocs_) {
    auto remap_id = remap[pr.first];
    assert(remap_id != Id::invalid());
    pr.first = remap_id;
  }

  return std::move(remap);
}


