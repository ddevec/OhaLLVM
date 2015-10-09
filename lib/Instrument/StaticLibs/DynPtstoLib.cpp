/*
 * Copyright (C) 2015 David Devecsery
 */

#include <cassert>
#include <cstdint>
#include <cstdio>

#include <iostream>
#include <map>
#include <set>
#include <string>
#include <vector>

class AddrRange {
 public:
    explicit AddrRange(void *addr) :
        start_(reinterpret_cast<intptr_t>(addr)),
        end_(start_+1) { }

    AddrRange(void *addr, int64_t size) :
        start_(reinterpret_cast<intptr_t>(addr)),
        end_(reinterpret_cast<intptr_t>(addr)+size) { }

    bool operator<(const AddrRange &r) const {
      // NOTE: end is not inclusive
      return (start_ < r.start_ && end_ <= r.start_);
    }

 private:
    intptr_t start_;
    intptr_t end_;
};

std::map<AddrRange, int32_t> addr_to_objid;
std::map<int32_t, std::set<int32_t>> valid_to_objids;
std::vector<std::vector<void *>> stack_allocs;

extern "C" {

void __DynPtsto_do_init() { }

void __DynPtsto_do_finish() {
  std::string outfilename("dyn_ptsto.log");

  FILE *out = fopen(outfilename.c_str(), "w");
  // Print to the logfile
  for (auto &val_pr : valid_to_objids) {
    fprintf(out, "%u:", val_pr.first);

    for (auto &obj_id : val_pr.second) {
      fprintf(out, " %d", obj_id);
    }
    fprintf(out, "\n");
  }
}

void __DynPtsto_do_call() {
  // Push a frame on the "stack"
  stack_allocs.emplace_back();
}


void __DynPtsto_do_alloca(int32_t obj_id, int64_t size,
    void *addr) {
  // Size is in bits...
  size /= 8;
  // Handle alloca
  // Add addresses to stack frame
  std::cout << "stacking: (" << obj_id << ") " << addr << std::endl;
  stack_allocs.back().push_back(addr);
  // Add ptstos to ptsto map
  auto ret = addr_to_objid.emplace(AddrRange(addr, size), obj_id);
  assert(ret.second);
}

void __DynPtsto_do_ret() {
  // Remove all ptstos on stack from map
  const std::vector<void *> &cur_frame = stack_allocs.back();
  for (auto addr : cur_frame) {
    std::cout << "popping: " << addr << std::endl;
    auto ret = addr_to_objid.erase(AddrRange(addr));
    assert(ret == 1);
  }

  // Pop ptsto frame from stack
  stack_allocs.pop_back();
}

void __DynPtsto_do_malloc(int32_t obj_id, int64_t size,
    void *addr) {
  // Size is in bits...
  size /= 8;
  // Add ptsto to map
  std::cout << "mallocing: (" << obj_id << ") " << addr << ", "
    << size << std::endl;
  // auto ret =
  addr_to_objid.emplace(AddrRange(addr, size), obj_id);
  // assert(ret.second);
}

void __DynPtsto_do_free(void *addr) {
  // Remove ptsto from map
  std::cout << "freeing: " << addr << std::endl;
  addr_to_objid.erase(AddrRange(addr));
}

void __DynPtsto_do_visit(int32_t val_id, void *addr) {
  // Record that this val_id pts to this addr
  // std::cout << "visit: Addr is " << addr << std::endl;
  auto it = addr_to_objid.find(AddrRange(addr));
  if (it != std::end(addr_to_objid)) {
    int32_t obj_id = addr_to_objid.at(AddrRange(addr));
    valid_to_objids[val_id].insert(obj_id);
  } else {
    std::cout << "  !!Found unmapped addr: " << addr << std::endl;
  }
}

}
