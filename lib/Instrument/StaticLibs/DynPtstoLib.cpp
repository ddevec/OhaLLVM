/*
 * Copyright (C) 2015 David Devecsery
 */

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstring>

#include <iostream>
#include <unordered_map>
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

    bool operator==(const AddrRange &r) const {
      // NOTE: end is not inclusive
      return (start_ == r.start_);
    }

 private:
    friend struct std::hash<AddrRange>;
    intptr_t start_;
    intptr_t end_;
};

namespace std {
template <>
struct hash<AddrRange> {
  std::size_t operator()(const AddrRange &k) const {
    return (std::hash<intptr_t>()(k.start_));
  }
};
}  // namespace std

std::unordered_map<AddrRange, int32_t> addr_to_objid;
std::unordered_map<int32_t, std::set<int32_t>> valid_to_objids;
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

void __DynPtsto_do_malloc(int32_t obj_id, int64_t size,
    void *addr);
void __DynPtsto_main_init2(int32_t obj_id, int argc, char **argv) {
  for (int i = 0; i < argc; i++) {
    // FIXME: this is hacky
    // The data pointed to by argv is part of the argv object, which is argv
    //   value + 1...
    __DynPtsto_do_malloc(obj_id+1, (strlen(argv[i])+1)*8, argv[i]);
  }
  __DynPtsto_do_malloc(obj_id, (sizeof(*argv)*argc+1)*8, argv);
}

void __DynPtsto_main_init3(int32_t obj_id, int argc, char **argv,
    char **envp) {
  // Init envp
  int i;
  for (i = 0; envp[i] != nullptr; i++) {
    __DynPtsto_do_malloc(obj_id, (strlen(envp[i])+1)*8, envp[i]);
  }
  __DynPtsto_do_malloc(obj_id, (sizeof(*envp)*i)*8, envp);

  // Do std init
  __DynPtsto_main_init2(obj_id, argc, argv);
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
  // std::cout << "stacking: (" << obj_id << ") " << addr << std::endl;
  stack_allocs.back().push_back(addr);
  // Add ptstos to ptsto map
#ifndef NDEBUG
  auto ret =
#endif
    addr_to_objid.emplace(AddrRange(addr, size), obj_id);
  assert(ret.second);
}

void __DynPtsto_do_ret() {
  // Remove all ptstos on stack from map
  const std::vector<void *> &cur_frame = stack_allocs.back();
  for (auto addr : cur_frame) {
    // std::cout << "popping: " << addr << std::endl;
#ifndef NDEBUG
    auto ret =
#endif
      addr_to_objid.erase(AddrRange(addr));
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
  /*
  std::cout << "mallocing: (" << obj_id << ") " << addr << ", "
    << size << std::endl;
  */
  // auto ret =
  addr_to_objid.emplace(AddrRange(addr, size), obj_id);
  // assert(ret.second);
}

void __DynPtsto_do_free(void *addr) {
  // Remove ptsto from map
  // std::cout << "freeing: " << addr << std::endl;
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
    /*
    std::cout << "  !!Found unmapped addr: " << addr <<
      " val_id: " << val_id << std::endl;
    */
    // abort();
  }
}

}
