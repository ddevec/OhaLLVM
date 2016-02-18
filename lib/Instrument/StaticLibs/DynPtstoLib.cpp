/*
 * Copyright (C) 2015 David Devecsery
 */

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstring>

#include <algorithm>
#include <fstream>
#include <iostream>
#include <map>
#include <unordered_map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

#ifndef NDEBUG
#  define if_debug_enabled(...) __VA_ARGS__
#else
#  define if_debug_enabled(...)
#endif

class AddrRange {
 public:
    explicit AddrRange(void *addr) :
        start_(reinterpret_cast<intptr_t>(addr)),
        end_(start_+1) { }

    AddrRange(void *addr, int64_t size) :
        start_(reinterpret_cast<intptr_t>(addr)),
        end_(reinterpret_cast<intptr_t>(addr)+size) { }

    bool overlaps(const AddrRange &tmp) const {
      return (
          // -1 on end b/c it is exclusive
          (tmp.start() < start() && tmp.end() > start()) ||
          (tmp.end() > start() && tmp.start() < end()));
    }

    bool operator<(const AddrRange &r) const {
      // NOTE: end is not inclusive
      return (start_ < r.start_ && end_ <= r.start_);
    }

    bool operator==(const AddrRange &r) const {
      // NOTE: end is not inclusive
      return (start_ == r.start_ && end_ == r.end_);
    }

    intptr_t start() const {
      return start_;
    }

    intptr_t end() const {
      return end_;
    }

    friend std::ostream &operator<<(std::ostream &os, const AddrRange &ar) {
      os << "( " << ar.start() << ", " << ar.end() << " )";
      return os;
    }

 private:
    intptr_t start_;
    intptr_t end_;
};

std::map<AddrRange, std::vector<int32_t>> addr_to_objid;
std::unordered_map<int32_t, std::set<int32_t>> valid_to_objids;
std::vector<std::vector<void *>> stack_allocs;
// Used to pop jmp_env's from the stack on pop
// std::vector<std::vector<std::map<void *, std::pair<std::vector<std::vector<void *>>::iterator, std::vector<void *>::iterator>>::iterator>> stack_longjmps;  // NOLINT
 std::vector<std::vector<std::map<void *, std::pair<size_t, size_t>>::iterator>> stack_longjmps;  // NOLINT
// Used to lookup the stack location jumped to
std::map<void *, std::pair<size_t, size_t>> longjmps;  // NOLINT

extern "C" {

void __DynPtsto_do_init() { }

void __DynPtsto_do_finish() {
  std::string outfilename("dyn_ptsto.log");

  // If there is already an outfilename, merge the two
  {
    std::ifstream logfile(outfilename);
    if (logfile.is_open()) {
      for (std::string line; std::getline(logfile, line, ':'); ) {
        // First parse the first int till the :
        int32_t call_id = stoi(line);

        auto &fcn_set = valid_to_objids[call_id];

        std::getline(logfile, line);
        // Now split the line...
        std::stringstream converter(line);
        int32_t fcn_id;
        converter >> fcn_id;
        while (!converter.fail()) {
          fcn_set.insert(fcn_id);
          converter >> fcn_id;
        }
      }
    }
  }

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
void __DynPtsto_main_init2(int32_t obj_id, int32_t argv_dest_id,
    int argc, char **argv) {
  for (int i = 0; i < argc; i++) {
    __DynPtsto_do_malloc(argv_dest_id, (strlen(argv[i])+1)*8, argv[i]);
  }

  __DynPtsto_do_malloc(obj_id, (sizeof(*argv)*argc+1)*8, argv);
}

void __DynPtsto_main_init3(int32_t obj_id, int32_t argv_dest_id,
    int argc, char **argv, char **envp) {
  // Init envp
  int i;
  for (i = 0; envp[i] != nullptr; i++) {
    __DynPtsto_do_malloc(argv_dest_id, (strlen(envp[i])+1)*8, envp[i]);
  }
  __DynPtsto_do_malloc(obj_id, (sizeof(*envp)*i)*8, envp);

  // Do std init
  __DynPtsto_main_init2(obj_id, argv_dest_id, argc, argv);
}

void __DynPtsto_do_call() {
  // Push a frame on the "stack"
  stack_allocs.emplace_back();
  stack_longjmps.emplace_back();
}


void __DynPtsto_do_alloca(int32_t obj_id, int64_t size,
    void *addr) {
  // Can happen on some null allocations *glares at getenv*
  if (size == 0) {
    return;
  }
  // Size is in bits...
  size /= 8;
  // Handle alloca
  // Add addresses to stack frame
  // std::cout << "stacking: (" << obj_id << ") " << addr << std::endl;
  stack_allocs.back().push_back(addr);
  // Add ptstos to ptsto map
  auto ret =
    addr_to_objid.emplace(AddrRange(addr, size),
        std::vector<int32_t>(1, obj_id));
  if (!ret.second) {
    std::cerr << "failed to place obj_id: " << obj_id << std::endl;
    std::cerr << "old obj_ids are:";
    for (auto &old_obj_id : ret.first->second) {
      std::cerr << " " << old_obj_id;
    }
    std::cerr << std::endl;
  }
  assert(ret.second);
}

void __DynPtsto_do_ret() {
  // Remove all ptstos on stack from map
  const std::vector<void *> &cur_frame = stack_allocs.back();
  for (auto addr : cur_frame) {
    // std::cout << "popping: " << addr << std::endl;
    if_debug_enabled(auto ret =)
      addr_to_objid.erase(AddrRange(addr));
    assert(ret == 1);
  }
  // Pop ptsto frame from stack
  stack_allocs.pop_back();

  // Also pop the setjumps...
  for (auto &it : stack_longjmps.back()) {
    longjmps.erase(it);
  }
  stack_longjmps.pop_back();
}

void __DynPtsto_do_setjmp(int32_t, void *addr) {
  // Add ourself to the longjmp ret, so where know where to return to
  auto stack_pos = std::make_pair(stack_allocs.size()-1,
      stack_allocs.back().size()-1);
  auto rc = longjmps.emplace(addr, stack_pos);

  // We reset a jump without clearing it from the stack
  //   This can happen if setjmp is called 2x on the same jmp_env
  if (!rc.second) {
    rc.first->second = stack_pos;
  }

  // Add ourself to the longjmp stack (so we're cleared on ret)
  stack_longjmps.back().push_back(rc.first);
}

void __DynPtsto_do_longjmp(int32_t id, void *addr) {
  // Look up our jump in the map...
  auto jump_pr = longjmps.at(addr);

  // Now, free the later frames from the vector
  // while (std::next(jump_pr.first) != std::end(stack_allocs))
  for (size_t i = stack_allocs.size()-1; i > jump_pr.first; --i) {
    const std::vector<void *> &cur_frame = stack_allocs[i];
    for (auto addr : cur_frame) {
      // std::cout << "popping: " << addr << std::endl;
      auto ret = addr_to_objid.erase(AddrRange(addr));
      if (ret != 1) {
        std::cerr << "do_longjmp failed at return erase\n";
        std::cerr << "do_longjmp id: " << id << "\n";
        std::cerr << "frame: " << stack_allocs.size()-1 << "\n";
        std::cerr << "addr: " << addr << "\n";
        abort();
      }
    }
    // Pop ptsto frame from stack
    stack_allocs.pop_back();

    // Also pop the setjumps...
    for (auto &it : stack_longjmps.back()) {
      longjmps.erase(it);
    }
    stack_longjmps.pop_back();

    // We should have the same number of frames for both allocs and longjmps
    assert(stack_longjmps.size() == stack_allocs.size());
  }

  // Then free anything after this jump
  /*std::for_each(std::next(jump_pr.second), std::end(stack_allocs.back()),
      [] (void *addr)*/
  auto &vec = stack_allocs.back();
  for (size_t i = vec.size() - 1; i > jump_pr.second; --i) {
    void *addr = vec[i];
    // std::cout << "popping: " << addr << std::endl;
    if_debug_enabled(auto ret =)
      addr_to_objid.erase(AddrRange(addr));
    assert(ret == 1);
    vec.pop_back();
  }

  // stack_allocs.back().erase(jump_pr.second, std::end(stack_allocs.back()));
}

void __DynPtsto_do_malloc(int32_t obj_id, int64_t size,
    void *addr) {
  // Size is in bits...
  size /= 8;

  // Add ptsto to map
  /*
  std::cout << "mallocing: (" << obj_id << ") " << addr << ", "
    << size << std::endl;
  if (obj_id == 66 || obj_id == 1488 || obj_id == 1568) {
    uintptr_t start_addr = reinterpret_cast<uintptr_t>(addr);
    std::cerr << "obj_id: " << obj_id << " => (" << start_addr << ", " <<
      start_addr + size << ")\n";
  }
  */

  AddrRange cur_range(addr, size);

  auto ret = addr_to_objid.emplace(cur_range,
      std::vector<int32_t>());

  // If we overlap, but are not equal
  while (!ret.second && ret.first->first.overlaps(cur_range)) {
    if (addr == nullptr) {
      return;
    }
    /*
    std::cerr << "Couldn't place range: " << cur_range << std::endl;
    std::cerr << "Old range is: " << ret.first->first << std::endl;
    */

    // Replace ret...
    auto vec = std::move(ret.first->second);
    int64_t new_addr = std::min(ret.first->first.start(), cur_range.start());
    int64_t new_len = std::max(cur_range.end() - new_addr,
        ret.first->first.end() - new_addr);
    AddrRange new_range(reinterpret_cast<void *>(new_addr), new_len);
    // std::cerr << "new range is: " << ret.first->first << std::endl;
    addr_to_objid.erase(ret.first);
    ret = addr_to_objid.emplace(new_range, std::move(vec));
  }

  ret.first->second.push_back(obj_id);
  assert(ret.second);
}

void __DynPtsto_do_free(void *addr) {
  // Remove ptsto from map
  // std::cout << "freeing: " << addr << std::endl;
  // We shouldn't have double allocated anything except globals, which are never
  //   freed
  assert(addr_to_objid.at(AddrRange(addr)).size() == 1);
  addr_to_objid.erase(AddrRange(addr));
}

void __DynPtsto_do_visit(int32_t val_id, void *addr) {
  // Record that this val_id pts to this addr
  auto it = addr_to_objid.find(AddrRange(addr));
  if (it != std::end(addr_to_objid)) {
    for (int32_t obj_id : it->second) {
      valid_to_objids[val_id].insert(obj_id);
    }
  } else {
    // FIXME: 3 is the universal value... I should have this imported somewhere
    //   instead of hardcoded...
    valid_to_objids[val_id].insert(3);
  }
}

}
