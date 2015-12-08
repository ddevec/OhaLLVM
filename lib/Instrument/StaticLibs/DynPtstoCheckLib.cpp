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

static std::map<AddrRange, std::vector<int32_t>> addr_to_objid;
static std::unordered_map<int32_t, std::set<int32_t>> valid_to_objids;
static std::vector<std::vector<void *>> stack_allocs;

extern "C" {

void __ptscheck_do_init() { }

void __ptscheck_do_finish() {
  /*
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
  */
}

void __ptscheck_do_malloc(int32_t obj_id, int64_t size,
    void *addr);
void __ptscheck_main_init2(int32_t obj_id, int32_t argv_dest_id,
    int argc, char **argv) {
  for (int i = 0; i < argc; i++) {
    __ptscheck_do_malloc(argv_dest_id, (strlen(argv[i])+1)*8, argv[i]);
  }

  __ptscheck_do_malloc(obj_id, (sizeof(*argv)*argc+1)*8, argv);
}

void __ptscheck_main_init3(int32_t obj_id, int32_t argv_dest_id,
    int argc, char **argv, char **envp) {
  // Init envp
  int i;
  for (i = 0; envp[i] != nullptr; i++) {
    __ptscheck_do_malloc(argv_dest_id, (strlen(envp[i])+1)*8, envp[i]);
  }
  __ptscheck_do_malloc(obj_id, (sizeof(*envp)*i)*8, envp);

  // Do std init
  __ptscheck_main_init2(obj_id, argv_dest_id, argc, argv);
}

void __ptscheck_do_call() {
  // Push a frame on the "stack"
  stack_allocs.emplace_back();
}


void __ptscheck_do_alloca(int32_t obj_id, int64_t size,
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
    addr_to_objid.emplace(AddrRange(addr, size),
        std::vector<int32_t>(1, obj_id));
  assert(ret.second);
}

void __ptscheck_do_ret() {
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

void __ptscheck_do_malloc(int32_t obj_id, int64_t size,
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
  // assert(ret.second);
}

void __ptscheck_do_free(void *addr) {
  // Remove ptsto from map
  // std::cout << "freeing: " << addr << std::endl;
  // We shouldn't have double allocated anything except globals, which are never
  //   freed
  assert(addr_to_objid.at(AddrRange(addr)).size() == 1);
  addr_to_objid.erase(AddrRange(addr));
}

void __ptscheck_do_visit(int32_t /*size*/, int32_t val_id, void *addr) {
  // Record that this val_id pts to this addr
  // std::cout << "visit: Addr is " << addr << std::endl;
  // if (valid_to_objids[val_id].size() < (size_t)size) {
    auto it = addr_to_objid.find(AddrRange(addr));
    if (it != std::end(addr_to_objid)) {
      for (int32_t obj_id : it->second) {
        valid_to_objids[val_id].insert(obj_id);
      }
    } else {
      // FIXME: 3 is the universal value...
      //    I should have this imported somewhere instead of hardcoded...
      valid_to_objids[val_id].insert(3);
    }
  // }
}

}
