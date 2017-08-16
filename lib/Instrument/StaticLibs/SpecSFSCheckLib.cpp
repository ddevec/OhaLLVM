/*
 * Copyright (C) 2015 David Devecsery
 */

#include <execinfo.h>

#include <signal.h>
#include <sys/types.h>
#include <unistd.h>

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstring>

#include <algorithm>
#include <iostream>
#include <map>
#include <unordered_map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#define IN_INS

#include "include/BloomHash.h"

static int64_t filter_check = 0;
static int64_t filter_miss = 0;


/*
[[ gnu::constructor ]]
void init(void) {
}
*/

[[ gnu::destructor ]]
void fini(void) {
  std::cerr << "filter good: " << filter_check << std::endl;
  std::cerr << "filter miss: " << filter_miss << std::endl;
}

[[ gnu::unused ]]
static void print_trace(void) {
  void *array[10];
  size_t size;
  char **strings;
  size_t i;

  size = backtrace(array, 10);
  strings = backtrace_symbols(array, size);

  std::cerr << "BACKTRACE:" << std::endl;
  for (i = 0; i < size; i++) {
    std::cerr << "\t" << strings[i] << std::endl;
  }

  free(strings);
}

int parent_pid = 1;
[[ gnu::constructor ]]
static void premain(void) {
  parent_pid = getpid();
}

[[ gnu::unused ]]
static void do_exit(void) {
  std::cerr << "MisSpecFinish" << std::endl;
  std::cerr.flush();
  if (getpid() != parent_pid) {
    kill(parent_pid, SIGQUIT);
  }
  kill(getpid(), SIGQUIT);
}



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
    friend struct std::hash<AddrRange>;
    intptr_t start_;
    intptr_t end_;
};

std::map<AddrRange, std::vector<int32_t>> addr_to_objid;
std::vector<std::vector<void *>> stack_allocs;

// Initialize to 0, to represent the "main" call node
thread_local std::vector<std::pair<int32_t, uint64_t>> stack = {
  std::pair<int32_t, uint64_t>(0, 0x5F5F5F5F5F5F5F5FULL) };

thread_local std::unordered_map<void *, std::pair<size_t,
             std::pair<int32_t, uint64_t>>> addr_to_frame;

extern "C" {

void __specsfs_alloc_fcn(int32_t obj_id, void *addr, int64_t size);

void __specsfs_main_init2(int32_t obj_id, int32_t argv_dest_id,
    int argc, char **argv) {
  for (int i = 0; i < argc; i++) {
    __specsfs_alloc_fcn(argv_dest_id, argv[i], (strlen(argv[i])+1)*8);
  }

  __specsfs_alloc_fcn(obj_id, argv, (sizeof(*argv)*argc+1)*8);
}

void __specsfs_main_init3(int32_t obj_id, int32_t argv_dest_id,
    int argc, char **argv, char **envp) {
  // Init envp
  int i;
  for (i = 0; envp[i] != nullptr; i++) {
    __specsfs_alloc_fcn(argv_dest_id, envp[i], (strlen(envp[i])+1)*8);
  }
  __specsfs_alloc_fcn(obj_id, envp, (sizeof(*envp)*i)*8);

  // Do std init
  __specsfs_main_init2(obj_id, argv_dest_id, argc, argv);
}

void __specsfs_do_call() {
  // Push a frame on the "stack"
  stack_allocs.emplace_back();
}

void __specsfs_callstack_push(int32_t id, uint32_t hash) {
  auto &pr = stack.back();
  if (stack.empty() || pr.first != id) {
    auto &cur_hash = pr.second;

    auto new_hash = BloomHasher::mix_hash(cur_hash, hash);
    stack.push_back(std::make_pair(id, new_hash));
  }
}

void __specsfs_callstack_pop(int32_t id) {
  // if (!stack.empty() && stack.back() == id)
  auto &pr = stack.back();
  if (pr.first == id) {
    stack.pop_back();
  }
}

void __specsfs_callstack_check(int32_t check_id, int32_t size, int32_t **ids,
    uint64_t filter_hash[]) {
  // First, check the bloom filter for this set
  auto &stack_hash = stack.back().second;
  filter_check++;

  if (!BloomHasher::bloom_check(filter_hash, stack_hash)) {
    return;
  }
  filter_miss++;

  // Check if stack matches any in ids
  for (int i = 0; i < size; ++i) {
    int32_t *id = ids[i];
    int32_t size = id[0];
    ++id;

    if (size != static_cast<int32_t>(stack.size())) {
      continue;
    }

    bool clear = false;
    for (int j = size-1; j >= 0; --j) {
      if (stack[j].first != id[j]) {
        clear = true;
        break;
      }
    }

    if (!clear) {
      std::cerr << "stack check failed!" << std::endl;
      std::cerr << "check id: " << check_id << std::endl;
      std::cerr << "stack is: {";
      for (int j = 0; j < size; ++j) {
        std::cerr << " " << stack[j].first;
      }
      std::cerr << " }" << std::endl;

      std::cerr << "ids[" << i << "] is: {";
      for (int j = 0; j < size; ++j) {
        std::cerr << " " << id[j];
      }
      std::cerr << " }" << std::endl;

      // print_trace();
      do_exit();
    }
  }
}

// longjmp support... meh
void __specsfs_do_longjmp_call(int32_t, void *jmpstruct, int64_t) {
  // Save the stack (if it needs saving), pop it back to jmpstruct
  auto it = addr_to_frame.find(jmpstruct);
  assert(it != std::end(addr_to_frame));

  // IF we returned to an element w/in an scc, stack.size() will be one less
  // than the recorded size, in which case, we push the frame back on...
  if (stack.size() < it->second.first) {
    assert(stack.size() + 1 == it->second.first);
    stack.push_back(it->second.second);
  // In the expected case, we just dump the top of our stack
  } else {
    stack.resize(it->second.first);
  }
}

void __specsfs_do_setjmp_call(int32_t, void *jmpstruct) {
  // Save the stack, denote we just setjmp'd
  /*
  std::cout << "Dumping stack size: " << stack.size() << std::endl;
  std::cout << "  stack:";
  for (auto &elm : stack) {
    std::cout << " " << elm;
  }
  std::cout << std::endl;
  */

  addr_to_frame[jmpstruct] = std::make_pair(stack.size(), stack.back());
}

void __specsfs_alloca_fcn(int32_t obj_id, void *addr,
    int64_t size) {
  // alloca_cnt++;
  // Size is in bits...
  // Handle alloca
  // Add addresses to stack frame
  stack_allocs.back().push_back(addr);
  // Add ptstos to ptsto map
#ifndef NDEBUG
  auto ret =
#endif
    addr_to_objid.emplace(AddrRange(addr, size),
        std::vector<int32_t>(1, obj_id));
  assert(ret.second);
}

void __specsfs_ret_fcn() {
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

void __specsfs_alloc_fcn(int32_t obj_id, void *addr,
    int64_t size) {
  // malloc_cnt++;
  // Size is in bits...
  // Add ptsto to map
  /*
  if (obj_id == 70 ||
      obj_id == 78 ||
      obj_id == 82 ||
      obj_id == 90 ||
      obj_id == 94 ||
      obj_id == 116 ||
      obj_id == 128 ||
      obj_id == 150 ||
      obj_id == 160 ||
      obj_id == 170 ||
      obj_id == 176 ||
      obj_id == 190 ||
      obj_id == 204 ||
      obj_id == 218 ||
      obj_id == 230 ||
      obj_id == 236 ||
      obj_id == 240 ||
      obj_id == 252 ||
      obj_id == 256 ||
      obj_id == 276 ||
      obj_id == 284 ||
      obj_id == 852 ||
      obj_id == 1024 ||
      obj_id == 1032 ||
      obj_id == 1538) {
    std::cerr << "mallocing: (" << obj_id << ") " << addr << ", "
      << size << std::endl;
  }
  */
  // std::cerr << "allocing: (" << obj_id << ") " << addr << std::endl;

  AddrRange cur_range(addr, size);
  auto ret = addr_to_objid.emplace(cur_range,
      std::vector<int32_t>());

  // FIXME: Maybe unsound?  Will evaluate if have time
  while (!ret.second && ret.first->first.overlaps(cur_range)) {
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

  /*
  std::cerr << "mallocing: (" << obj_id << ") " << addr << ", "
    << size << std::endl;
  */
  ret.first->second.push_back(obj_id);
  // assert(ret.second);
}

void __specsfs_free_fcn(void *addr) {
  // free_cnt++;
  // Remove ptsto from map
  // std::cout << "freeing: " << addr << std::endl;
  addr_to_objid.erase(AddrRange(addr));
}

/*
void __DynPtsto_do_visit(int32_t val_id, void *addr) {
  // Record that this val_id pts to this addr
  // std::cout << "visit: Addr is " << addr << std::endl;
  auto it = addr_to_objid.find(AddrRange(addr));
  if (it != std::end(addr_to_objid)) {
    int32_t obj_id = addr_to_objid.at(AddrRange(addr));
    valid_to_objids[val_id].insert(obj_id);
  } else {
    // FIXME: 3 is the universal value... I should have this imported somewhere
    //   instead of hardcoded...
    valid_to_objids[val_id].insert(3);
  }
}
*/

void __specsfs_visit_fcn(int32_t id) {
  std::cerr << "Visit failed!\n";
  std::cerr << "Visit id: " << id << "\n";
  // print_trace();
  do_exit();
}

void __specsfs_set_check_fcn(int32_t id,
    void *addr, int32_t set[], int32_t set_size) {
  // visit_cnt++;
  // Don't check nulls, they are fine
  if (addr == nullptr) {
    return;
  }

  /*
  std::cerr << "Checking set:";
  for (int i = 0; i < set_size; i++) {
    std::cerr << " " << set[i];
  }
  std::cerr << std::endl;
  */

  int32_t obj_id = -1;
  auto it = addr_to_objid.find(AddrRange(addr));
  bool found = false;
  if (it != std::end(addr_to_objid)) {
    auto &obj_vec = it->second;
    /*
    std::cerr << "objid is: " << obj_id << std::endl;
    std::cerr << "set is:";
    for (int i = 0; i < set_size; i++) {
      std::cerr << " " << set[i];
    }
    std::cerr << std::endl;
    */
    for (auto o_id : obj_vec) {
      found |= std::binary_search(set, set+set_size, o_id);
    }
    obj_id = obj_vec.front();
  }


  if (!found) {
    std::cerr << "set_check_fcn abort!" << std::endl;
    std::cerr << "obj_id is: " << obj_id << std::endl;
    std::cerr << "addr is: " << addr << std::endl;
    std::cerr << "set is:";
    for (int i = 0; i < set_size; i++) {
      std::cerr << " " << set[i];
    }
    std::cerr << std::endl;
    std::cerr << "id is: " << id << std::endl;
    // print_trace();
    do_exit();
  }
}

}

