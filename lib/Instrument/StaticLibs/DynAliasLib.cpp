/*
 * Copyright (C) 2015 David Devecsery
 */

#include <sys/types.h>
#include <unistd.h>

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

#include <algorithm>
#include <fstream>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <mutex>
#include <thread>
#include <unordered_map>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#ifndef NDEBUG
#  define if_debug_enabled(...) __VA_ARGS__
#else
#  define if_debug_enabled(...)
#endif

#define sizeof_bits(type) (sizeof(type) * 8)

template <typename T = int32_t,
         T invalid_value = -1>
class AddressMap {
  //{{{
 public:
  typedef T value_type;

  static const value_type InvalidValue = invalid_value;

  static const size_t AddressableMemory = std::numeric_limits<size_t>::max();

  static const size_t Level0Bits = 24;
  static const size_t Level1Bits = 20;
  static const size_t Level2Bits = 20;

  /*
  static const size_t Level0Bits = 16;
  static const size_t Level1Bits = 16;
  static const size_t Level2Bits = 16;
  static const size_t Level3Bits = 16;
  */

  static const size_t NumPages = (1 << Level0Bits);

  // An internal page class
  template <typename next_page, size_t bits>
  class ShadowPageInternal {
    //{{{
   public:
    static const size_t PageSize = (1 << bits);
    static const size_t Mask = PageSize - 1;
    static const size_t EntriesPerPage = next_page::EntriesPerPage * PageSize;
    static const size_t ShiftSize = next_page::ShiftSize + bits;

    value_type get(uintptr_t addr) const {
      auto mask_addr = addrMask(addr);

      if (map_[mask_addr] == nullptr) {
        return InvalidValue;
      }

      return map_[mask_addr]->get(addr);
    }

    void set(value_type val, uintptr_t addr) {
      auto mask_addr = addrMask(addr);

      if (map_[mask_addr] == nullptr) {
        map_[mask_addr] = std::unique_ptr<next_page>(new next_page());
      }

      map_[mask_addr]->set(val, addr);
    }

    size_t set(value_type val, uintptr_t addr, size_t size) {
      size_t orig_size = size;

      while (size) {
        auto mask_addr = addrMask(addr);

        if (map_[mask_addr] == nullptr) {
          map_[mask_addr] = std::unique_ptr<next_page>(new next_page());
        }

        size_t set_size = map_[mask_addr]->set(val, addr, size);

        addr += set_size;
        size -= set_size;
      }

      return orig_size;
    }

   private:
    static uintptr_t addrMask(intptr_t addr) {
      return (addr >> next_page::ShiftSize) & Mask;
    }

    std::array<std::unique_ptr<next_page>, PageSize> map_;
    //}}}
  };

  // A specialization for our bottom-level page
  template<size_t bits>
  class ShadowPageInternal<value_type, bits> {
    //{{{
   public:
    static const size_t PageSize = (1 << bits);
    static const size_t Mask = PageSize - 1;
    static const size_t EntriesPerPage = PageSize;
    static const size_t ShiftSize = bits;

    value_type get(uintptr_t addr) const {
      auto mask_addr = addr & Mask;

      return map_[mask_addr];
    }

    void set(value_type val, uintptr_t addr) {
      auto mask_addr = addr & Mask;

      map_[mask_addr] = val;
    }

    size_t set(value_type val, uintptr_t addr, size_t size) {
      auto mask_size = addr & Mask;

      size = std::min(size, PageSize - mask_size);
      assert(size <= PageSize);

      auto it = std::begin(map_);
      std::advance(it, mask_size);
      auto en = it;
      std::advance(en, size);

      std::fill(it, en, val);
      return size;
    }

   private:
    std::array<value_type, PageSize> map_;
    //}}}
  };

  // typedef ShadowPageInternal<value_type, Level3Bits> Level3Page;
  typedef ShadowPageInternal<value_type, Level2Bits> Level2Page;
  typedef ShadowPageInternal<Level2Page, Level1Bits> Level1Page;
  typedef ShadowPageInternal<Level1Page, Level0Bits> Level0Page;

  static_assert(Level0Page::ShiftSize == sizeof_bits(void *),
      "Pagemap cannot address full address space");

  AddressMap() { }

  value_type get(uintptr_t addr) const {
    return map_.get(addr);
  }

  value_type get(void *addr) const {
    return get(reinterpret_cast<uintptr_t>(addr));
  }

  void set(value_type val, uintptr_t addr, size_t size) {
    map_.set(val, addr, size);
  }

  void set(value_type val, void *addr, size_t size) {
    set(val, reinterpret_cast<uintptr_t>(addr), size);
  }

  void set(value_type val, uintptr_t addr) {
    map_.set(val, addr);
  }

  void set(value_type val, void *addr) {
    set(val, reinterpret_cast<uintptr_t>(addr));
  }

 private:
  Level0Page map_;
  //}}}
};

// std::mutex inst_lock;

static AddressMap<int32_t> map;

std::unordered_map<int32_t, std::set<int32_t>> load_to_store_alias;

std::unordered_map<void *, size_t> allocs;

thread_local std::vector<std::vector<void *>> stack_allocs;
// Used to pop jmp_env's from the stack on pop
thread_local std::vector<std::vector<std::map<void *, std::pair<size_t, size_t>>::iterator>> stack_longjmps;  // NOLINT
// Used to lookup the stack location jumped to
thread_local std::map<void *, std::pair<size_t, size_t>> longjmps;  // NOLINT


extern "C" {

void __DynAlias_do_init() { }

void __DynAlias_do_finish() {
  const char *logname = "profile.alias";

  char *envname = getenv("SFS_LOGFILE");
  if (envname != nullptr) {
    logname = envname;
  }

  std::ostringstream outfilename;

  outfilename << logname << "." << getpid();

  // If there is already an outfilename, merge the two
  /*
  {
    std::ifstream logfile(outfilename.str());
    if (logfile.is_open()) {
      for (std::string line; std::getline(logfile, line, ':'); ) {
        // First parse the first int till the :
        int32_t call_id = stoi(line);

        auto &fcn_set = load_to_store_alias[call_id];

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
  */

  // Now, create the outfile
  std::ofstream ofil(outfilename.str());

  // Write out counts:
  for (auto &val_pr : load_to_store_alias) {
    ofil << val_pr.first << ":";

    for (int32_t id : val_pr.second) {
      ofil << " " << id;
    }
    ofil << std::endl;
  }
}

void __DynAlias_do_malloc(int32_t obj_id, int64_t size,
    void *addr);
void __DynAlias_main_init2(int32_t argv_id, int32_t arg_id,
    int32_t /*envp_id*/, int32_t /*env_id*/,
    int argc, char **argv) {

  int i = 0;
  for (i = 0; i < argc; i++) {
    __DynAlias_do_malloc(arg_id, (strlen(argv[i])+1), argv[i]);
  }

  __DynAlias_do_malloc(argv_id, (sizeof(*argv)*(argc+1)), argv);
}

void __DynAlias_main_init3(int32_t argv_id, int32_t arg_id,
    int32_t envp_id, int32_t env_id,
    int argc, char **argv, char **envp) {
  // Init envp
  int i;
  for (i = 0; envp[i] != nullptr; i++) {
    __DynAlias_do_malloc(env_id, (strlen(envp[i])+1), envp[i]);
  }
  // Also do for the nullptr
  __DynAlias_do_malloc(env_id, (1), envp[i]);

  __DynAlias_do_malloc(envp_id, (sizeof(*envp)*(i+1)), envp);

  // Do std init
  __DynAlias_main_init2(argv_id, arg_id, envp_id, env_id, argc, argv);
}

void __DynAlias_do_call() {
  // Push a frame on the "stack"
  stack_allocs.emplace_back();
  stack_longjmps.emplace_back();
}

void __DynAlias_do_alloca(int32_t, int64_t size,
    void *addr) {
  // Can happen on some null allocations *glares at getenv*
  if (size == 0) {
    return;
  }

  if (addr == nullptr) {
    return;
  }

  // Handle alloca
  // Add addresses to stack frame
  // std::cout << "stacking: (" << obj_id << ") " << addr << std::endl;
  stack_allocs.back().push_back(addr);

  // std::unique_lock<std::mutex> lk(inst_lock);
  /*
  std::cerr << "alloca addr: " << addr << ", " <<
    reinterpret_cast<void *>(reinterpret_cast<uintptr_t>(addr) + size)
    << "\n";
  */
  allocs.emplace(addr, size);

  /*
  if (obj_id == 42665) {
    std::cerr << "Allocating " << obj_id << " at: " <<
      AddrRange(addr, size) << "\n";
  }
  */

  // Add ptstos to ptsto map
  // map.set(obj_id, addr, size);

  // std::cout << "base_locs alloca: " << ret.first->first << std::endl;
}

static bool do_free_addr(void *addr) {
  bool ret = false;

  // std::cerr << "Finding addr: " << addr << "\n";
  auto it = allocs.find(addr);

  assert(it != std::end(allocs));


  map.set(AddressMap<int32_t>::InvalidValue, addr, it->second);

  /*
  int count = 0;
  std::for_each(pr.first, pr.second,
      [&ret, &count, &pr]
      (std::pair<void * const, void *> &pr_it) {
    count++;
    auto free_addr = pr_it.second;
    // std::cout << "popping: " << addr << std::endl;
    auto rc = (addr_to_objid.erase(AddrRange(free_addr)) != 1);
    if (rc) {
      std::cout << "do_free failed on: " << free_addr << std::endl;
      std::cout << "   range is: " << count << " of " <<
          std::distance(pr.first, pr.second) << std::endl;
    }
    ret |= rc;
  });
  */

  return ret;
}

void __DynAlias_do_ret() {
  // Remove all ptstos on stack from map
  const std::vector<void *> &cur_frame = stack_allocs.back();
  // std::unique_lock<std::mutex> lk(inst_lock);
  for (auto addr : cur_frame) {
    bool rc = do_free_addr(addr);
    if (rc) {
      // Do ret failed?
      std::cerr << "Do ret failed to erase address: " << addr << std::endl;
      assert(0 && "do_ret failed");
    }
  }
  // Pop ptsto frame from stack
  stack_allocs.pop_back();

  // Also pop the setjumps...
  for (auto &it : stack_longjmps.back()) {
    longjmps.erase(it);
  }
  stack_longjmps.pop_back();
}

void __DynAlias_do_setjmp(int32_t, void *addr) {
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

void __DynAlias_do_longjmp(int32_t id, void *addr) {
  // Look up our jump in the map...
  auto jump_pr = longjmps.at(addr);

  // std::unique_lock<std::mutex> lk(inst_lock);
  // Now, free the later frames from the vector
  // while (std::next(jump_pr.first) != std::end(stack_allocs))
  for (size_t i = stack_allocs.size()-1; i > jump_pr.first; --i) {
    const std::vector<void *> &cur_frame = stack_allocs[i];
    for (auto addr : cur_frame) {
      auto ret = do_free_addr(addr);
      if (ret) {
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
      do_free_addr(addr);
    assert(!ret);
    vec.pop_back();
  }

  // stack_allocs.back().erase(jump_pr.second, std::end(stack_allocs.back()));
}

void __DynAlias_do_malloc(int32_t, int64_t size,
    void *addr) {
  // Don't allocate nullptr
  if (addr == nullptr) {
    return;
  }
  /*
  std::cout << "do_malloc: " << obj_id << ", " << size << ", " <<
    addr << std::endl;
  */

  /*
  std::cout << "do_malloc (bytes): " << obj_id << ", " << size << ", " <<
    addr << std::endl;
  */

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

  /*
  if (obj_id == 42665) {
    std::cerr << "Allocating " << obj_id << " at: " << cur_range << "\n";
  }
  */

  // map.set(obj_id, addr, size);
  // std::cout << "  do_malloc range: " << cur_range << std::endl;

  // If we overlap, but are not equal
  // XXX:  Should only happen for globals, so I'm ignoring this in base_loc
  // calcualtions
  // bool glbl = false;
  /*
  while (!ret.second && ret.first->first.overlaps(cur_range)) {
    // Allocated multiple times... because its static and external to the
    //    program
    if (obj_id == 9) {
      ret.second = true;
      break;
    }
    if (addr == nullptr) {
      return;
    }

    // Replace ret...
    auto vec = std::move(ret.first->second);
    int64_t new_addr = std::min(ret.first->first.start(), cur_range.start());
    int64_t new_len = std::max(cur_range.end() - new_addr,
        ret.first->first.end() - new_addr);
    AddrRange new_range(reinterpret_cast<void *>(new_addr), new_len);
    // std::cerr << "new range is: " << ret.first->first << std::endl;
    addr_to_objid.erase(ret.first);
    ret = addr_to_objid.emplace(new_range, std::move(vec));
    // glbl = true;
  }
  */

  /*
  if (glbl) {
    std::cout << "base_locs malloc (glbl): " << ret.first->first << std::endl;
  } else {
    std::cout << "base_locs malloc: (" << obj_id << ") " <<
      ret.first->first << std::endl;
  }
  */
  // base_locs.emplace(addr, ret.first->first.addr());

  // std::unique_lock<std::mutex> lk(inst_lock);
  /*
  std::cerr << "malloc addr: " << addr << ", " <<
    reinterpret_cast<void *>(reinterpret_cast<uintptr_t>(addr) + size)
    << "\n";
  */
  allocs.emplace(addr, size);
  /*
  ret.first->second.addId(obj_id);
  assert(ret.second);
  */
}

void __DynAlias_do_load(int32_t load_id, void *addr, size_t) {
  // std::unique_lock<std::mutex> lk(inst_lock);

  auto id = map.get(addr);
  /*
  if (load_id == 11061) {
    std::cerr << "Loading from: " << load_id << " at: " << addr << " size: " <<
      size << std::endl;
    std::cerr << "  got id: " << id << std::endl;
  }
  */

  load_to_store_alias[load_id].insert(id);
}

void __DynAlias_do_store(int32_t store_id, void *addr, size_t size) {
  // Convert from bits to bytes
  // std::unique_lock<std::mutex> lk(inst_lock);

  /*
  if (store_id == 10923) {
    std::cerr << "Storing to: " << store_id << " at: " << addr << " size: " <<
      size << std::endl;
  }
  */
  map.set(store_id, addr, size);
}

void __DynAlias_do_free(void *addr) {
  if (addr == nullptr) {
    return;
  }
  // Remove ptsto from map
  // std::cout << "freeing: " << addr << std::endl;
  // We shouldn't have double allocated anything except globals, which are never
  //   freed
  // std::unique_lock<std::mutex> lk(inst_lock);
  do_free_addr(addr);
}

}
