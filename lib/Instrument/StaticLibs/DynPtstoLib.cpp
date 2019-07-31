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
#include <mutex>
#include <unordered_map>
#include <set>
#include <sstream>
#include <string>
#include <thread>
#include <utility>
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
        end_(start_+1),
        baseAddr_(addr) { }

    AddrRange(void *addr, int64_t size) :
        start_(reinterpret_cast<intptr_t>(addr)),
        end_(reinterpret_cast<intptr_t>(addr)+size),
        baseAddr_(addr) { }

    AddrRange(const AddrRange &) = default;
    AddrRange(AddrRange &&) = default;

    AddrRange &operator=(AddrRange &&) = default;
    AddrRange &operator=(const AddrRange &) = default;

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

    void *base() const {
      return baseAddr_;
    }

    void *addr() const {
      return reinterpret_cast<void *>(start_);
    }

    void *endAddr() const {
      return reinterpret_cast<void *>(end_);
    }

    AddrRange split(intptr_t offs) {
      AddrRange ret(offs, end_, baseAddr_);
      end_ = offs;

      return ret;
    }

    friend std::ostream &operator<<(std::ostream &os, const AddrRange &ar) {
      os << "( " << reinterpret_cast<void *>(ar.start()) << ", " <<
       reinterpret_cast<void *>(ar.end()) << " )";
      return os;
    }

 private:
    AddrRange(intptr_t s, intptr_t e, void *b) : start_(s), end_(e),
        baseAddr_(b) { }

    intptr_t start_;
    // Not inclusive
    // FIXME: Super hacky!
    // Mutable so we can reduce the end w/o changing the element when a key in a
    //    map
    // This is technically illegal.... but it makes our life so much easier, and
    //    will work w/ the standard map implementation
    mutable intptr_t end_;

    void * const baseAddr_;
};

class AddressValue {
 public:
  AddressValue() = default;
  explicit AddressValue(int32_t &obj_id) :
    AddressValue(std::vector<int32_t>(1, obj_id), 0, false) { }
  explicit AddressValue(const std::vector<int32_t> &obj_ids) :
    AddressValue(obj_ids, 0, false) { }
  explicit AddressValue(const std::vector<int32_t> obj_ids,
      int32_t offs, bool gep) :
    objs_(obj_ids), gep_(gep) {
      std::transform(std::begin(objs_), std::end(objs_), std::begin(objs_),
          [offs] (int32_t id) { return id + offs; });
    }

  void addId(int32_t id) {
    objs_.push_back(id);
  }

  bool gep() const {
    return gep_;
  }

  void setGep(int32_t offs, bool force_gep) {
    assert(!gep_);
    gep_ = force_gep;

    std::transform(std::begin(objs_), std::end(objs_), std::begin(objs_),
        [offs] (int32_t id) { return id + offs; });
  }

  size_t size() const {
    return objs_.size();
  }

  const std::vector<int32_t> &ids() const {
    return objs_;
  }

  typedef std::vector<int32_t>::iterator iterator;
  typedef std::vector<int32_t>::const_iterator const_iterator;

  iterator begin() {
    return std::begin(objs_);
  }

  iterator end() {
    return std::end(objs_);
  }

  const_iterator begin() const {
    return std::begin(objs_);
  }

  const_iterator end() const {
    return std::end(objs_);
  }

 private:
  std::vector<int32_t> objs_;
  bool gep_ = false;
};

std::mutex inst_lock;
std::map<AddrRange, AddressValue> addr_to_objid;
std::unordered_map<int32_t, std::set<int32_t>> valid_to_objids;

thread_local std::vector<std::vector<void *>> stack_allocs;
// Used to pop jmp_env's from the stack on pop
// std::vector<std::vector<std::map<void *, std::pair<std::vector<std::vector<void *>>::iterator, std::vector<void *>::iterator>>::iterator>> stack_longjmps;  // NOLINT
thread_local std::vector<std::vector<std::map<void *, std::pair<size_t, size_t>>::iterator>> stack_longjmps;  // NOLINT
// Used to lookup the stack location jumped to
thread_local std::map<void *, std::pair<size_t, size_t>> longjmps;  // NOLINT


// GEP support
// static std::unordered_map<void *, std::vector<AddrRange *>> base_locs;
static std::unordered_multimap<void *, void *> base_locs;

extern "C" {

void __DynPtsto_do_init() { }

void __DynPtsto_do_finish() {
  const char *logname = "dyn_ptsto.log";

  char *envname = getenv("SFS_LOGFILE");
  if (envname != nullptr) {
    logname = envname;
  }

  std::string outfilename(logname);

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
void __DynPtsto_main_init2(int32_t argv_id, int32_t arg_id,
    int32_t /*envp_id*/, int32_t /*env_id*/,
    int argc, char **argv) {
  int i = 0;
  for (i = 0; i < argc; i++) {
    __DynPtsto_do_malloc(arg_id, (strlen(argv[i])+1), argv[i]);
  }

  __DynPtsto_do_malloc(argv_id, (sizeof(*argv)*(argc+1)), argv);
}

void __DynPtsto_main_init3(int32_t argv_id, int32_t arg_id,
    int32_t envp_id, int32_t env_id,
    int argc, char **argv, char **envp) {
  // Init envp
  int i;
  for (i = 0; envp[i] != nullptr; i++) {
    __DynPtsto_do_malloc(env_id, (strlen(envp[i])+1), envp[i]);
  }
  // Also do for the nullptr
  __DynPtsto_do_malloc(env_id, (1), envp[i]);

  __DynPtsto_do_malloc(envp_id, (sizeof(*envp)*(i+1)), envp);

  // Do std init
  __DynPtsto_main_init2(argv_id, arg_id, envp_id, env_id, argc, argv);
}

void __DynPtsto_do_call() {
  // Push a frame on the "stack"
  stack_allocs.emplace_back();
  stack_longjmps.emplace_back();
}

void __DynPtsto_do_gep(int32_t offs, void *base_addr,
    void *res_addr, int64_t size, int32_t /*gep_id*/) {
  static uint64_t gep_count = 0;
  std::unique_lock<std::mutex> lk(inst_lock);

  gep_count++;

  /*
  if (gep_count % 30000 == 0) {
    std::cerr << "gep count: " << gep_count << std::endl;
  }
  */

  // Get the current field at the res_addr
  /*
  std::cout << "gep: " << offs << ", " << res_addr << ", " <<
      size << std::endl;
  */
  auto it = addr_to_objid.find(AddrRange(res_addr));
  if (it == std::end(addr_to_objid)) {
    if (reinterpret_cast<uintptr_t>(res_addr) > 0x1000) {
      /*
      std::cerr << "WARNING: gep addr not found: " << res_addr << " gep_id: " <<
        gep_id <<"\n";
      abort();
      */
    }
    return;
  }
  auto addr = it->first;
  // std::cout << "  addr: " << addr << std::endl;

  auto base_it = addr_to_objid.find(AddrRange(base_addr));

  if (base_it == std::end(addr_to_objid)) {
    std::cerr << "WARNING: BASE addr not found: " << base_addr << "\n";
    std::cerr << "         gep addr: " << res_addr << "\n";
    return;
  }

  auto base_ids = base_it->second.ids();

  bool force_gep = (offs != 0);

  // Now, get the address to associate this free with...
  auto base_hint = base_locs.find(addr.base());
  ++base_hint;

  auto hint_it = it;
  ++hint_it;

  intptr_t pos = reinterpret_cast<intptr_t>(res_addr);
  intptr_t max_pos = reinterpret_cast<intptr_t>(res_addr) + size;
  // std::cout << "init pos: " << reinterpret_cast<void *>(pos) << std::endl;
  // First, check if we have a lower half to split off
  if (addr.start() < pos) {
    // First (base, res_addr-1) is old_id
    // Note, we've already taken care of this
    auto new_addr = addr;
    auto new_end_addr = new_addr.split(reinterpret_cast<intptr_t>(res_addr));
    // assert(new_addr.base() == second.base());

    // assert(it->second.size() == 1);
    /*
    std::cout << "pre: Replacing: " << it->first << " with " << new_addr <<
      std::endl;
    */
    addr_to_objid.erase(it);
    addr_to_objid.emplace_hint(hint_it, new_addr,
        AddressValue(base_ids));

    // std::cout << "pre: Inserting: " << new_end_addr << std::endl;
    auto new_addr_it = addr_to_objid.emplace_hint(hint_it, new_end_addr,
        AddressValue(base_ids));

    /*
    std::cout << "pre: base_locs: " << addr.base() << "gains: " <<
      new_addr_it->first.addr() << std::endl;
    */
    base_locs.emplace_hint(base_hint,
        reinterpret_cast<void *>(addr.base()),
        new_addr_it->first.addr());

    pos = new_addr.end();
    /*
    std::cout << "before pos: " << reinterpret_cast<void *>(pos) << std::endl;
    */
  }

  int itr = 0;
  do {
    assert(itr < 16);
    itr++;
    /*
    std::cout << "int: find on: " << reinterpret_cast<void *>(pos) << std::endl;
    */
    auto addr_it = addr_to_objid.find(
        AddrRange(reinterpret_cast<void *>(pos)));

    // assert(addr_it != std::end(addr_to_objid));
    if (addr_it == std::end(addr_to_objid)) {
      std::cerr << "WARNING: Use of unmapped addr: " <<
        reinterpret_cast<void *>(pos) << std::endl;
      break;
    }

    // Split if too large
    /*
    std::cout << "start addr: " << addr_it->first << std::endl;
    std::cout << "max_pos: " << reinterpret_cast<void *>(max_pos) << std::endl;
    */
    if (addr_it->first.end() > max_pos) {
      auto new_addr = addr_it->first;
      auto new_end_addr = new_addr.split(max_pos);
      assert(new_addr.end() == max_pos);

      /*
      std::cout << "int: Replacing: " << addr_it->first << " with " <<
        new_addr << std::endl;
      std::cout << "int: Inserting: " << new_end_addr << std::endl;
      */
      assert(new_addr.end() == max_pos);
      addr_to_objid.erase(addr_it);
#ifndef NDEBUG
      auto pr_e =
#endif
        addr_to_objid.emplace(new_end_addr,
          AddressValue(base_ids));
      assert(pr_e.second);
#ifndef NDEBUG
      auto new_addr_it =
        pr_e.first;
#endif
      assert(new_addr_it != std::end(addr_to_objid));

      /*
      addr_it = addr_to_objid.emplace_hint(new_addr_it, new_addr,
          AddressValue(base_ids));
      */
      auto pr = addr_to_objid.emplace(new_addr,
          AddressValue(base_ids));
      assert(pr.second);
      addr_it = pr.first;
      assert(addr_it != std::end(addr_to_objid));
      assert(addr_it->first.end() == max_pos);
      assert(addr_it->first == new_addr);

      assert(addr_to_objid.find(AddrRange(new_addr.addr())) !=
          std::end(addr_to_objid));

      assert(new_addr.end() == max_pos);
      /*
      std::cout << "new addr end: " << new_addr.endAddr() << std::endl;

      std::cout << "int: base_locs: " << new_end_addr.base() << " gains: " <<
        new_end_addr.addr() << std::endl;
      */
      base_locs.emplace_hint(base_hint,
          reinterpret_cast<void *>(new_end_addr.base()),
          new_end_addr.addr());
    }

    // do gep on addr_it
    if (!addr_it->second.gep()) {
      addr_it->second.setGep(offs, force_gep);
    }

    /*
    std::cout << "old_pos: " << reinterpret_cast<void *>(pos) << std::endl;
    std::cout << "addr_it->first.end(): " << addr_it->first.endAddr()
      << std::endl;
    */
    pos = addr_it->first.end();
    // Pos should not be greater than max pos at this point
    assert(!(pos > max_pos));
  } while (pos < max_pos);
}


void __DynPtsto_do_alloca(int32_t obj_id, int64_t size,
    void *addr) {
  // Can happen on some null allocations *glares at getenv*
  if (size == 0) {
    return;
  }

  // Handle alloca
  // Add addresses to stack frame
  // std::cout << "stacking: (" << obj_id << ") " << addr << std::endl;
  stack_allocs.back().push_back(addr);

  /*
  if (obj_id == 42665) {
    std::cerr << "Allocating " << obj_id << " at: " <<
      AddrRange(addr, size) << "\n";
  }
  */

  std::unique_lock<std::mutex> lk(inst_lock);
  // Add ptstos to ptsto map
  auto ret =
    addr_to_objid.emplace(AddrRange(addr, size),
        AddressValue(obj_id));
  if (!ret.second) {
    std::cerr << "failed to place obj_id: " << obj_id << std::endl;
    std::cerr << "old obj_ids are:";
    for (auto &old_obj_id : ret.first->second.ids()) {
      std::cerr << " " << old_obj_id;
    }
    std::cerr << std::endl;
  }

  // std::cout << "base_locs alloca: " << ret.first->first << std::endl;
  base_locs.emplace(addr, ret.first->first.addr());
  assert(ret.second);
}

static bool do_free_addr(void *addr) {
  auto pr = base_locs.equal_range(addr);

  bool ret = false;

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

  base_locs.erase(pr.first, pr.second);

  return ret;
}

void __DynPtsto_do_ret() {
  // Remove all ptstos on stack from map
  const std::vector<void *> &cur_frame = stack_allocs.back();
  {
    std::unique_lock<std::mutex> lk(inst_lock);
    for (auto addr : cur_frame) {
      bool rc = do_free_addr(addr);
      if (rc) {
        // Do ret failed?
        std::cerr << "Do ret failed to erase address: " << addr << std::endl;
        assert(0 && "do_ret failed");
      }
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
  std::unique_lock<std::mutex> lk(inst_lock);
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

void __DynPtsto_do_malloc(int32_t obj_id, int64_t size,
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

  AddrRange cur_range(addr, size);

  /*
  if (obj_id == 42665) {
    std::cerr << "Allocating " << obj_id << " at: " << cur_range << "\n";
  }
  */

  std::unique_lock<std::mutex> lk(inst_lock);
  auto ret = addr_to_objid.emplace(cur_range,
      AddressValue());
  // std::cout << "  do_malloc range: " << cur_range << std::endl;

  // If we overlap, but are not equal
  // XXX:  Should only happen for globals, so I'm ignoring this in base_loc
  // calcualtions
  // bool glbl = false;
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
    // glbl = true;
  }

  /*
  if (glbl) {
    std::cout << "base_locs malloc (glbl): " << ret.first->first << std::endl;
  } else {
    std::cout << "base_locs malloc: (" << obj_id << ") " <<
      ret.first->first << std::endl;
  }
  */
  base_locs.emplace(addr, ret.first->first.addr());

  ret.first->second.addId(obj_id);
  assert(ret.second);
}

void __DynPtsto_do_free(void *addr) {
  // Remove ptsto from map
  // std::cout << "freeing: " << addr << std::endl;
  // We shouldn't have double allocated anything except globals, which are never
  //   freed
  std::unique_lock<std::mutex> lk(inst_lock);
  do_free_addr(addr);
}

void __DynPtsto_do_visit(int32_t val_id, void *addr) {
  /*
  if (val_id == 117258) {
    std::cout << "Visit on: " << val_id << " : " << addr << std::endl;
  }
  */
  // Record that this val_id pts to this addr
  std::unique_lock<std::mutex> lk(inst_lock);
  auto it = addr_to_objid.find(AddrRange(addr));
  if (it != std::end(addr_to_objid)) {
    for (int32_t obj_id : it->second) {
      /*
      if (val_id == 117258) {
        std::cout << "   got id: " << obj_id << " at: " <<
          it->first << std::endl;
      }
      */
      valid_to_objids[val_id].insert(obj_id);
    }
  } else {
    // FIXME: 3 is the universal value... I should have this imported somewhere
    //   instead of hardcoded...
    valid_to_objids[val_id].insert(3);
  }
}

}
