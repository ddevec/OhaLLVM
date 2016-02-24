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
  explicit AddressValue(int32_t obj_id) : AddressValue(obj_id, false) { }
  explicit AddressValue(int32_t obj_id, bool gep) : objs_(1, obj_id),
        gep_(gep) { }

  void addId(int32_t id) {
    objs_.push_back(id);
  }

  bool gep() const {
    return gep_;
  }

  void setGep(int32_t new_id, bool force_gep) {
    assert(!gep_);
    assert(size() == 1);
    gep_ = force_gep;

    objs_[0] = new_id;
  }

  size_t size() const {
    return objs_.size();
  }

  int32_t id() const {
    assert(objs_.size() == 1);
    return objs_[0];
  }

  const std::vector<int32_t> ids() const {
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

std::map<AddrRange, AddressValue> addr_to_objid;
std::unordered_map<int32_t, std::set<int32_t>> valid_to_objids;
std::vector<std::vector<void *>> stack_allocs;
// Used to pop jmp_env's from the stack on pop
// std::vector<std::vector<std::map<void *, std::pair<std::vector<std::vector<void *>>::iterator, std::vector<void *>::iterator>>::iterator>> stack_longjmps;  // NOLINT
 std::vector<std::vector<std::map<void *, std::pair<size_t, size_t>>::iterator>> stack_longjmps;  // NOLINT
// Used to lookup the stack location jumped to
std::map<void *, std::pair<size_t, size_t>> longjmps;  // NOLINT


// GEP support
// static std::unordered_map<void *, std::vector<AddrRange *>> base_locs;
static std::unordered_multimap<void *, const AddrRange *> base_locs;

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

void __DynPtsto_do_gep(int32_t offs, void *base_addr,
    void *res_addr, int64_t size) {
  size /= 8;
  // Get the current field at the res_addr
  std::cout << "gep: " << offs << ", " << res_addr << ", " <<
      size << std::endl;
  auto it = addr_to_objid.find(AddrRange(res_addr));
  if (it == std::end(addr_to_objid)) {
    std::cerr << "WARNING: gep addr not found: " << res_addr << "\n";
    return;
  }
  auto addr = it->first;
  std::cout << "  addr: " << addr << std::endl;

  auto base_id = addr_to_objid.at(AddrRange(base_addr)).id();

  bool force_gep = (offs != 0);

  // Now, get the address to associate this free with...
  auto base_hint = base_locs.find(addr.base());
  ++base_hint;

  auto hint_it = it;
  ++hint_it;

  // Split the address into 2 parts

  // This happens if we're looking up an addr that already has a top-level ptsto
  // In this instance, we don't do the first split, instead we assign second to
  // be equal to addr;
  if (reinterpret_cast<intptr_t>(res_addr) == addr.start()) {
    if (!it->second.gep()) {
      it->second.setGep(base_id + offs, force_gep);
    }
    // Check if we need a third
    if (addr.end() != addr.start() + size) {
      // it->second.setGep(offs);
      // Update the id of the GEP range
      assert(it->second.size() == 1);

      auto new_addr = addr;
      auto third = new_addr.split(
          reinterpret_cast<intptr_t>(new_addr.start() + size));
      assert(new_addr.base() == third.base());

      std::cout << "  new_addr: " << new_addr << " -> " <<
        base_id + offs << std::endl;
      std::cout << "    new_addr range: " << it->first << std::endl;
      std::cout << "  third: " << third << " -> " << base_id << std::endl;

      // Second (res_addr, res_addr+size-1) is id + offs
      assert(it->second.size() == 1);
      addr_to_objid.erase(it);
      addr_to_objid.emplace_hint(hint_it, new_addr,
          AddressValue(base_id + offs, force_gep));
      auto a1_it = addr_to_objid.emplace_hint(hint_it,
          third, AddressValue(base_id));

      // Update the free_map, add res_addr, and res_addr+size
      base_locs.emplace_hint(base_hint, reinterpret_cast<void *>(third.base()),
          &a1_it->first);
    }
  } else {
    // First (base, res_addr-1) is old_id
    // Note, we've already taken care of this
    auto new_addr = addr;
    auto second = new_addr.split(reinterpret_cast<intptr_t>(res_addr));
    assert(new_addr.base() == second.base());

    assert(it->second.size() == 1);
    addr_to_objid.erase(it);
    addr_to_objid.emplace_hint(hint_it, new_addr,
        AddressValue(base_id));

    // If we've already covered this address, we're done
    if (second.start() != second.end()) {
      std::cout << "  new addr: " << it->first << " -> " << it->second.id()
        << std::endl;

      // Second (res_addr, res_addr+size-1) is id + offs
      auto a1_it = addr_to_objid.emplace_hint(hint_it,
          second, AddressValue(base_id + offs, force_gep));
      assert(a1_it->first == second);
      assert(a1_it->second.id() == base_id + offs);

      std::cout << "  new second: " << a1_it->first << " -> " <<
        a1_it->second.id() << std::endl;
      // Update the free_map, add res_addr, and res_addr+size
      base_locs.emplace_hint(base_hint, reinterpret_cast<void *>(second.base()),
          &a1_it->first);

      if (second.start() + size != second.end()) {
        auto new_second = a1_it->first;
        auto third = new_second.split(second.start() + size);
        assert(new_second.base() == third.base());
        std::cout << "  second: " << new_second << " -> " << base_id + offs
          << std::endl;

        std::cout << "  third: " << third << " -> " << base_id <<
          std::endl;

        // Third (res_addr+size, base_end) is old_id
        addr_to_objid.erase(a1_it);
        addr_to_objid.emplace_hint(hint_it,
            new_second, AddressValue(base_id + offs, force_gep));

        auto a2_it = addr_to_objid.emplace_hint(hint_it,
            third, AddressValue(base_id));
        base_locs.emplace_hint(base_hint,
            reinterpret_cast<void *>(third.base()),
            &a2_it->first);
      } else {
       std::cout << "  second: " << second << " -> " <<
         (base_id + offs) << std::endl;
      }
    } else {
      // std::cout << "  sanity addr: " << addr << std::endl;
    }
  }

  /*
  intptr_t new_addr = reinterpret_cast<intptr_t>(res_addr) & (~(intptr_t)0xFFF);
  new_addr |= 0x210;

  auto new_it = addr_to_objid.find(
      AddrRange(reinterpret_cast<void *>(new_addr)));
  if (new_it != std::end(addr_to_objid)) {
    std::cout << "  obj at new_addr: " <<
      new_it->second.id() << std::endl;

    std::cout << "  range at new_addr: " <<
      new_it->first << std::endl;
  }
  */

  std::cout << "  obj at res_addr (" << res_addr << "): " <<
    addr_to_objid.at(AddrRange(res_addr)).id() << std::endl;

  std::cout << "  obj at base_addr(" << base_addr << "): " <<
    addr_to_objid.at(AddrRange(base_addr)).id() << std::endl;

  /*
  if (addr_to_objid.at(AddrRange(res_addr)).front() !=
      (addr_to_objid.at(AddrRange(base_addr)).front() + offs)) {
    std::cout << "res_addr: " << res_addr << std::endl;
    std::cout << "obj at res_addr: " <<
      addr_to_objid.at(AddrRange(res_addr)).front() << std::endl;

    std::cout << "base_addr: " << res_addr << std::endl;
    std::cout << "obj at base_addr: " <<
      addr_to_objid.at(AddrRange(base_addr)).front() << std::endl;

    abort();
  }
  */
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
        AddressValue(obj_id));
  if (!ret.second) {
    std::cerr << "failed to place obj_id: " << obj_id << std::endl;
    std::cerr << "old obj_ids are:";
    for (auto &old_obj_id : ret.first->second.ids()) {
      std::cerr << " " << old_obj_id;
    }
    std::cerr << std::endl;
  }

  base_locs.emplace(addr, &(ret.first->first));
  assert(ret.second);
}

static bool do_free_addr(void *addr) {
  auto pr = base_locs.equal_range(addr);

  bool ret = false;

  std::for_each(pr.first, pr.second,
      [&ret] (std::pair<void * const, const AddrRange *> &pr_it) {
    auto &range = *pr_it.second;
    // std::cout << "popping: " << addr << std::endl;
    ret |=
      (addr_to_objid.erase(range) != 1);
  });

  base_locs.erase(pr.first, pr.second);

  return ret;
}

void __DynPtsto_do_ret() {
  // Remove all ptstos on stack from map
  const std::vector<void *> &cur_frame = stack_allocs.back();
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
  std::cout << "do_malloc: " << obj_id << ", " << size << ", " <<
    addr << std::endl;
  // Size is in bits...
  size /= 8;

  std::cout << "do_malloc (bytes): " << obj_id << ", " << size << ", " <<
    addr << std::endl;

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
      AddressValue());
  std::cout << "  do_malloc range: " << cur_range << std::endl;

  // If we overlap, but are not equal
  // XXX:  Should only happen for globals, so I'm ignoring this in base_loc
  // calcualtions
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

  base_locs.emplace(addr, &ret.first->first);

  ret.first->second.addId(obj_id);
  assert(ret.second);
}

void __DynPtsto_do_free(void *addr) {
  // Remove ptsto from map
  // std::cout << "freeing: " << addr << std::endl;
  // We shouldn't have double allocated anything except globals, which are never
  //   freed
  do_free_addr(addr);
}

void __DynPtsto_do_visit(int32_t val_id, void *addr) {
  if (val_id == 6251) {
    std::cout << "Visit on: " << val_id << " : " << addr << std::endl;
  }
  // Record that this val_id pts to this addr
  auto it = addr_to_objid.find(AddrRange(addr));
  if (it != std::end(addr_to_objid)) {
    for (int32_t obj_id : it->second) {
      if (val_id == 6251) {
        std::cout << "   got id: " << obj_id << " at: " <<
          it->first << std::endl;
      }
      valid_to_objids[val_id].insert(obj_id);
    }
  } else {
    // FIXME: 3 is the universal value... I should have this imported somewhere
    //   instead of hardcoded...
    valid_to_objids[val_id].insert(3);
  }
}

}
