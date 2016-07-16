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

#define INVALID_ID (-1)

// We have a stack per thread
std::mutex inst_lock;
std::set<std::vector<int32_t>> all_stacks;
thread_local std::vector<int32_t> stack;
thread_local bool pushed;

thread_local std::unordered_map<void *, std::pair<size_t, int32_t>>
    addr_to_frame;

extern "C" {

void __DynContext_do_init() { }

void __DynContext_do_finish() {
  const char *logname = "profile.callstack";

  char *envname = getenv("SFS_LOGFILE");
  if (envname != nullptr) {
    logname = envname;
  }

  std::ostringstream outfilename;

  outfilename << logname << "." << getpid();

  std::ofstream ofil(outfilename.str());

  std::unique_lock<std::mutex> lk(inst_lock);

  for (auto &vec : all_stacks) {
    for (auto &elm : vec) {
      ofil << elm << " ";
    }
    ofil << std::endl;
  }
}

// Do Call -- no recursion counting
void __DynContext_do_call(int32_t id) {
  if (stack.empty() || stack.back() != id) {
    stack.push_back(id);
    pushed = true;
  }
}

static void save_stack(const std::vector<int32_t> &stack) {
  std::unique_lock<std::mutex> lk(inst_lock);

  /*
  // Clean Stack
  std::vector<int32_t> new_stack;
  int32_t last_elm = -1;
  for (auto elm : stack) {
    // Remove recursive repititions
    if (last_elm != elm) {
      new_stack.push_back(elm);
    }

    last_elm = elm;
  }

  all_stacks.emplace(std::move(new_stack));
  */

  all_stacks.emplace(stack);
}

// Do ret -- Don't pop if we didn't just return from ourself
void __DynContext_do_ret(int32_t id) {
  /*
  if (pushed) {
    save_stack(stack);
    pushed = false;
  }
  stack.pop_back();
  */
  if (pushed) {
    save_stack(stack);
    pushed = false;
  }

  // if (!stack.empty() && stack.back() == id)
  if (stack.back() == id) {
    stack.pop_back();
  }
}

// longjmp support... meh
void __DynContext_do_longjmp_call(int32_t, void *jmpstruct) {
  // Save the stack (if it needs saving), pop it back to jmpstruct
  if (pushed) {
    save_stack(stack);
    pushed = false;
  }

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

// Never called
void __DynContext_do_longjmp_ret(int32_t, void *) {
  assert(0 && "Should never be called");
}

void __DynContext_do_setjmp_call(int32_t, void *jmpstruct) {
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

void __DynContext_do_setjmp_ret(int32_t, void *) {
  assert(0 && "Should never be called");
}

}

