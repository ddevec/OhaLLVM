/*
 * Copyright (C) 2015 David Devecsery
 */
#ifndef INCLUDE_DEBUG_H_
#define INCLUDE_DEBUG_H_

#include <execinfo.h>

#include <cstdint>

#include <iostream>
#include <fstream>
#include <string>

#ifndef SPECSFS_IS_TEST
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_os_ostream.h"
#include "llvm/Support/Debug.h"
#endif


// Used to remove llvm dependencies on unit tests
#ifdef SPECSFS_IS_TEST
#  define if_unit_test(X) X
#  define if_unit_test_else(X, Y) X
#  define if_not_unit_test(X)
#  define dbg std::cerr
#  define dbg_type std::ostream
#  define dbg_ostream std::ofstream
#  define unreachable(X) abort()

template<typename target_type, typename base_type>
target_type &cast(base_type &b) {
  return *static_cast<target_type *>(&b);
}

template<typename target_type, typename base_type>
const target_type &cast(const base_type &b) {
  return *static_cast<const target_type *>(&b);
}

template<typename target_type, typename base_type>
target_type *cast(base_type *b) {
  return static_cast<target_type *>(b);
}

template<typename target_type, typename base_type>
const target_type *cast(const base_type *b) {
  return static_cast<const target_type *>(b);
}

template<typename target_type, typename base_type>
target_type &dyn_cast(base_type &b) {
  return *static_cast<target_type *>(&b);
}

template<typename target_type, typename base_type>
const target_type &dyn_cast(const base_type &b) {
  return *static_cast<target_type *>(&b);
}

template<typename target_type, typename base_type>
target_type *dyn_cast(base_type *b) {
  return static_cast<target_type *>(b);
}

template<typename target_type, typename base_type>
const target_type *dyn_cast(const base_type *b) {
  return static_cast<const target_type *>(b);
}

#else
#  define if_unit_test(X)
#  define if_unit_test_else(X, Y) Y
#  define if_not_unit_test(X) X
#  define dbg llvm::dbgs()
#  define dbg_type llvm::raw_ostream
#  define dbg_ostream llvm::raw_os_ostream
#  define unreachable(X) llvm_unreachable(X)

/*
#define cast llvm::cast
#define dyn_cast llvm::dyn_cast
#define dyn_cast_or_null llvm::dyn_cast_or_null
*/
using llvm::dyn_cast;
using llvm::cast;
using llvm::dyn_cast_or_null;
#endif

[[ gnu::unused ]]
static void print_trace(void) {
  void *array[10];
  size_t size;
  char **strings;
  size_t i;

  size = backtrace(array, 10);
  strings = backtrace_symbols(array, size);

  dbg << "BACKTRACE:\n";
  for (i = 0; i < size; i++) {
    dbg << "\t" << strings[i] << "\n";
  }

  free(strings);
}

// TODOs  NOLINT
#define DO_PRAGMA(x) _Pragma (#x)
#define TODO(x) DO_PRAGMA(message ("TODO - " x))
#define FIXME(x) DO_PRAGMA(message ("FIXME - " x))

// If debug NDEBUG enabled
#ifndef NDEBUG
#  define if_debug_enabled(...) __VA_ARGS__
#else
#  define if_debug_enabled(...)
#endif

#if (defined(SPECSFS_LOGDEBUG) || defined(SPECSFS_DEBUG)) \
  && !defined(SPECSFS_NODEBUG)
#  define if_print_debug(X) X
#else
#  define if_print_debug(X)
#endif

#if defined(SPECSFS_LOGDEBUG) && !defined(SPECSFS_NODEBUG)
#  if defined(SPECSFS_DEBUG)
#    error "SPECSFS_LOGDEBUG and SPECSFS_DEBUG should not be defined together"
#  endif
#  define logout(X) (dbg << X)
#else
#  define logout(X)
#endif

// NOTE: DEBUG is defined at the top of each c file when needed!
// debug on/off statements
#if defined(SPECSFS_DEBUG) && !defined(SPECSFS_NODEBUG)
#  define if_debug(...) __VA_ARGS__
#  define if_not_debug(...)
#  define if_else_debug(X, Y) X
#  define debug_or_true(X) X
#  define debug_or_false(X) X
#else
#  define if_debug(...)
#  define if_not_debug(...) __VA_ARGS__
#  define if_else_debug(X, Y) Y
#  define debug_or_true(X) true
#  define debug_or_false(X) false
#endif

// printing
#if defined(SPECSFS_DEBUG) && !defined(SPECSFS_NODEBUG)
#  define dout(X) (dbg << X)
#else
#  define dout(X)
#endif

/*
template <typename T>
class DebugVar {
#ifndef NDEBUG
 public:
  DebugVar(T val) : val_(val) { }

  DebugVar &operator=(T val) {
    val_ = val;
  }

  T &operator T() {
    return val_;
  }

  const T &operator T() const {
    return val_;
  }

  T &operator++() {
    return ++val_;
  }

  T &operator++(int) {
    return val_++;
  }

  T &operator--() {
    return ++val_;
  }

  T &operator--(int) {
    return val_++;
  }

 private:
  T val_;
#else
 public:
  DebugVar(T val) { }

  DebugVar &operator=(T val) { }

  T &operator++() { }

  T &operator++(int) { }

  T &operator--() { }

  T &operator--(int) { }
#endif
}
*/

#endif  // INCLUDE_DEBUG_H_

