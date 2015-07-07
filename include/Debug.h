/*
 * Copyright (C) 2015 David Devecsery
 */
#ifndef INCLUDE_DEBUG_H_
#define INCLUDE_DEBUG_H_

#include <cstdint>

#include "llvm/Support/raw_ostream.h"

class null_ostream : public llvm::raw_ostream {
  //{{{
 public:
    ~null_ostream() {
      flush();
    }

    // Singleton instance
    static null_ostream &nullstream();

 private:
    static null_ostream nullstream_;

    virtual void write_impl(const char *, size_t) { }

    virtual uint64_t current_pos() const { return 0; }
  //}}}
};


// TODOs  NOLINT
#define DO_PRAGMA(x) _Pragma (#x)
#define TODO(x) DO_PRAGMA(message ("TODO - " x))
#define FIXME(x) DO_PRAGMA(message ("FIXME - " x))

// NOTE: DEBUG is defined at the top of each c file when needed!
// debug on/off statements
#ifdef SPECSFS_DEBUG
#define if_debug(...) __VA_ARGS__
#define if_not_debug(...)
#define if_else_debug(X, Y) X
#define debug_or_true(X) X
#define debug_or_false(X) X
#else
#define if_debug(...)
#define if_not_debug(...) __VA_ARGS__
#define if_else_debug(X, Y) Y
#define debug_or_true(X) true
#define debug_or_false(X) false
#endif

// printing
#ifdef SPECSFS_DEBUG
#define dout dbgs()
#else
#define dout null_ostream::nullstream()
#endif

#endif  // INCLUDE_DEBUG_H_

