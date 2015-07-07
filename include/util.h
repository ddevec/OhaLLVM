/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_UTIL_H_
#define INCLUDE_UTIL_H_

#include <limits>

#include "llvm/Support/raw_ostream.h"

template<class T = uint64_t, T initial_value = T(0),
  T invalid_value = std::numeric_limits<T>::max()>
class UniqueIdentifier {
 public:
    UniqueIdentifier() = default;
    explicit UniqueIdentifier(const T &init) : val_(init) { }

    static T invalid() {
      return invalid_value;
    }

    static bool isInvalid(const T &val) {
      return val == invalid();
    }

    bool check(const T &val) {
      assert(val < val_);
    }

    T next() {
      return val_++;
    }

 private:
    T val_ = initial_value;
};

template<class Tag, class impl, impl default_value>
class ID {
 public:
  typedef impl base_type;
  static ID invalid() { return ID(); }

  struct hasher {
    std::size_t operator()(const ID &id) const {
      return std::hash<impl>()(id.val());
    }
  };

  // Defaults to ID::invalid()
  ID() = default;

  // Explicit constructor:
  constexpr explicit ID(impl val) : m_val(val) { }

  // Allow copy
  ID(const ID &) = default;

  // Assignment operator
  ID &operator=(const ID &) = default;

  // Explicit conversion to get back the impl:
  explicit operator impl() const { return m_val; }

  constexpr impl val() const { return m_val; }

  bool operator<(const ID &id) const {
    return m_val < id.m_val;
  }

  bool operator>(const ID &id) const {
    return m_val > id.m_val;
  }

  bool operator>=(const ID &id) const {
    return m_val >= id.m_val;
  }

  bool operator<=(const ID &id) const {
    return m_val <= id.m_val;
  }

  bool valid() const {
    return *this != invalid();
  }

  friend bool operator==(ID a, ID b) { return a.m_val == b.m_val; }
  friend bool operator!=(ID a, ID b) { return a.m_val != b.m_val; }

  template <typename T, class T2, T2 DV>
  friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
      const ID<T, T2, DV> &id);

 private:
  impl m_val = default_value;
};

template<class Tag, class impl, impl default_value>
llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
     const ID<Tag, impl, default_value> &id) {
  o << id.m_val;
  return o;
}

#endif  // INCLUDE_UTIL_H_
