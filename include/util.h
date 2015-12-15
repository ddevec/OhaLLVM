/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_UTIL_H_
#define INCLUDE_UTIL_H_

#include <cassert>

#include <atomic>
#include <chrono>
#include <iterator>
#include <limits>
#include <memory>
#include <string>
#include <vector>

#include "include/Debug.h"

#include "llvm/Support/Debug.h"

#ifdef SPECSFS_NOTIMERS
#define if_timers(X)
#define if_timers_else(X, Y) Y
#else
#define if_timers(X) X
#define if_timers_else(X, Y) X
#endif

namespace std14 {
// General Helpers {{{
template <typename T, typename... va_args>
std::unique_ptr<T> make_unique(va_args&&... args) {
  return std::unique_ptr<T>(new T(std::forward<va_args>(args)...));
}

template <typename T>
typename T::const_iterator cbegin(const T &container) {
  return std::begin(container);
}

template <typename T>
typename T::const_iterator cend(const T &container) {
  return std::end(container);
}
//}}}
}  // namespace std14

namespace util {

// PerfTimers {{{
class PerfTimer {
  //{{{
 public:
    typedef std::chrono::high_resolution_clock Clock;
    typedef Clock::time_point TimePoint;
    typedef std::chrono::duration<double> Duration;
    PerfTimer() = default;

    PerfTimer(const PerfTimer &) = delete;
    PerfTimer &operator=(const PerfTimer &) = delete;

    PerfTimer(PerfTimer &&) = default;
    PerfTimer &operator=(PerfTimer &&) = default;

    void start() {
      if_timers(
        running_ = true;
        lastTime_ = Clock::now());
    }

    void stop() {
      if_timers(
        // Hacky, to avoid optimizations
        assert(running_);
        running_ = false;
        auto cur_time = Clock::now();

        auto elapsed =
          std::chrono::duration_cast<Duration>(cur_time - lastTime_);
        totalTime_ += elapsed;
        numTimes_++);
    }

    void tick() {
      if_timers(
        if (running_) {
          auto prev_time = lastTime_;
          lastTime_ = Clock::now();
          totalTime_ +=
            std::chrono::duration_cast<Duration>(lastTime_ - prev_time);
          numTimes_++;
        } else {
          running_ = true;
          lastTime_ = Clock::now();
        })
    }

    void reset() {
      if_timers(
        running_ = false;
        numTimes_ = 0;
        totalTime_ = Duration::zero());
    }

    Duration totalElapsed() const {
      if_timers_else(
        return totalTime_,
        return Duration::zero());
    }

    Duration averageElapsed() const {
      if_timers_else(
          return totalTime_ / numTimes_,
          return Duration::zero());
    }

    void printDuration(llvm::raw_ostream &o, const std::string &name) const {
      if_timers(
      o << name << ": timer duration: " << totalElapsed().count() <<  "\n");
    }

 private:
    TimePoint lastTime_;
    Duration totalTime_ = Duration::zero();
    int64_t numTimes_ = 0;
    bool running_ = false;
  //}}}
};

class PerfTimerTick {
  //{{{
 public:
    explicit PerfTimerTick(PerfTimer &t) : tmr_(t) {
      tmr_.start();
    }

    ~PerfTimerTick() {
      tmr_.stop();
    }

 private:
    PerfTimer &tmr_;
  //}}}
};

class PerfTimerPrinter {
  //{{{
 public:
    explicit PerfTimerPrinter(llvm::raw_ostream &o, std::string name) :
        o_(o), name_(std::move(name)) {
      if_timers(
      timer_.start();
      o << name_ << ": timer start\n");
    }

    ~PerfTimerPrinter() {
      if_timers(
        timer_.stop();
        timer_.printDuration(o_, name_));
    }

 private:
    llvm::raw_ostream &o_;
    PerfTimer timer_;
    std::string name_;
  //}}}
};
//}}}

/*
// Union-find data structure {{{
template<typename v_type>
class UnionFind {
 public:
  // Typedefs {{{
  typedef v_type value_type;
  typedef v_type & reference;
  typedef const v_type & const_reference;
  typedef v_type * pointer;
  typedef const v_type * const_pointer;
  //}}}
  
  // Constructors {{{
  UnionFind() = default;
  UnionFind(const UnionFind &rhs) {
    data_.reserve(data_.size());
    for (auto &node : data) {
      data_.emplace_back(node);
    }
  }

  UnionFind(UnionFind &&rhs) = default;

  UnionFind &operator=(const UnionFind &rhs) {
    data_.reserve(data_.size());
    for (auto &node : data) {
      data_.emplace_back(node);
    }
  }

  UnionFind &operator=UnionFind(UnionFind &&rhs) = default;
  //}}}

  // Modifiers {{{
  iterator emplace_back
  // }}}

 private:
  class Node {
    //{{{
   public:
    static size_t NODE_REP = std::numeric_limits<size_t>::max;

    Node() = default;
    Node(const value_type &data) : data_(new value_type(data)) { }
    Node(value_type &&data) : data_(new value_type(data)) { }

    template<typename... va_args>
    Node(va_args&&... args) :
      data_(new value_type(std::forward<va_args>(args)...)) { }

    const_reference data() const {
      return data_;
    }

    reference data() {
      return data_;
    }

    bool isRep() const {
      return rep_ == NODE_REP;
    }

    size_t rep() const {
      return rep_;
    }

    void setRep(size_t rep) const {
      rep_ = rep;
    }

   private:
    std::unqiue_ptr<value_type> data_;
    mutable size_t rep_ = NODE_REP;
    //}}}
  };

  std::vector<Node> data_;
};
//}}}
*/

// map Key/Value iteration {{{
// Value Iterators {{{
template<class map_iterator>
class ValueIterator : public std::iterator<std::bidirectional_iterator_tag,
  typename map_iterator::value_type::second_type> {
  //{{{
 public:
  typedef std::iterator<std::bidirectional_iterator_tag,
          typename map_iterator::value_type::second_type>
            iter_base;
  ValueIterator() { }
  explicit ValueIterator(map_iterator itr) : itr_(itr) { }

  ValueIterator &operator++() {
    ++itr_;
    return *this;
  }

  ValueIterator &operator++(int) {
    auto tmp = *this;
    ++itr_;
    return tmp;
  }

  ValueIterator &operator--() {
    --itr_;
    return *this;
  }

  ValueIterator &operator--(int) {
    auto tmp = *this;
    --itr_;
    return tmp;
  }

  bool operator==(const ValueIterator &rhs) const {
    return rhs.itr_ == itr_;
  }

  bool operator!=(const ValueIterator &rhs) const {
    return rhs.itr_ != itr_;
  }

  typename iter_base::reference operator*() {
    return itr_->second;
  }

  typename iter_base::pointer operator->() {
    return &itr_->second;
  }

 private:
  map_iterator itr_;
  //}}}
};

template<class iter_type>
inline ValueIterator<iter_type>
make_value_iterator(iter_type &i) {
  return ValueIterator<iter_type>(i);
}

template<class container>
inline ValueIterator<typename container::iterator>
value_begin(container &c) {
  return make_value_iterator(std::begin(c));
}

template<class container>
inline ValueIterator<typename container::iterator>
value_end(container &c) {
  return make_value_iterator(std::end(c));
}

template<class container>
inline ValueIterator<typename container::const_iterator>
value_begin(const container &c) {
  return make_value_iterator(std::begin(c));
}

template<class container>
inline ValueIterator<typename container::const_iterator>
value_end(const container &c) {
  return make_value_iterator(std::end(c));
}

template<class container>
inline ValueIterator<typename container::const_iterator>
value_cbegin(const container &c) {
  return make_value_iterator(std::begin(c));
}

template<class container>
inline ValueIterator<typename container::const_iterator>
value_cend(const container &c) {
  return make_value_iterator(std::end(c));
}
//}}}

// Key Iterators {{{
template<class map_iterator>
class KeyIterator : public std::iterator<std::bidirectional_iterator_tag,
  typename map_iterator::value_type::second_type> {
  //{{{
 public:
  typedef std::iterator<std::bidirectional_iterator_tag,
          typename map_iterator::value_type::second_type>
            iter_base;
  KeyIterator() { }
  explicit KeyIterator(map_iterator itr) : itr_(itr) { }

  KeyIterator &operator++() {
    ++itr_;
    return *this;
  }

  KeyIterator &operator++(int) {
    auto tmp = *this;
    ++itr_;
    return tmp;
  }

  KeyIterator &operator--() {
    --itr_;
    return *this;
  }

  KeyIterator &operator--(int) {
    auto tmp = *this;
    --itr_;
    return tmp;
  }

  bool operator==(const KeyIterator &rhs) const {
    return rhs.itr_ == itr_;
  }

  bool operator!=(const KeyIterator &rhs) const {
    return rhs.itr_ != itr_;
  }

  typename iter_base::reference operator*() {
    return itr_->first;
  }

  typename iter_base::pointer operator->() {
    return &itr_->first;
  }

 private:
  map_iterator itr_;
  //}}}
};

template<class iter_type>
inline KeyIterator<iter_type>
make_key_iterator(iter_type &i) {
  return KeyIterator<iter_type>(i);
}

template<class container>
inline KeyIterator<typename container::iterator>
key_begin(container &c) {
  return make_key_iterator(std::begin(c));
}

template<class container>
inline KeyIterator<typename container::iterator>
key_end(container &c) {
  return make_key_iterator(std::end(c));
}

template<class container>
inline KeyIterator<typename container::const_iterator>
key_begin(const container &c) {
  return make_key_iterator(std::begin(c));
}

template<class container>
inline KeyIterator<typename container::const_iterator>
key_end(const container &c) {
  return make_key_iterator(std::end(c));
}

template<class container>
inline KeyIterator<typename container::const_iterator>
key_cbegin(const container &c) {
  return make_key_iterator(std::begin(c));
}

template<class container>
inline KeyIterator<typename container::const_iterator>
key_cend(const container &c) {
  return make_key_iterator(std::end(c));
}
//}}}
//}}}

// Unique IDs {{{
template<class T = uint64_t, T initial_value = T(0),
  T invalid_value = std::numeric_limits<T>::max()>
class UniqueIdentifier {
  //{{{
 public:
    UniqueIdentifier() = default;
    explicit UniqueIdentifier(const T &init) : val_(init) { }

    static T invalid() {
      return invalid_value;
    }

    static bool isInvalid(const T &val) {
      return val == invalid();
    }

    void check(const T &val) {
      assert(val < val_);
    }

    T next() {
      return val_++;
    }

 private:
    T val_ = initial_value;
  //}}}
};

// NOTE: We use max as our bad value because min() may be 0 which is a common
//   default value
template<class Tag, class impl = int64_t,
  impl invalid_value = std::numeric_limits<impl>::max()>
class ID {
  //{{{
 public:
    typedef impl base_type;
    static constexpr impl invalidValue = invalid_value;
    static ID invalid() { return ID(); }

    struct hasher {
      std::size_t operator()(const ID &id) const {
        return std::hash<impl>()(id.val());
      }
    };

    // Defaults to ID::invalid()
    ID() = default;

    // Explicit constructor:
    constexpr explicit ID(impl val) : val_(val) { }

    // Allow copy
    ID(const ID &) = default;

    // Assignment operator
    ID &operator=(const ID &) = default;

    // Explicit conversion to get back the impl:
    explicit operator impl() const { return val_; }

    constexpr impl val() const { return val_; }

    bool operator<(const ID &id) const {
      return val_ < id.val_;
    }

    bool operator>(const ID &id) const {
      return val_ > id.val_;
    }

    bool operator>=(const ID &id) const {
      return val_ >= id.val_;
    }

    bool operator<=(const ID &id) const {
      return val_ <= id.val_;
    }

    bool valid() const {
      return *this != invalid();
    }

    ID operator++(int) {
      ID ret(val_++);

      return ret;
    }

    ID operator++() {
      ++val_;

      return *this;
    }

    friend bool operator==(ID a, ID b) { return a.val_ == b.val_; }
    friend bool operator!=(ID a, ID b) { return a.val_ != b.val_; }

#ifndef SPECSFS_IS_TEST
    template <typename T, class T2, T2 DV>
    friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
         ID<T, T2, DV> id);
#endif

    template <typename T, class T2, T2 DV>
    friend std::ostream &operator<<(std::ostream &o,
        ID<T, T2, DV> id);

 private:
    impl val_ = invalid_value;
  //}}}
};

// Quick wrapper for generating unique IDs
template<typename id_type, typename id_type::base_type initial_value = 0>
class IDGenerator {
  //{{{
 public:
    IDGenerator() = default;
    explicit IDGenerator(const id_type &init) : val_(init) { }

    static id_type invalid() {
      return id_type::invalid();
    }

    static bool isInvalid(const id_type &val) {
      return val == invalid();
    }

    void check(const id_type &val) {
      assert(val < val_);
    }

    id_type next() {
      auto ret = id_type(val_);
      val_++;
      return ret;
    }

 private:
    typename id_type::base_type val_ = initial_value;
  //}}}
};

#ifndef SPECSFS_IS_TEST
template <typename T, class T2, T2 DV>
llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
    ID<T, T2, DV> id) {
  o << id.val_;
  return o;
}
#endif

template <typename T, class T2, T2 DV>
std::ostream &operator<<(std::ostream &o,
    ID<T, T2, DV> id) {
  o << id.val_;
  return o;
}
//}}}
}  // namespace util

#endif  // INCLUDE_UTIL_H_
