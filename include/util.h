/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_UTIL_H_
#define INCLUDE_UTIL_H_

#include <atomic>
#include <chrono>
#include <limits>
#include <string>

#include "llvm/Support/raw_ostream.h"

#ifdef SPECSFS_NOTIMERS
#define if_timers(X)
#define if_timers_else(X, Y) Y
#else
#define if_timers(X) X
#define if_timers_else(X, Y) X
#endif

// Performance junks
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

 private:
    TimePoint lastTime_;
    Duration totalTime_ = Duration::zero();
    int64_t numTimes_ = 0;
    bool running_ = false;
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
        o_ << name_ << ": timer duration: " << timer_.totalElapsed().count()
            <<  "\n");
    }

 private:
    llvm::raw_ostream &o_;
    PerfTimer timer_;
    std::string name_;
  //}}}
};

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
         ID<T, T2, DV> id);

    template <typename T, class T2, T2 DV>
    friend std::ostream &operator<<(std::ostream &o,
        ID<T, T2, DV> id);

 private:
    impl m_val = invalid_value;
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

template <typename T, class T2, T2 DV>
llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
    ID<T, T2, DV> id) {
  o << id.m_val;
  return o;
}

template <typename T, class T2, T2 DV>
std::ostream &operator<<(std::ostream &o,
    ID<T, T2, DV> id) {
  o << id.m_val;
  return o;
}

#endif  // INCLUDE_UTIL_H_
