/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_UTIL_H_
#define INCLUDE_UTIL_H_

#include <cassert>

#include <atomic>
#include <bitset>
#include <chrono>
#include <iterator>
#include <limits>
#include <list>
#include <memory>
#include <set>
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
// General helpers {{{
constexpr bool is_power_of_two(size_t x) {
  return x && ((x & (x-1)) == 0);
}

constexpr bool is_divisible_by(size_t x, size_t y) {
  return (x % y) == 0;
}

template<typename T>
constexpr T div_round_up(T x, T y) {
  return (x + (y-1)) / y;
}
//}}}

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

    // To work with container types
    explicit operator size_t() const { return val_; }

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

template<typename id_type>
class ObjectRemap {
 public:
  ObjectRemap() = delete;
  explicit ObjectRemap(size_t size) : remap_(size) { }

  const id_type &operator[](id_type id) const {
    return remap_[static_cast<size_t>(id)];
  }

  id_type &operator[](id_type id) {
    return remap_[static_cast<size_t>(id)];
  }

  void set(id_type old_id, id_type new_id) {
    remap_[static_cast<size_t>(old_id)] = new_id;
  }

  size_t size() const {
    return remap_.size();
  }

 private:
  std::vector<id_type> remap_;
};
//}}}


// Union Find {{{
// id_type must be construtable from a size_t, have the
//    bool operator<(size_t) const;
// and be castable to a size_t (aka):
//    explicit size_t() const;
// Implements union-find structure, with union-by-rank and path-compression
template<typename id_type = int32_t>
class UnionFind {
 public:
  UnionFind() = default;
  explicit UnionFind(size_t default_size) :
        ranks_(default_size, 0), ids_(default_size) {
    std::iota(std::begin(ids_), std::end(ids_), id_type(0));
  }

  id_type add() {
    ids_.emplace_back(ids_.size());
    ranks_.emplace_back(0);
    return id_type(ids_.size() - 1);
  }

  id_type find(id_type idx) {
    assert(static_cast<size_t>(idx) < ids_.size());
    // If this is not a rep
    if (ids_[static_cast<size_t>(idx)] != idx) {
      ids_[static_cast<size_t>(idx)] =
        find(ids_[static_cast<size_t>(idx)]);
    }

    return ids_[static_cast<size_t>(idx)];
  }

  void merge(id_type rhs, id_type lhs) {
    id_type rhs_root = find(rhs);
    id_type lhs_root = find(lhs);
    auto &rhs_rank = ranks_[static_cast<size_t>(rhs_root)];
    auto &lhs_rank = ranks_[static_cast<size_t>(lhs_root)];

    if (rhs_rank < lhs_rank) {
      ids_[static_cast<size_t>(rhs_root)] = lhs_root;
    } else if (lhs_rank < rhs_rank) {
      ids_[static_cast<size_t>(lhs_root)] = rhs_root;
    } else {
      ids_[static_cast<size_t>(lhs_root)] = rhs_root;
      rhs_rank++;
    }
  }

  size_t size() const {
    assert(ids_.size() == ranks_.size());
    return ids_.size();
  }

  void remap(const ObjectRemap<id_type> &remap) {
    assert(ranks_.size() == ids_.size());
    assert(remap.size() == ids_.size());

    std::vector<int32_t> new_ranks(ranks_.size());
    std::vector<id_type> new_ids(ranks_.size());

    for (size_t i = 0; i < ids_.size(); ++i) {
      new_ids[static_cast<size_t>(remap[id_type(i)])] = remap[ids_[i]];
      new_ranks[static_cast<size_t>(remap[id_type(i)])] = ranks_[i];
    }
    ranks_ = std::move(new_ranks);
    ids_ = std::move(new_ids);
  }

 private:
  std::vector<int32_t> ranks_;
  std::vector<id_type> ids_;
};

// Excludes the union by rank optimization, for when ordering matters
template<typename id_type = int32_t>
class UnionFindNoRank {
 public:
  UnionFindNoRank() = default;
  explicit UnionFindNoRank(size_t default_size) :
        ids_(default_size) {
    std::iota(std::begin(ids_), std::end(ids_), id_type(0));
  }

  id_type add() {
    ids_.emplace_back(ids_.size());
    return id_type(ids_.size() - 1);
  }

  id_type __debugFind(id_type idx,
      std::set<id_type> &cycle_detect,
      std::vector<id_type> &cycle_order) {
    assert(static_cast<size_t>(idx) < ids_.size());
    assert(ids_[static_cast<size_t>(idx)] <= idx);

    auto cycle_it = cycle_detect.find(idx);
    if (cycle_it != std::end(cycle_detect)) {
      // Print cycle and crash
      std::cerr << "Union Find cycle:" << std::endl;
      for (auto prev_idx : cycle_order) {
        std::cerr << "  " << prev_idx << std::endl;
      }
      std::cerr << "  -> " << idx << std::endl;
      abort();
    } else {
      cycle_detect.emplace(idx);
      cycle_order.emplace_back(idx);
    }

    // If this is not a rep
    if (ids_[static_cast<size_t>(idx)] != idx) {
      ids_[static_cast<size_t>(idx)] =
        find(ids_[static_cast<size_t>(idx)]);
    }

    return ids_[static_cast<size_t>(idx)];
  }

  id_type debugFind(id_type idx) {
    std::vector<id_type> a;
    std::set<id_type> b;
    return __debugFind(idx, b, a);
  }

  id_type find(id_type idx) {
    assert(static_cast<size_t>(idx) < ids_.size());
    // If this is not a rep
    if (ids_[static_cast<size_t>(idx)] != idx) {
      ids_[static_cast<size_t>(idx)] =
        find(ids_[static_cast<size_t>(idx)]);
    }

    return ids_[static_cast<size_t>(idx)];
  }

  void merge(id_type lhs, id_type rhs) {
    id_type rhs_root = find(rhs);
    id_type lhs_root = find(lhs);

    ids_[static_cast<size_t>(rhs_root)] = lhs_root;
  }

  size_t size() const {
    return ids_.size();
  }

 private:
  std::vector<id_type> ids_;
};
//}}}

// Stack Alloc {{{
template <typename T>
class StackAlloc : public std::allocator<T> {
 public:
  typedef size_t size_type;
  typedef T* pointer;
  typedef const T* const_pointer;

  static const size_t StackSize = 10000;

  template <typename nT>
  struct rebind {
    typedef StackAlloc<nT> other;
  };

  pointer allocate(size_type n, const void *hint = 0) {
    pointer ret = nullptr;
    if (pos_ == 0) {
      ret = std::allocator<T>::allocate(n, hint);
    } else {
      pos_--;
      ret = st_[pos_];
    }
    return ret;
  }

  void deallocate(pointer p, size_type n) {
    if (pos_ < StackSize && n == 1) {
      st_[pos_] = p;
      pos_++;
    } else {
      std::allocator<T>::deallocate(p, n);
    }
  }

  StackAlloc() : std::allocator<T>() { }  // NOLINT

  template <typename nT>
  StackAlloc(const StackAlloc<nT> &nt) : std::allocator<T>(nt) { }

 private:
  static size_t pos_;
  static std::vector<pointer> st_;
};

template <typename T>
std::vector<T *> StackAlloc<T>::st_(StackAlloc<T>::StackSize, nullptr);

template <typename T>
size_t StackAlloc<T>::pos_(0);
//}}}

// Sparse BitMap {{{
template <size_t bits_per_field>
class BitmapNode {
 public:
  // Note: we use c-type here as gcc makes it a word size
  static const int32_t BitsPerSet = 8*sizeof(unsigned long); //  NOLINT

  static_assert(is_divisible_by(bits_per_field, BitsPerSet),
      "bits_per_field must be divsible by BitsPerSet");

  static const size_t NumBitsets = bits_per_field / BitsPerSet;

  typedef typename std::array<std::bitset<BitsPerSet>, NumBitsets> bmap;

  explicit BitmapNode(size_t idx) : index_(idx) { }

  bool operator==(const BitmapNode &rhs) const {
    return index() == rhs.index() && bitmap_ == rhs.bitmap_;
  }

  bool operator!=(const BitmapNode &rhs) const {
    return !(*this == rhs);
  }

  bool operator|=(const BitmapNode &rhs) {
    assert(index() == rhs.index());

    bool ch = false;
    auto rhs_it = std::begin(rhs.bitmap_);

    for (auto &bs : bitmap_) {
      auto c1 = bs.to_ulong();

      bs |= *rhs_it;

      ch |= (c1 != bs.to_ulong());
      ++rhs_it;
    }

    return ch;
  }

  bool operator&=(const BitmapNode &rhs) {
    if (rhs.index() != index()) {
      return false;
    }

    bool ch = false;
    auto rhs_it = std::begin(rhs.bitmap_);
    for (auto &bs : bitmap_) {
      auto c1 = bs.count();

      bs &= *rhs_it;

      ch |= (c1 != bs.count());
      ++rhs_it;
    }

    return ch;
  }

  bool orWithIntersect(const BitmapNode &rhs,
      const BitmapNode &is) {
    assert(index() == rhs.index());
    assert(index() == is.index());

    bool ch = false;
    auto rhs_it = std::begin(rhs.bitmap_);
    auto is_it = std::begin(is.bitmap_);

    for (auto &bs : bitmap_) {
      auto c1 = bs.to_ulong();

      bs |= (*rhs_it & *is_it);

      // FIXME: Should be enabled in llvm code, but testcase doesn't enforce
      // this
      // assert((bs & std::bitset<BitsPerSet>(*is_it).flip()).none());

      ch |= (c1 != bs.to_ulong());
      ++rhs_it;
      ++is_it;
    }

    return ch;
  }

  static BitmapNode Intersect(const BitmapNode &rhs,
      const BitmapNode &intersect) {
    BitmapNode ret(rhs);

    rhs &= intersect;

    return rhs;
  }

  bool intersects(const BitmapNode &rhs) const {
    if (index() != rhs.index()) {
      return false;
    }

    auto rhs_it = std::begin(rhs.bitmap_);
    for (auto &elm : bitmap_) {
      if (!(elm & *rhs_it).none()) {
        return true;
      }
      ++rhs_it;
    }

    return false;
  }

  bool test(size_t idx) const {
    size_t bitset = idx / BitsPerSet;
    size_t offs = idx % BitsPerSet;
    return bitmap_[bitset].test(offs);
  }

  void set(size_t idx) {
    size_t bitset = idx / BitsPerSet;
    size_t offs = idx % BitsPerSet;
    bitmap_[bitset].set(offs);
  }

  void reset(size_t idx) {
    size_t bitset = idx / BitsPerSet;
    size_t offs = idx % BitsPerSet;
    bitmap_[bitset].reset(offs);
  }

  size_t count() const {
    size_t ret = 0;
    for (auto &bset : bitmap_) {
      ret += bset.count();
    }
    return ret;
  }

  bool none() const {
    for (auto &bs : bitmap_) {
      if (!bs.none()) {
        return false;
      }
    }

    return true;
  }

  size_t index() const {
    return index_;
  }

  unsigned long getUl(size_t idx) const { //  NOLINT
    return bitmap_[idx].to_ulong();
  }

  size_t hash() const {
    static_assert(sizeof(size_t) == sizeof(unsigned long),  // NOLINT
        "hash assumes sizeof size_t == sizeof ulong");
    size_t ret = 0;
    for (auto &elm : bitmap_) {
      // ret ^= elm.to_ulong();
      ret ^= std::hash<std::bitset<BitsPerSet>>()(elm);
    }
    return ret;
  }

 private:
  bmap bitmap_;
  size_t index_;
};

template <typename id_type = int32_t, size_t bits_per_field = 128,
         typename alloc = StackAlloc<BitmapNode<bits_per_field>>>
class SparseBitmap {
 public:
  typedef BitmapNode<bits_per_field> node;
  typedef typename std::list<node, alloc> bitmap_list;

  // Constructors {{{
  explicit SparseBitmap(const alloc &a = alloc()) : alloc_(a), elms_(alloc_),
      curElm_(std::end(elms_)) { }

  SparseBitmap(const SparseBitmap &s) : alloc_(s.alloc_),
      elms_(std::begin(s.elms_), std::end(s.elms_)),
  /*
      curElm_(std::next(std::begin(elms_),
            std::distance(std::begin(s.elms_), s.curElm_))) { }
            */
      curElm_(std::begin(elms_)) { }
  SparseBitmap(SparseBitmap &&s) = default;

  SparseBitmap &operator=(const SparseBitmap &s) {
    alloc_ = s.alloc_;

    elms_.clear();
    elms_.insert(std::end(elms_), std::begin(s.elms_), std::end(s.elms_));

    curElm_ = std::begin(elms_);
    /*
    curElm_ = std::next(std::begin(elms_),
      std::distance(std::begin(s.elms_), s.curElm_));
      */

    return *this;
  }

  SparseBitmap &operator=(SparseBitmap &&) = default;
  //}}}

  // Misc {{{
  bool empty() const {
    return elms_.empty();
  }

  void clear() {
    elms_.clear();
  }
  //}}}

  // Accessors {{{
  bool test(id_type id) const {
    auto idx = getIdx(id);
    auto it = findClosest(idx);

    if (it == std::end(elms_)) {
      return false;
    }

    if (it->index() != idx) {
      return false;
    }

    return it->test(getOffs(id));
  }

  bool intersects(SparseBitmap &rhs) const {
    if (elms_.empty() && rhs.elms_.empty()) {
      return false;
    }

    auto it1 = std::begin(elms_);
    auto it2 = std::begin(rhs.elms_);

    while (it2 != std::end(rhs.elms_)) {
      if (it1 == std::end(elms_)) {
        return false;
      }

      if (it1->index() > it2->index()) {
        ++it2;
      } else if (it2->index() > it1->index()) {
        ++it1;
      // index1 == index2
      } else {
        if (it1->intersects(*it2)) {
          return true;
        }
        ++it1;
        ++it2;
      }
    }
    return false;
  }

  bool singleton() const {
    return elms_.size() == 1 &&
      elms_.front().count() == 1;
  }

  size_t count() const {
    size_t ret = 0;
    for (auto &elm : elms_) {
      ret += elm.count();
    }
    return ret;
  }
  // }}}

  // Modifiers {{{
  void reset(id_type id) {
    auto idx = getIdx(id);

    auto it = findClosest(idx);

    if (it == std::end(elms_) ||
        it->index() != idx) {
      return;
    }

    it->reset(getOffs(id));

    // If no bits are set, erase the bitset
    if (it->none()) {
      // Advance curElm because we're about to erase this one
      ++curElm_;
      elms_.erase(it);
    }
  }

  void set(id_type id) {
    auto idx = getIdx(id);
    auto it = findClosest(idx);

    // Need to insert at rear?
    if (it == std::end(elms_)) {
      it = elms_.insert(it, node(idx));
    } else if (it->index() != idx) {
      if (it->index() < idx) {
        it = elms_.insert(++it, node(idx));
      } else {
        it = elms_.insert(it, node(idx));
      }
    }

    assert(it->index() == idx);
    curElm_ = it;

    it->set(getOffs(id));
  }

  bool test_and_set(id_type id) {
    auto idx = getIdx(id);
    auto it = findClosest(idx);
    // std::cout << "id: " << id << ", idx: " << idx << std::endl;

    // Need to insert at rear?
    if (it == std::end(elms_)) {
      it = elms_.insert(it, node(idx));
    } else if (it->index() != idx) {
      // std::cout << "it->idx: " << it->index << std::endl;
      if (it->index() < idx) {
        // std::cout << "InsAfter" << std::endl;
        it = elms_.insert(++it, node(idx));
      } else {
        // std::cout << "InsBefore" << std::endl;
        it = elms_.insert(it, node(idx));
      }
    }

    curElm_ = it;

    auto offs = getOffs(id);
    bool ret = !(it->test(offs));
    it->set(offs);
    return ret;
  }

  bool orWithIntersect(const SparseBitmap &rhs,
      const SparseBitmap *intersect) {
    if (intersect == nullptr) {
      return operator|=(rhs);
    }

    // If they are empty nothing changes...
    if (rhs.empty()) {
      return false;
    }

    bool ch = false;
    auto it1 = std::begin(elms_);
    auto it2 = std::begin(rhs.elms_);
    auto it_int = std::begin(intersect->elms_);

    while (it2 != std::end(rhs.elms_)) {
      while (it_int != std::end(intersect->elms_) &&
          it2->index() > it_int->index()) {
        ++it_int;
      }

      if (it_int == std::end(intersect->elms_)) {
        break;
      }

      // Only proceed to check if the two intersect
      if (it_int->index() > it2->index()) {
        ++it2;
        continue;
      }

      node new_node(*it2);
      new_node &= *it_int;

      // If the intersection of rhs and intersect is empty, move on
      if (new_node.none()) {
        ++it2;
        continue;
      }

      assert(it_int->index() == it2->index());
      assert(new_node.index() == it2->index());

      // std::cout << "it1->idx: " << it1->index() << std::endl;
      // std::cout << "it2->idx: " << it2->index() << std::endl;
      if (it1 == std::end(elms_) || it1->index() > it2->index()) {
        elms_.insert(it1, std::move(new_node));
        ++it2;
        ch = true;
      } else if (it1->index() == it2->index()) {
        ch |= it1->orWithIntersect(*it2, *it_int);
        ++it1;
        ++it2;
      } else {
        ++it1;
      }
    }

    curElm_ = std::begin(elms_);

    return ch;
  }
  //}}}

  // Operators {{{
  bool operator==(const SparseBitmap &rhs) const {
    auto it1 = std::begin(elms_);
    auto it2 = std::begin(rhs.elms_);

    for (; it1 != std::end(elms_) && it1 != std::end(rhs.elms_); ++it1, ++it2) {
      if (*it1 != *it2) {
        return false;
      }
    }

    return it1 == std::end(elms_) && it2 == std::end(rhs.elms_);
  }

  bool operator!=(const SparseBitmap &rhs) const {
    return !(*this == rhs);
  }

  // Ugh, harder
  bool operator|=(const SparseBitmap &rhs) {
    // If they are empty nothing changes...
    if (rhs.empty()) {
      return false;
    }

    bool ch = false;
    auto it1 = std::begin(elms_);
    auto it2 = std::begin(rhs.elms_);

    while (it2 != std::end(rhs.elms_)) {
      // std::cout << "it1->idx: " << it1->index() << std::endl;
      // std::cout << "it2->idx: " << it2->index() << std::endl;
      if (it1 == std::end(elms_) || it1->index() > it2->index()) {
        elms_.insert(it1, *it2);
        ++it2;
        ch = true;
      } else if (it1->index() == it2->index()) {
        // Don't do copy if we've already changed
        ch |= (*it1 |= *it2);
        ++it1;
        ++it2;
      } else {
        ++it1;
      }
    }

    curElm_ = std::begin(elms_);

    return ch;
  }

  bool operator&=(const SparseBitmap &rhs) {
    if (elms_.empty() && rhs.elms_.empty()) {
      return false;
    }

    bool ch = false;
    auto it1 = std::begin(elms_);
    auto it2 = std::begin(rhs.elms_);

    while (it2 != std::end(rhs.elms_)) {
      if (it1 == std::end(elms_)) {
        curElm_ = std::begin(elms_);
        return ch;
      }

      if (it1->index() > it2->index()) {
        ++it2;
      } else if (it1->index() == it2->index()) {
        // Don't do copy if we've already changed
        ch = (*it1 &= *it2);

        if (it1->none()) {
          assert(ch);
          auto tmp = it1;
          ++it1;
          elms_.erase(tmp);
        } else {
          ++it1;
        }
        ++it2;
      } else {
        auto tmp = it1;
        ++it1;
        elms_.erase(tmp);
      }
    }

    ch |= (it1 == std::end(elms_));
    elms_.erase(it1, std::end(elms_));
    curElm_ = std::begin(elms_);
    return ch;
  }
  //}}}

  // Hash {{{
  struct hasher {
    size_t operator()(const SparseBitmap &map) const {
      size_t ret = 0;

      for (auto &elm : map.elms_) {
        ret ^= elm.hash();
      }

      return ret;
    }
  };
  //}}}

  // Iteration {{{
  class iterator :
      public std::iterator<std::forward_iterator_tag, id_type> {
   public:
    // NOTE: We use unsigned long here for size of machine word... works w/ gcc
    int32_t BitsPerShift = 8*sizeof(unsigned long);  // NOLINT

    explicit iterator(const bitmap_list &bl, bool end) :
        bl_(bl), it_(std::begin(bl)), end_(end) {
      getFirstBit();
    }

    explicit iterator(const bitmap_list &bl) : bl_(bl), it_(std::begin(bl)) {
      getFirstBit();
    }

    iterator operator++(int) {
      auto tmp = *this;
      advanceBit();
      return tmp;
    }

    iterator &operator++() {
      advanceBit();
      return *this;
    }

    id_type operator*() const {
      // -1 b/c the bsPos_ is 1 indexed
      auto ret = id_type(bsPos_-1 +
          (bsShift_ * node::BitsPerSet)
          + it_->index() * bits_per_field);

      // std::cout << "Returning: " << ret << std::endl;

      return ret;
    }

    bool operator==(const iterator &it) const {
      return end_ == it.end_ ||
        (it_ == it.it_ &&
        bsPos_ == it.bsPos_ &&
        bsShift_ == it.bsShift_);
    }

    bool operator!=(const iterator &it) const {
      return !(*this == it);
    }

   private:
    void getBsVal() {
      bsVal_ = it_->getUl(bsShift_);
      // std::cout << "getBsVal: " << bsVal_ << std::endl;
    }

    void advanceBs() {
      bsShift_++;
    }

    void nextBsVal() {
      advanceBs();
      getBsVal();
    }

    void nextBsPos() {
      int val = __builtin_ffsl(bsVal_);
      assert(val != 0);
      if (val == 8*sizeof(unsigned long)) {  // NOLINT
        bsVal_ = 0;
      } else {
        bsVal_ >>= val;
      }
      /*
      std::cout << "~new bsVal_: " << std::hex << bsVal_ << std::dec << std::endl;
      */
      bsPos_ += val;
    }

    void getFirstBit() {
      if (end_) {
        return;
      }

      if (bl_.empty()) {
        end_ = true;
        return;
      }

      it_ = std::begin(bl_);
      // std::cout << "init it->idx: " << it_->index() << std::endl;

      // Initialize bsVal_;
      getBsVal();

      // std::cout << "init bsVal_: " << bsVal_ << std::endl;

      // Go until we get a non-0 bs
      while (bsVal_ == 0) {
        nextBsVal();
      }

      /*
      std::cout << "post-inc bsVal_: " << std::hex << bsVal_ << std::dec << std::endl;
      */

      // Okay, now find the first bit
      bsPos_ = 0;
      nextBsPos();
      // std::cout << "init bsPos_: " << bsPos_ << std::endl;
      // std::cout << "init bsVal_: " << bsVal_ << std::endl;
      // std::cout << "init bsShift_: " << bsShift_ << std::endl;
    }

    void advanceBit() {
      if (end_) {
        return;
      }

      // std::cout << "have bsVal_: " << bsVal_ << std::endl;
      while (bsVal_ == 0) {
        bsPos_ = 0;
        // std::cout << "have bsShift_: " << bsShift_ << std::endl;
        if (bsShift_ == (node::NumBitsets-1)) {
          ++it_;
          // std::cout << "IT advance" << std::endl;
          if (it_ == std::end(bl_)) {
            // std::cout << "END" << std::endl;
            end_ = true;
            return;
          }
          bsShift_ = 0;
          getBsVal();
          // std::cout << "BS reset to: " << bsVal_ << std::endl;
        } else {
          nextBsVal();
        }
      }

      // std::cout << "old bsPos_ : " << bsPos_ << std::endl;
      nextBsPos();
      // std::cout << "new bsPos_ : " << bsPos_ << std::endl;
    }

    const bitmap_list &bl_;
    typename bitmap_list::const_iterator it_;

    bool end_ = false;
    uint32_t bsPos_ = 0;
    unsigned long bsVal_;  // NOLINT
    uint32_t bsShift_ = 0;
  };

  typedef iterator const_iterator;

  iterator begin() {
    return iterator(elms_);
  }

  iterator end() {
    return iterator(elms_, true);
  }

  const_iterator begin() const {
    return const_iterator(elms_);
  }

  const_iterator end() const {
    return const_iterator(elms_, true);
  }
  //}}}

  // Print debug {{{
  friend std::ostream &operator<<(std::ostream &os, const SparseBitmap &map) {
    os << "{";
    for (auto val : map) {
      os << " " << val;
    }
    os << " }";
    return os;
  }

  friend llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
      const SparseBitmap &map) {
    os << "{";
    for (auto val : map) {
      os << " " << val;
    }
    os << " }";
    return os;
  }
  //}}}

 private:
  static size_t getIdx(id_type id) {
    return static_cast<size_t>(id) / (bits_per_field);
  }

  static size_t getOffs(id_type id) {
    return static_cast<size_t>(id) % (bits_per_field);
  }

  // Returns the node that contains this id, or the node before it if it isn't
  //   found, or std::end(list) if the element belongs at the front of the list
  typename bitmap_list::iterator findClosest(size_t idx) const {
    if (elms_.empty()) {
      return std::end(elms_);
    }

    if (curElm_ == std::end(elms_)) {
      --curElm_;
    }

    auto elm = curElm_;
    if (elm->index() == idx) {
      return elm;
    } else if (elm->index() > idx) {
      while (elm != std::begin(elms_) &&
          elm->index() > idx) {
        --elm;
      }
    } else {
      while (elm != std::end(elms_) &&
          elm->index() < idx) {
        ++elm;
      }
    }

    curElm_ = elm;
    return elm;
  }

  alloc alloc_;

  mutable bitmap_list elms_;

  // We make lastElm_ mutable as it does not modify the interface to the class,
  // so we can change it in const accessors while they still appear const to the
  // outside world
  mutable typename bitmap_list::iterator curElm_;
};
//}}}
}  // namespace util

#endif  // INCLUDE_UTIL_H_
