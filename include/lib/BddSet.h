/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LIB_BDDSET_H_
#define INCLUDE_LIB_BDDSET_H_

#include <bdd.h>
#include <bvec.h>
#include <fdd.h>

#include <cassert>

#include <algorithm>
#include <limits>
#include <map>
#include <memory>
#include <utility>
#include <vector>

class default_bdd_tag { };

// in lib/BddSet.cpp
extern int32_t g_num_doms;
void bdd_init_once(int num_doms);

// Okay, what do I need to know to setup the bdd domain
template <typename id_type, typename tag = default_bdd_tag>
class BddSet {
  //{{{
 public:
  typedef id_type value_type;

  // Constructors {{{
  BddSet() {
    assert(bddInitd());
  }

  BddSet(const BddSet &) = default;
  BddSet(BddSet &&) = default;

  BddSet &operator=(const BddSet &) = default;
  BddSet &operator=(BddSet &&) = default;
  //}}}

  // Static methods {{{
  static BddSet tautology() {
    BddSet ret;
    ret.ptsto_ = bddtrue;
    return ret;
  }
  //}}}

  // Misc {{{
  int id() const {
    return ptsto_.id();
  }

  bool isTautology() const {
    return ptsto_ == bddtrue;
  }
  //}}}

  // Set, reset, insert, assign, clear, test {{{
  bool set(value_type id) {
    assert(static_cast<int32_t>(id) < domainSize_);
    auto init = ptsto_;
    ptsto_ |= getFddVar(id);
    return (init != ptsto_);
  }

  template<typename InputIterator>
  void insert(InputIterator it, InputIterator en) {
    std::for_each(it, en,
        [this] (value_type id) {
      set(id);
    });
  }

  void reset(value_type id) {
    assert(static_cast<int32_t>(id) < domainSize_);
    ptsto_ &= !getFddVar(id);
  }

  bool assign(const BddSet &rhs) {
    bdd init = ptsto_;
    ptsto_ = rhs.ptsto_;

    return (init != ptsto_);
  }

  void clear() {
    ptsto_ = bddfalse;
  }

  bool test(value_type obj_id) const {
    bdd ret = ptsto_ & getFddVar(obj_id);
    return ret != bddfalse;
  }
  //}}}

  // Equality/inequality {{{
  bool operator==(const BddSet &rhs) const {
    return ptsto_ == rhs.ptsto_;
  }

  bool operator!=(const BddSet &rhs) const {
    return ptsto_ != rhs.ptsto_;
  }
  //}}}

  // Logical operations {{{
  bool operator&=(const BddSet &rhs) {
    auto init = ptsto_;
    ptsto_ &= rhs.ptsto_;

    return (init != ptsto_);
  }

  BddSet operator&(const BddSet &rhs) const {
    BddSet ret(*this);

    ret &= rhs;

    return ret;
  }

  BddSet operator-(const BddSet &rhs) const {
    BddSet ret(*this);

    ret.ptsto_ -= rhs.ptsto_;

    return ret;
  }

  bool operator|=(const BddSet &rhs) {
    auto init = ptsto_;

    ptsto_ |= rhs.ptsto_;

    return init != ptsto_;
  }

  bool intersectWith(const bdd &bmp) {
    auto init = ptsto_;
    ptsto_ &= bmp;
    return (ptsto_ != init);
  }
  //}}}

  // Intersects ignoring {{{
  bool intersectsIgnoring(BddSet &rhs, value_type ignore) {
    auto rhs_tmp = rhs.ptsto_;
    auto lhs_tmp = ptsto_;

    rhs_tmp &= getFddVar(ignore);
    lhs_tmp &= getFddVar(ignore);

    auto ret = ptsto_ & rhs.ptsto_;

    return ret != bddfalse;
  }
  //}}}

  // Size checks (count, singleton, empty) {{{
  size_t count() const {
    updateBddVec();
    return bddVec_->size();
  }

  size_t singleton() const {
    updateBddVec();
    return bddVec_->size() == 1;
  }

  bool empty() const {
    return ptsto_ == bddfalse;
  }
  //}}}

  // Iteration {{{
  class const_iterator {
    //{{{
   private:
    typedef typename std::vector<value_type>::iterator vec_it;

   public:
    typedef std::forward_iterator_tag iterator_category;
    // typedef value_type value_type;
    typedef int32_t difference_type;
    typedef id_type * pointer;
    typedef id_type & reference;

    // Constructor {{{
    explicit const_iterator(vec_it itr) :
      itr_(itr) { }
    //}}}

    // Operators {{{
    bool operator==(const const_iterator &it) const {
      return (itr_ == it.itr_);
    }

    bool operator!=(const const_iterator &it) const {
      return !operator==(it);
    }

    const reference operator*() const {
      return itr_.operator*();
    }

    pointer operator->() const {
      return itr_.operator->();
    }

    const_iterator &operator++() {
      ++itr_;
      return *this;
    }

    const_iterator operator++(int) {
      const_iterator tmp(*this);
      ++itr_;

      return tmp;
    }
    //}}}

   private:
    // Private data {{{
    vec_it itr_;
    //}}}
    //}}}
  };

  const_iterator begin() const {
    updateBddVec();
    return const_iterator(std::begin(*bddVec_));
  }

  const_iterator end() const {
    updateBddVec();
    return const_iterator(std::end(*bddVec_));
  }

  const_iterator cbegin() const {
    updateBddVec();
    return const_iterator(std::begin(*bddVec_));
  }

  const_iterator cend() const {
    updateBddVec();
    return const_iterator(std::end(*bddVec_));
  }
  //}}}

  static void Setup(int32_t domain_size);

 protected:
  void updateBddVec() const {
    if (ptsto_ != iterBdd_ || iterBdd_ == bddfalse) {
      bddVec_ = getBddVec(ptsto_);
      iterBdd_ = ptsto_;
    }
  }

  // Bdd Static Functions {{{
  static bool bddInitd() {
    return bddInitd_;
  }

  // Get Fdds {{{
  static bdd getFddVar(value_type elm) {
    return _getFddVar(static_cast<int32_t>(elm));
  }

  // Cache fdd vars...
  static bdd _getFddVar(int32_t elm) {
    if (fddCache_.size() <= static_cast<size_t>(elm)) {
      fddCache_.resize(elm+1, bddfalse);
    }

    if (fddCache_[elm] == bddfalse) {
      fddCache_[elm] = fdd_ithvar(bddDom_, elm);
    }

    return fddCache_[elm];
  }
  //}}}

  // Vector cache {{{
  // Cache on top of bdd to vector code
  static std::shared_ptr<std::vector<value_type>> getBddVec(bdd pts) {
    if (pts == bddfalse) {
      static std::shared_ptr<std::vector<value_type>> bddfalse_vec
        = std::make_shared<std::vector<value_type>>();
      return bddfalse_vec;
    }

    auto id = pts.id();
    auto it = vecCache_.find(id);
    if (it != std::end(vecCache_)) {
      it->second.first = true;
      return it->second.second;
    }

    // Fill the vector...
    // First check for overflow
    while (vecCache_.size() >= MaxVecCacheSize) {
      auto remove = std::end(vecCache_);
      for (auto it = std::begin(vecCache_), en = std::end(vecCache_);
          it != en; ++it) {
        if (!it->second.first) {
          remove = it;
          break;
        }

        it->second.first = false;
      }

      if (remove != std::end(vecCache_)) {
        vecCache_.erase(remove);
      }
    }

    // Now fill the vector...
    assert(uglyBddVec_.size() == 0);

    bdd_allsat(pts, bddToVector);

    assert(vecCache_.size() < MaxVecCacheSize);
    auto rc = vecCache_.emplace(id,
        std::make_pair(true,
          std::make_shared<std::vector<value_type>>(
            std::move(uglyBddVec_))));
    assert(rc.second);
    std::sort(std::begin(*rc.first->second.second),
        std::end(*rc.first->second.second));

    auto upper_bound = std::lower_bound(std::begin(*rc.first->second.second),
        std::end(*rc.first->second.second), value_type(domainSize_));
    rc.first->second.second->erase(upper_bound,
        std::end(*rc.first->second.second));

    // Remove anything above upper_bound

    // Return our newly allocated vector
    return rc.first->second.second;
  }

  static void bddToVector(char *varset, int) {
    /*
    std::cerr << "bddToVector:" << std::endl;

    std::cerr << "  elm:";
    for (int i = 0; i < size; ++i) {
      int elm = varset[i];
      // std::cerr << (elm < 0) ? 'X' : ('0' + elm);
      if (elm == -1) {
        std::cerr << 'X';
      } else {
        std::cerr << elm;
      }
    }
    std::cerr << std::endl;

    std::cerr << "  g_num_doms: " << g_num_doms << std::endl;
    std::cerr << "  bddDom_: " << bddDom_ << std::endl;
    */
    static int32_t fdd_bits = 0;
    static int32_t fdd_start = 0;
    if (fdd_bits == 0) {
      for (int32_t i = 0; i < bddDom_; i++) {
        fdd_start += fdd_varnum(i);
      }

      fdd_bits = fdd_varnum(bddDom_);
    }
    /*
    std::cerr << "  fdd_bits: " << fdd_bits << std::endl;
    std::cerr << "  fdd_start: " << fdd_start << std::endl;
    */

    uint32_t dont_care[32];
    uint32_t num_dont_care = 0;
    uint32_t base = 0;

    // Only consider bits in my dom --
    // Create don't care mask set for the bits in my domain
    for (uint32_t i = fdd_start, m = 1;
        i < static_cast<uint32_t>(fdd_start + fdd_bits);
        i += 1, m<<=1) {
      switch (varset[i]) {
        case -1:
          dont_care[num_dont_care] = m;
          num_dont_care++;
          break;
        case 1:
          base |= m;
          break;
        default:
          {
            // do nothing for 0's (not in set)
          }
      }
    }

    // Speed up handling of small don't care cases...
    // Now, take the base value, and add on the appropriate don't care bits
    switch (num_dont_care) {
      case 2:
        {
          uint32_t x = base | dont_care[1];
          // std::cerr << "vec add: " << x << "\n";
          uglyBddVec_.emplace_back(x);
          // std::cerr << "vec add: " << (x | dont_care[0]) << std::endl;
          uglyBddVec_.emplace_back(x | dont_care[0]);
        }
        // std::cerr << "vec add: " << (base | dont_care[0]) << std::endl;
        uglyBddVec_.emplace_back(base | dont_care[0]);
        uglyBddVec_.emplace_back(base);
        break;
      case 1:
        // std::cerr << "vec add: " << (base | dont_care[0]) << std::endl;
        uglyBddVec_.emplace_back(base | dont_care[0]);
        uglyBddVec_.emplace_back(base);
        break;
      case 0:
        // std::cerr << "vec add: " << base << std::endl;
        uglyBddVec_.emplace_back(base);
        break;
      default:
        assert(num_dont_care <= 25 && "More don't cares than expected");
        for (uint32_t i = 0, ie = 1 << num_dont_care; i < ie; ++i) {
          uint32_t x = base;
          for (uint32_t j = 0, m = 1; j < num_dont_care; ++j, m <<= 1) {
            if (i & m) {
              x |= dont_care[j];
            }
          }
          // std::cerr << "vec add: " << x << std::endl;
          uglyBddVec_.emplace_back(x);
        }
    }
  }
  //}}}

  // Bdd Static Vars {{{
  static bool bddInitd_;

  // GEPS
  static int32_t domainSize_;
  static int32_t bddDom_;

  static std::vector<bdd> fddCache_;
  static std::vector<id_type> uglyBddVec_;

  // Cache:  id -> pair<clock, ptsto>
  static const size_t MaxVecCacheSize = 50000;
  static std::map<uint32_t, std::pair<bool,
    std::shared_ptr<std::vector<id_type>>>> vecCache_;
  //}}}
  //}}}

  bdd ptsto_;

  mutable bdd iterBdd_ = bddfalse;
  mutable std::shared_ptr<std::vector<id_type>> bddVec_ = nullptr;
  //}}}
};

// Static Vars {{{
template <typename id_type, typename tag>
bool BddSet<id_type, tag>::bddInitd_ = false;

// Domain
template <typename id_type, typename tag>
int32_t BddSet<id_type, tag>::domainSize_ = -1;

template <typename id_type, typename tag>
int32_t BddSet<id_type, tag>::bddDom_ = -1;

template <typename id_type, typename tag>
std::vector<bdd> BddSet<id_type, tag>::fddCache_;

template <typename id_type, typename tag>
std::vector<id_type> BddSet<id_type, tag>::uglyBddVec_;

// Cache:  id -> pair<clock, ptsto>
template <typename id_type, typename tag>
std::map<uint32_t, std::pair<bool,
  std::shared_ptr<std::vector<id_type>>>>
    BddSet<id_type, tag>::vecCache_;
//}}}

// Static setup function {{{
template <typename id_type, typename tag>
void BddSet<id_type, tag>::Setup(int32_t domain_size) {
  assert(bddDom_ == -1);
  // add one dom
  bdd_init_once(1);
  bddInitd_ = true;
  domainSize_ = domain_size;
  // Do extdomain...
  int32_t dom[] = { domain_size };
  bddDom_ = fdd_extdomain(dom, 1);
}
//}}}

#endif  // INCLUDE_LIB_BDDSET_H_
