/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_SOLVEHELPERS_H_
#define INCLUDE_SOLVEHELPERS_H_

#include <bdd.h>
#include <bvec.h>
#include <fdd.h>

#include <algorithm>
#include <limits>
#include <map>
#include <queue>
#include <set>
#include <utility>
#include <vector>

#include "llvm/ADT/SparseBitVector.h"

#include "include/util.h"
#include "include/Cg.h"

// Bitmap used in many places (and by Andersen's) to represent ptsto
// typedef llvm::SparseBitVector<> Bitmap;
typedef util::SparseBitmap<> Bitmap;

// Required for using a Bitmap as a std::map key (used for ID gathering) {{{
struct BitmapLT {
  bool operator() (const Bitmap &b1, const Bitmap &b2) const {
    auto it1 = std::begin(b1);
    auto it2 = std::begin(b2);
    auto en1 = std::end(b1);
    auto en2 = std::end(b2);

    // True if any element b1 < b2
    for (; it1 != en1 && it2 != en2; ++it1, ++it2) {
      // if it1 < it2 : b1 < b2
      if (*it1 < *it2) {
        return true;
      // If it1 > it2 : b1 > b2
      } else if (*it1 > *it2) {
        return false;
      }
      // Otherwise, they are equal, try the next element
    }

    // If they are equivalent but b1 is longer b1 is less than it b2
    if (it1 != en1) {
      return true;
    }

    return false;
  }
};

/*
typedef Bitmap::hasher BitmapHash;
struct BitmapHash {
  size_t operator() (const Bitmap &b1) const {
    return Bitmap::hasher()(b1);
  }
};
*/

struct BitmapHash {
  size_t operator() (const Bitmap &b1) const {
    /*
    size_t ret = 0;
    for (auto elm : b1) {
      ret ^= std::hash<int32_t>()(elm);
      ret <<= 1;
    }
    return ret;
    */
    return Bitmap::hasher()(b1);
  }
};
//}}}

// Typedef for PartID
struct part_id { };
typedef util::ID<part_id, int32_t> __PartID;

// Lowest priority dual queue work queue -- what sfs uses
template<typename vtype>
class Worklist {
  //{{{
 public:
    typedef vtype value_type;
    typedef vtype * pointer;
    typedef vtype & reference;

    value_type pop(uint32_t &prio) {
      // Try getting our next heap
      if (heap_.empty()) {
        heap_.swap(nextHeap_);
      }

      if (heap_.empty()) {
        return vtype::invalid();
      }

      auto &entry = heap_.front();
      // Must do this before popping the heap...
      auto ret = entry.node();
      prio = entry.prio();

      // Only okay to pop the heap after I'm done with entry...
      std::pop_heap(std::begin(heap_), std::end(heap_));
      heap_.pop_back();

      return ret;
    }

    void push(value_type node, uint32_t prio) {
      nextHeap_.emplace_back(node, prio);
      std::push_heap(std::begin(nextHeap_), std::end(nextHeap_));
    }

    bool empty() const {
      return (heap_.size() == 0 && nextHeap_.size() == 0);
    }

 private:
    class HeapEntry {
      //{{{
     public:
        HeapEntry(reference node, uint32_t prio) :
          node_(node), prio_(prio) { }

        value_type node() const {
          return node_;
        }

        int32_t prio() const {
          return prio_;
        }

        bool operator<(const HeapEntry &rhs) const {
          // We want a min heap, so invert the < operator to >
          if (prio() == rhs.prio()) {
            return node() < rhs.node();
          }

          return prio() > rhs.prio();
        }

     private:
        value_type node_;
        uint32_t prio_;
      //}}}
    };

    std::vector<HeapEntry> heap_;
    std::vector<HeapEntry> nextHeap_;
  //}}}
};

class BddPtstoSet {
  //{{{
 public:
  BddPtstoSet() {
    assert(bddInitd());
  }

  explicit BddPtstoSet(const Bitmap &dyn_pts) :
      dynPtsto_(bitmapToBdd(dyn_pts)) {
    assert(bddInitd());
  }

  BddPtstoSet(const BddPtstoSet &rhs) {
    ptsto_ = rhs.ptsto_;
    if (rhs.dynPtsto_ != nullptr) {
      dynPtsto_ = std::unique_ptr<bdd>(new bdd(*rhs.dynPtsto_));
    } else {
      dynPtsto_ = nullptr;
    }
  }
  BddPtstoSet(BddPtstoSet &&) = default;

  BddPtstoSet &operator=(const BddPtstoSet &rhs) {
    ptsto_ = rhs.ptsto_;
    if (rhs.dynPtsto_ != nullptr) {
      dynPtsto_ = std::unique_ptr<bdd>(new bdd(*rhs.dynPtsto_));
    } else {
      dynPtsto_ = nullptr;
    }
    return *this;
  }
  BddPtstoSet &operator=(BddPtstoSet &&) = default;

  static void PtstoSetInit(const Cg &cg) {
    if (!bddInitd()) {
      bddInit(cg);
    }
  }

  bool set(ValueMap::Id id) {
    auto init = ptsto_;
    ptsto_ |= getFddVar(id);
    return (init != ptsto_);
  }

  template<typename InputIterator>
  void insert(InputIterator it, InputIterator en) {
    std::for_each(it, en,
        [this] (ValueMap::Id id) {
      set(id);
    });
  }

  void reset(ValueMap::Id id) {
    ptsto_ &= !getFddVar(id);
  }

  size_t getSizeNoStruct(ValueMap &map) const {
    std::set<const llvm::Value *> pts_set;

    for (auto obj_id : *this) {
      auto val = map.getValue(obj_id);
      pts_set.insert(val);
    }

    return pts_set.size();
  }

  void setDynSet(const Bitmap &dyn_set) {
    dynPtsto_ = bitmapToBdd(dyn_set);
  }

  bool assign(const BddPtstoSet &rhs) {
    bdd init = ptsto_;
    ptsto_ = rhs.ptsto_;

    clearDynPtsto();

    return (init != ptsto_);
  }

  void clear() {
    ptsto_ = bddfalse;
  }

  bool operator==(const BddPtstoSet &rhs) const {
    return ptsto_ == rhs.ptsto_;
  }

  bool operator!=(const BddPtstoSet &rhs) const {
    return ptsto_ != rhs.ptsto_;
  }

  bool operator&=(const BddPtstoSet &rhs) {
    auto init = ptsto_;
    ptsto_ &= rhs.ptsto_;

    return (init != ptsto_);
  }

  BddPtstoSet operator&(const BddPtstoSet &rhs) const {
    BddPtstoSet ret(*this);

    ret &= rhs;

    return ret;
  }

  BddPtstoSet operator-(const BddPtstoSet &rhs) const {
    BddPtstoSet ret(*this);

    ret.ptsto_ -= rhs.ptsto_;

    return ret;
  }

  bool operator|=(const BddPtstoSet &rhs) {
    auto init = ptsto_;

    ptsto_ |= rhs.ptsto_;

    if (init != ptsto_) {
      clearDynPtsto();
    }

    return init != ptsto_;
  }

  bool operator|=(ValueMap::Id &id) {
    bdd init = ptsto_;
    ptsto_ |= getFddVar(id);
    if (ptsto_ != init) {
      clearDynPtsto();
    }
    return (init != ptsto_);
  }

  bool orOffs(const BddPtstoSet &rhs, int32_t offs) {
    if (offs == 0) {
      return operator|=(rhs);
    }

    bdd init = ptsto_;

    // Do an or offs
    ptsto_ |= bdd_replace(bdd_relprod(rhs.ptsto_, geps_[offs], ptsDom_),
        gepToPts_);

    if (init != ptsto_) {
      clearDynPtsto();
    }

    return (init != ptsto_);
  }

  bool intersectWith(const bdd &bmp) {
    auto init = ptsto_;
    ptsto_ &= bmp;
    return (ptsto_ != init);
  }

  bool test(ValueMap::Id obj_id) {
    bdd ret = ptsto_ & getFddVar(obj_id);
    return ret != bddfalse;
  }

  bool intersectsIgnoring(BddPtstoSet &rhs, ValueMap::Id ignore) {
    auto rhs_tmp = rhs.ptsto_;
    auto lhs_tmp = ptsto_;

    rhs_tmp &= getFddVar(ignore);
    lhs_tmp &= getFddVar(ignore);

    auto ret = ptsto_ & rhs.ptsto_;

    return ret != bddfalse;
  }

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

  class const_iterator {
    //{{{
   public:
    typedef std::forward_iterator_tag iterator_category;
    typedef ValueMap::Id value_type;
    typedef int32_t difference_type;
    typedef ValueMap::Id * pointer;
    typedef ValueMap::Id & reference;

    // Constructor {{{
    explicit const_iterator(std::vector<ValueMap::Id>::iterator itr) :
      itr_(itr) { }
    //}}}

    // Operators {{{
    bool operator==(const const_iterator &it) const {
      return (itr_ == it.itr_);
    }

    bool operator!=(const const_iterator &it) const {
      return !operator==(it);
    }

    const value_type operator*() const {
      return ValueMap::Id(itr_.operator*());
    }

    /*
    value_type operator->() const {
      return ValueMap::Id(itr_.operator->());
    }
    */

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
    std::vector<ValueMap::Id>::iterator itr_;
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

#ifndef SPECSFS_IS_TEST
  friend llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
      const BddPtstoSet &ps) {
    os << "{";
    for (ValueMap::Id id : ps) {
      os << " " << id;
    }
    os << " }";

    return os;
  }
#endif

  static void updateGeps(const Cg &cg);
  static void updateConstraints(const Cg &cg);

 private:
  std::unique_ptr<bdd> bitmapToBdd(const Bitmap &bm) {
    auto ret = std::unique_ptr<bdd>(new bdd(bddfalse));

    for (auto elm : bm) {
      *ret |= getFddVar(elm);
    }

    return ret;
  }

  void clearDynPtsto() {
    if (dynPtsto_ != nullptr) {
      // llvm::dbgs() << "!!!!!CLEAR DYN PTSTO????\n";
      ptsto_ &= *dynPtsto_;
    }
  }

  void updateBddVec() const {
    if (ptsto_ != iterBdd_ || iterBdd_ == bddfalse) {
      iterBdd_ = ptsto_;
      bddVec_ = getBddVec(ptsto_);
    }
  }

  // Bdd Static Functions {{{
  // Setup geps! (ugh)
  // For geps needs omap (for object size into)
  //   and cg -- for (for used constraint offsets)
  static void bddInit(const Cg &cg);

  static bool bddInitd() {
    return bddInitd_;
  }

  // Get Fdds {{{
  static bdd getFddVar(ValueMap::Id elm) {
    return getFddVar(elm.val());
  }

  // Cache fdd vars...
  static bdd getFddVar(int32_t elm) {
    if (fddCache_.size() <= static_cast<size_t>(elm)) {
      fddCache_.resize(elm+1, bddfalse);
    }

    if (fddCache_[elm] == bddfalse) {
      fddCache_[elm] = fdd_ithvar(0, elm);
    }

    return fddCache_[elm];
  }
  //}}}

  // Vector cache {{{
  // Cache on top of bdd to vector code
  static std::shared_ptr<std::vector<ValueMap::Id>> getBddVec(bdd pts) {
    if (pts == bddfalse) {
      static std::shared_ptr<std::vector<ValueMap::Id>> bddfalse_vec
        = std::make_shared<std::vector<ValueMap::Id>>();
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
          std::make_shared<std::vector<ValueMap::Id>>(
            std::move(uglyBddVec_))));
    assert(rc.second);
    std::sort(std::begin(*rc.first->second.second),
        std::end(*rc.first->second.second));

    // Return our newly allocated vector
    return rc.first->second.second;
  }

  static void bddToVector(char *varset, int) {
    static int32_t fdd_bits = 0;
    if (fdd_bits == 0) {
      fdd_bits = fdd_varnum(0) * 2 - 1;
    }

    uint32_t dont_care[32];
    uint32_t num_dont_care = 0;
    uint32_t base = 0;

    // odds represent fdd domain 1?
    // Create don't care mask set for the bits in domain 0
    for (uint32_t i = 0, m = 1; i < static_cast<uint32_t>(fdd_bits);
        i += 2, m<<=1) {
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
            // do nothing
          }
      }
    }

    // Speed up handling of small don't care cases...
    // Now, take the base value, and add on the appropriate don't care bits
    switch (num_dont_care) {
      case 2:
        {
          uint32_t x = base | dont_care[1];
          uglyBddVec_.emplace_back(x);
          uglyBddVec_.emplace_back(x | dont_care[0]);
        }
        uglyBddVec_.emplace_back(base | dont_care[0]);
        uglyBddVec_.emplace_back(base);
        break;
      case 1:
        uglyBddVec_.emplace_back(base | dont_care[0]);
        uglyBddVec_.emplace_back(base);
        break;
      case 0:
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
          uglyBddVec_.emplace_back(x);
        }
    }
  }
  //}}}

  // Bdd Static Vars {{{
  static bool bddInitd_;

  // GEPS
  static std::vector<bdd> geps_;
  static bddPair *gepToPts_;
  static bdd ptsDom_;

  // Used to incrementally update GEPs
  static std::set<int32_t> validOffs_;
  static size_t consStartPos_;
  static int32_t maxOffs_;
  static size_t allocPos_;


  static std::vector<bdd> fddCache_;

  static std::vector<ValueMap::Id> uglyBddVec_;

  // Cache:  id -> pair<clock, ptsto>
  static const size_t MaxVecCacheSize = 50000;
  static std::map<uint32_t, std::pair<bool,
    std::shared_ptr<std::vector<ValueMap::Id>>>> vecCache_;
  //}}}
  // }}}

  bdd ptsto_;
  std::unique_ptr<bdd> dynPtsto_ = nullptr;

  mutable bdd iterBdd_ = bddfalse;
  mutable std::shared_ptr<std::vector<ValueMap::Id>> bddVec_ = nullptr;
  //}}}
};

class SVPtstoSet {
  //{{{
 public:
    SVPtstoSet() = default;
    explicit SVPtstoSet(const Bitmap &dyn_pts) :
        dynPtsto_(std::unique_ptr<Bitmap>(new Bitmap(dyn_pts))) { }

    SVPtstoSet(const SVPtstoSet &rhs) {
      ptsto_ = rhs.ptsto_;
      if (rhs.dynPtsto_ != nullptr) {
        dynPtsto_ = std::unique_ptr<Bitmap>(new Bitmap(*rhs.dynPtsto_));
      } else {
        dynPtsto_ = nullptr;
      }
    }
    SVPtstoSet(SVPtstoSet &&) = default;

    SVPtstoSet &operator=(const SVPtstoSet &rhs) {
      ptsto_ = rhs.ptsto_;
      if (rhs.dynPtsto_ != nullptr) {
        dynPtsto_ = std::unique_ptr<Bitmap>(new Bitmap(*rhs.dynPtsto_));
      } else {
        dynPtsto_ = nullptr;
      }
      return *this;
    }
    SVPtstoSet &operator=(SVPtstoSet &&) = default;

    typedef typename SEG::NodeID NodeID;
    bool set(ValueMap::Id id) {
      return ptsto_.test_and_set(id.val());
    }

    void reset(ValueMap::Id id) {
      ptsto_.reset(id.val());
    }

    size_t getSizeNoStruct(ValueMap &map) const {
      std::set<const llvm::Value *> pts_set;

      for (auto obj_id : *this) {
        auto val = map.getValue(obj_id);
        pts_set.insert(val);
      }

      return pts_set.size();
    }

    void setDynSet(const Bitmap &dyn_set) {
      dynPtsto_ = std::unique_ptr<Bitmap>(new Bitmap(dyn_set));
    }

    bool assign(const SVPtstoSet &rhs) {
      Bitmap init = ptsto_;
      ptsto_.clear();
      ptsto_ |= rhs.ptsto_;

      clearDynPtsto();

      return (init != ptsto_);
    }

    void clear() {
      ptsto_.clear();
    }

    bool operator==(const SVPtstoSet &rhs) const {
      return ptsto_ == rhs.ptsto_;
    }

    bool operator!=(const SVPtstoSet &rhs) const {
      return ptsto_ != rhs.ptsto_;
    }

    bool operator&=(const SVPtstoSet &rhs) {
      return ptsto_ &= rhs.ptsto_;
    }

    SVPtstoSet operator&(const SVPtstoSet &rhs) const {
      SVPtstoSet ret(*this);

      ret &= rhs;

      return ret;
    }

    bool operator|=(const SVPtstoSet &rhs) {
      bool ch = ptsto_.orWithIntersect(rhs.ptsto_, dynPtsto_.get());

      return ch;
    }

    bool operator|=(ValueMap::Id &id) {
      Bitmap init = ptsto_;
      bool ch = ptsto_.test_and_set(id.val());
      if (ch) {
        clearDynPtsto();
      }
      return (init != ptsto_);
    }

    /*
    bool orOffs(const SVPtstoSet &rhs, int32_t offs,
        const ObjectMap::StructMap &struct_set) {
      if (offs == 0) {
        return operator|=(rhs);
      }

      bool ret = false;
      Bitmap init = ptsto_;
      for (auto val : rhs.ptsto_) {
        int32_t or_offs = offs;

        // If this isn't a structure, don't treat it with an offset
        auto it = struct_set.find(ObjectMap::ObjID(val));
        // FIXME: We ignore invalid field reads...
        if (it == std::end(struct_set)) {
          continue;
        } else {
          if (it->second <= or_offs) {
            continue;
          }
        }

        ret |= ptsto_.test_and_set(val + or_offs);
      }

      if (ret) {
        clearDynPtsto();
      }

      return (init != ptsto_);
    }
    */

    bool intersectWith(const Bitmap &bmp) {
      return (ptsto_ &= bmp);
    }

    bool test(ValueMap::Id obj_id) {
      return ptsto_.test(obj_id.val());
    }

    bool intersectsIgnoring(SVPtstoSet &rhs, ValueMap::Id ignore) {
      bool ret = false;

      bool lhs_add = ptsto_.test(ignore.val());
      bool rhs_add = rhs.ptsto_.test(ignore.val());

      if (lhs_add) {
        ptsto_.reset(ignore.val());
      }

      if (rhs_add) {
        rhs.ptsto_.reset(ignore.val());
      }

      ret = ptsto_.intersects(rhs.ptsto_);

      if (lhs_add) {
        ptsto_.set(ignore.val());
      }

      if (rhs_add) {
        rhs.ptsto_.set(ignore.val());
      }

      return ret;
    }

    size_t count() const {
      return ptsto_.count();
    }

    size_t singleton() const {
      return ptsto_.singleton();
    }

    bool empty() const {
      return ptsto_.empty();
    }

    class iterator {
      //{{{
     public:
        typedef std::forward_iterator_tag iterator_category;
        typedef ValueMap::Id value_type;
        typedef int32_t difference_type;
        typedef ValueMap::Id * pointer;
        typedef ValueMap::Id & reference;

        // Constructor {{{
        explicit iterator(Bitmap::iterator itr) : itr_(itr) { }
        //}}}

        // Operators {{{
        bool operator==(const iterator &it) const {
          return (itr_ == it.itr_);
        }

        bool operator!=(const iterator &it) const {
          return !operator==(it);
        }

        value_type operator*() const {
          return ValueMap::Id(itr_.operator*());
        }

        iterator &operator++() {
          ++itr_;
          return *this;
        }

        iterator operator++(int) {
          iterator tmp(*this);
          ++itr_;

          return tmp;
        }
        //}}}

     private:
        // Private data {{{
        Bitmap::iterator itr_;
        //}}}
      //}}}
    };

    class const_iterator {
      //{{{
     public:
        typedef std::forward_iterator_tag iterator_category;
        typedef ValueMap::Id value_type;
        typedef int32_t difference_type;
        typedef ValueMap::Id * pointer;
        typedef ValueMap::Id & reference;

        // Constructor {{{
        explicit const_iterator(Bitmap::iterator itr) : itr_(itr) { }
        //}}}

        // Operators {{{
        bool operator==(const const_iterator &it) const {
          return (itr_ == it.itr_);
        }

        bool operator!=(const const_iterator &it) const {
          return !operator==(it);
        }

        const value_type operator*() const {
          return ValueMap::Id(itr_.operator*());
        }

        /*
        value_type operator->() const {
          return ValueMap::Id(itr_.operator->());
        }
        */

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
        Bitmap::iterator itr_;
        //}}}
      //}}}
    };

    iterator begin() {
      return iterator(std::begin(ptsto_));
    }

    iterator end() {
      return iterator(std::end(ptsto_));
    }

    const_iterator begin() const {
      return const_iterator(std::begin(ptsto_));
    }

    const_iterator end() const {
      return const_iterator(std::end(ptsto_));
    }

    const_iterator cbegin() const {
      return const_iterator(std::begin(ptsto_));
    }

    const_iterator cend() const {
      return const_iterator(std::end(ptsto_));
    }

#ifndef SPECSFS_IS_TEST
    friend llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
        const SVPtstoSet &ps) {
      os << "{";
      for (ValueMap::Id id : ps) {
        os << " " << id;
      }
      os << " }";

      return os;
    }
#endif

 private:
    bool clearDynPtsto() {
      bool ret = false;
      if (dynPtsto_ != nullptr) {
        // llvm::dbgs() << "!!!!!CLEAR DYN PTSTO????\n";
        ret = (ptsto_ &= *dynPtsto_);
      }

      return ret;
    }

    Bitmap ptsto_;
    std::unique_ptr<Bitmap> dynPtsto_ = nullptr;
  //}}}
};

// Switch between BddPtstoSet and SVPtstoSet
// typedef SVPtstoSet PtstoSet;
typedef BddPtstoSet PtstoSet;

#endif  // INCLUDE_SOLVEHELPERS_H_
