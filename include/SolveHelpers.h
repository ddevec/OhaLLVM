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

#include "include/ConstraintGraph.h"
#include "include/SEG.h"
#include "include/ObjectMap.h"


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

class DUG;
class DUGNode;

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

    pointer pop(uint32_t &prio) {
      // Try getting our next heap
      if (heap_.empty()) {
        heap_.swap(nextHeap_);
      }

      if (heap_.empty()) {
        return nullptr;
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

    void push(pointer node, uint32_t prio) {
      nextHeap_.emplace_back(node, prio);
      std::push_heap(std::begin(nextHeap_), std::end(nextHeap_));
    }

 private:
    class HeapEntry {
      //{{{
     public:
        HeapEntry(pointer node, uint32_t prio) :
          node_(node), prio_(prio) { }

        pointer node() const {
          return node_;
        }

        int32_t prio() const {
          return prio_;
        }

        bool operator<(const HeapEntry &rhs) const {
          // We want a min heap, so invert the < operator to >
          if (prio() == rhs.prio()) {
            return reinterpret_cast<intptr_t>(node()) <
              reinterpret_cast<intptr_t>(rhs.node());
          }

          return prio() > rhs.prio();
        }

     private:
        pointer node_;
        uint32_t prio_;
      //}}}
    };

    std::vector<HeapEntry> heap_;
    std::vector<HeapEntry> nextHeap_;
  //}}}
};

// FIXME: ?BDDs?
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

    static void PtstoSetInit(ObjectMap &omap, ConstraintGraph &cg) {
      if (!bddInitd()) {
        bddInit(omap, cg);
      }
    }

    typedef typename SEG::NodeID NodeID;
    bool set(ObjectMap::ObjID id) {
      auto init = ptsto_;
      ptsto_ |= getFddVar(id);
      return (init != ptsto_);
    }

    void reset(ObjectMap::ObjID id) {
      ptsto_ &= !getFddVar(id);
    }

    size_t getSizeNoStruct(ObjectMap &omap) const {
      std::set<const llvm::Value *> pts_set;

      for (auto obj_id : *this) {
        auto val = omap.valueAtID(obj_id);
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

      return std::move(ret);
    }

    BddPtstoSet operator-(const BddPtstoSet &rhs) const {
      BddPtstoSet ret(*this);

      ret.ptsto_ -= rhs.ptsto_;

      return std::move(ret);
    }

    bool operator|=(const BddPtstoSet &rhs) {
      auto init = ptsto_;

      ptsto_ |= rhs.ptsto_;

      if (init != ptsto_) {
        clearDynPtsto();
      }

      return init != ptsto_;
    }

    bool operator|=(ObjectMap::ObjID &id) {
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

    bool test(ObjectMap::ObjID obj_id) {
      bdd ret = ptsto_ & getFddVar(obj_id);
      return ret != bddfalse;
    }

    bool intersectsIgnoring(BddPtstoSet &rhs, ObjectMap::ObjID ignore) {
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
        typedef ObjectMap::ObjID value_type;
        typedef int32_t difference_type;
        typedef ObjectMap::ObjID * pointer;
        typedef ObjectMap::ObjID & reference;

        // Constructor {{{
        explicit const_iterator(std::vector<ObjectMap::ObjID>::iterator itr) :
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
          return ObjectMap::ObjID(itr_.operator*());
        }

        /*
        value_type operator->() const {
          return ObjectMap::ObjID(itr_.operator->());
        }
        */

        const_iterator &operator++() {
          ++itr_;
          return *this;
        }

        const_iterator operator++(int) {
          const_iterator tmp(*this);
          ++itr_;

          return std::move(tmp);
        }
        //}}}

     private:
        // Private data {{{
        std::vector<ObjectMap::ObjID>::iterator itr_;
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
      std::for_each(std::begin(ps), std::end(ps),
          [&os] (ObjectMap::ObjID id) {
        os << " " << id;
      });
      os << " }";

      return os;
    }
#endif

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
        bddVec_ = getBddVec(ptsto_);
      }
    }

    // Bdd Static Functions {{{
    // Setup geps! (ugh)
    // For geps needs omap (for object size into)
    //   and cg -- for (for used constraint offsets)
    static void bddInit(ObjectMap &omap, const ConstraintGraph &cg);

    static bool bddInitd() {
      return bddInitd_;
    }

    // Get Fdds {{{
    static bdd getFddVar(ObjectMap::ObjID elm) {
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
    static std::shared_ptr<std::vector<ObjectMap::ObjID>> getBddVec(bdd pts) {
      if (pts == bddfalse) {
        static std::shared_ptr<std::vector<ObjectMap::ObjID>> bddfalse_vec
          = std::make_shared<std::vector<ObjectMap::ObjID>>();
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
            std::make_shared<std::vector<ObjectMap::ObjID>>(
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
        case 1:
          uglyBddVec_.emplace_back(base | dont_care[0]);
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

    static std::vector<bdd> fddCache_;

    static std::vector<ObjectMap::ObjID> uglyBddVec_;

    // Cache:  id -> pair<clock, ptsto>
    static const size_t MaxVecCacheSize = 50000;
    static std::map<uint32_t, std::pair<bool,
      std::shared_ptr<std::vector<ObjectMap::ObjID>>>> vecCache_;
    //}}}
    // }}}

    bdd ptsto_;
    std::unique_ptr<bdd> dynPtsto_ = nullptr;

    mutable bdd iterBdd_ = bddfalse;
    mutable std::shared_ptr<std::vector<ObjectMap::ObjID>> bddVec_ = nullptr;
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
    bool set(ObjectMap::ObjID id) {
      return ptsto_.test_and_set(id.val());
    }

    void reset(ObjectMap::ObjID id) {
      ptsto_.reset(id.val());
    }

    size_t getSizeNoStruct(ObjectMap &omap) const {
      std::set<const llvm::Value *> pts_set;

      for (auto obj_id : *this) {
        auto val = omap.valueAtID(obj_id);
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

    bool operator|=(ObjectMap::ObjID &id) {
      Bitmap init = ptsto_;
      bool ch = ptsto_.test_and_set(id.val());
      if (ch) {
        clearDynPtsto();
      }
      return (init != ptsto_);
    }

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
        /*
        if (it == std::end(struct_set)) {
          or_offs = 0;
        } else {
          if (it->second <= or_offs) {
            or_offs = 0;
          }
        }
        */
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

    bool intersectWith(const Bitmap &bmp) {
      return (ptsto_ &= bmp);
    }

    bool test(ObjectMap::ObjID obj_id) {
      return ptsto_.test(obj_id.val());
    }

    bool intersectsIgnoring(SVPtstoSet &rhs, ObjectMap::ObjID ignore) {
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
        typedef ObjectMap::ObjID value_type;
        typedef int32_t difference_type;
        typedef ObjectMap::ObjID * pointer;
        typedef ObjectMap::ObjID & reference;

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
          return ObjectMap::ObjID(itr_.operator*());
        }

        iterator &operator++() {
          ++itr_;
          return *this;
        }

        iterator operator++(int) {
          iterator tmp(*this);
          ++itr_;

          return std::move(tmp);
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
        typedef ObjectMap::ObjID value_type;
        typedef int32_t difference_type;
        typedef ObjectMap::ObjID * pointer;
        typedef ObjectMap::ObjID & reference;

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
          return ObjectMap::ObjID(itr_.operator*());
        }

        /*
        value_type operator->() const {
          return ObjectMap::ObjID(itr_.operator->());
        }
        */

        const_iterator &operator++() {
          ++itr_;
          return *this;
        }

        const_iterator operator++(int) {
          const_iterator tmp(*this);
          ++itr_;

          return std::move(tmp);
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
      std::for_each(std::begin(ps), std::end(ps),
          [&os] (ObjectMap::ObjID id) {
        os << " " << id;
      });
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

class TopLevelPtsto {
  //{{{
 public:
    typedef typename SEG::NodeID NodeID;
    typedef ObjectMap::ObjID ObjID;

    class PtsPair {
      //{{{
     public:
        explicit PtsPair(ObjID id) : id_(id) { }

        ObjID id() const {
          return id_;
        }

        bool operator<(const PtsPair &rhs) const {
          return id() < rhs.id();
        }

        bool operator<(ObjID rhs) const {
          return id() < rhs;
        }

        std::vector<PtstoSet> &pts() {
          return pts_;
        }

        const std::vector<PtstoSet> &pts() const {
          return pts_;
        }

     private:
        ObjID id_;
        std::vector<PtstoSet> pts_;
      //}}}
    };

    TopLevelPtsto() = default;

    TopLevelPtsto(const std::vector<ObjID> &objs,
        std::map<ObjID, Bitmap> dyn_sets) :
          dynConstraints_(std::begin(dyn_sets), std::end(dyn_sets)) {
      assert(is_sorted(std::begin(objs), std::end(objs)));
      assert(std::adjacent_find(std::begin(objs), std::end(objs))
          == std::end(objs));

      std::for_each(std::begin(objs), std::end(objs),
          [this] (const ObjID &id) {
        data_.emplace_back(id);
      });
    }

    // Allow move assignment {{{
    TopLevelPtsto(TopLevelPtsto &&) = delete;
    // Allow copying... needed in store?
    TopLevelPtsto(const TopLevelPtsto &) = default;

    TopLevelPtsto &operator=(TopLevelPtsto &&) = default;
    TopLevelPtsto &operator=(const TopLevelPtsto &) = delete;
    //}}}

    PtstoSet &at(ObjID id, int32_t offset) {
      auto &vec = atVec(id);

      assert(offset >= 0);
      if (vec.size() < (uint32_t)offset+1) {
        auto it = dynConstraints_.find(id);
        if (it == std::end(dynConstraints_)) {
          vec.resize(offset+1);
        } else {
          PtstoSet base_pts(it->second);
          vec.resize(offset+1, PtstoSet(base_pts));
        }
      }

      return vec[offset];
    }

    PtstoSet &at(ObjID id) {
      return at(id, 0);
    }

    std::vector<PtstoSet> &atVec(ObjID id) {
      auto ret = std::lower_bound(std::begin(data_),
          std::end(data_), id);
      assert(ret != std::end(data_));
      return ret->pts();
    }

    void copy(ObjID src_id, ObjID dest_id) {
      auto it = find(dest_id);
      assert(it == std::end(data_));
      it->pts() = atVec(src_id);
    }

    // Bleh, this is slow
    void remove(ObjID id) {
      auto it = find(id);
      data_.erase(it);
    }

    typedef std::vector<PtsPair>::iterator iterator;
    typedef std::vector<PtsPair>::const_iterator
      const_iterator;

    iterator find(ObjID id) {
      return std::lower_bound(std::begin(data_), std::end(data_),
          id);
    }

    const_iterator find(ObjID id) const {
      return std::lower_bound(std::begin(data_), std::end(data_),
          id);
    }


    iterator begin() {
      return std::begin(data_);
    }

    iterator end() {
      return std::end(data_);
    }

    const_iterator begin() const {
      return std::begin(data_);
    }

    const_iterator end() const {
      return std::end(data_);
    }

    const_iterator cbegin() const {
      return std::begin(data_);
    }

    const_iterator cend() const {
      return std::end(data_);
    }

#ifndef SPECSFS_IS_TEST
    friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
        const TopLevelPtsto &g) {
      o << "( ";
      bool first = true;
      for (auto &pr : g) {
        if (!first) {
          o << ", ";
        }

        for (auto &pts_set : pr.pts()) {
          o << pr.id() << "->" << pts_set;
        }
        first = false;
      }
      o << " )";
      return o;
    }
#endif

 private:
    // std::map<ObjID, std::vector<PtstoSet>> data_;
    std::unordered_map<ObjectMap::ObjID, Bitmap, ObjectMap::ObjID::hasher>
      dynConstraints_;
    std::vector<PtsPair> data_;
  //}}}
};

// This is fine?
// FIXME: Need to have a way to add objects to our ptsto graph
class PtstoGraph {
  //{{{
 public:
    typedef typename SEG::NodeID NodeID;
    typedef ObjectMap::ObjID ObjID;

    PtstoGraph() = default;

    explicit PtstoGraph(const std::vector<ObjID> &objs) {
      // Assert this vector is sorted and unique
      assert(is_sorted(std::begin(objs), std::end(objs)));
      assert(std::adjacent_find(std::begin(objs), std::end(objs))
          == std::end(objs));

      for (auto obj_id : objs) {
        data_.emplace_back(obj_id);
      }
    }

    // Allow move assignment {{{
    PtstoGraph(PtstoGraph &&) = delete;
    // Allow copying... needed in store?
    PtstoGraph(const PtstoGraph &) = default;

    PtstoGraph &operator=(PtstoGraph &&) = default;
    PtstoGraph &operator=(const PtstoGraph &) = delete;
    //}}}

    PtstoSet &at(ObjID id) {
      auto it = std::lower_bound(std::begin(data_), std::end(data_), id);
      assert(it != std::end(data_) && it->id() == id);
      return it->pts();
    }

    const PtstoSet &at(ObjID id) const {
      auto it = std::lower_bound(std::begin(data_), std::end(data_), id);
      assert(it != std::end(data_));
      return it->pts();
    }

    bool has(ObjID id) const {
      auto it = std::lower_bound(std::begin(data_), std::end(data_), id);
      return (it != std::end(data_) && it->id() == id);
    }

    bool operator|=(PtstoGraph &rhs) {
      // Oh goody...
      bool ret = false;
      for (auto obj_id : rhs.change_) {
        auto &rhs_ptsset = rhs.at(obj_id);
        auto &lhs_ptsset = at(obj_id);

        bool loop_ch = (lhs_ptsset |= rhs_ptsset);
        if (loop_ch) {
          change_.insert(obj_id);
        }
      }

      return ret;
    }

    bool assign(ObjID elm, const PtstoSet &ptsset) {
      bool ret = at(elm).assign(ptsset);

      if (ret) {
        change_.insert(elm);
      }

      return ret;
    }

    bool orElement(ObjID elm, const PtstoSet &rhs) {
      bool ret = false;

      auto &lhs_ptsset = at(elm);
      ret |= (lhs_ptsset |= rhs);

      if (ret) {
        change_.insert(elm);
      }

      return ret;
    }

    bool orExcept(PtstoGraph &rhs,
        ObjID exception) {
      bool ret = false;

      for (ObjID obj_id : rhs.change_) {
        if (obj_id != exception) {
          auto &lhs_ptsset = at(obj_id);
          auto &rhs_ptsset = rhs.at(obj_id);

          bool loop_ch = (lhs_ptsset |= rhs_ptsset);

          if (loop_ch) {
            ret = true;
            change_.insert(obj_id);
          }
        }
      }

      return ret;
    }

    bool canOrPart(const PtstoGraph &rhs,
        std::vector<__PartID> &part_map,
        __PartID part_id) const {
      for (ObjID obj_id : rhs.change_) {
        if (part_map[obj_id.val()] != part_id) {
          continue;
        }

        if (!has(obj_id)) {
          return false;
        }
      }

      return true;
    }

    bool orPart(const PtstoGraph &rhs,
        std::vector<__PartID> &part_map,
        __PartID part_id) {
      bool ret = false;

      for (ObjID obj_id : rhs.change_) {
        if (part_map[obj_id.val()] != part_id) {
          continue;
        }

        auto &rhs_ptsset = rhs.at(obj_id);
        auto &lhs_ptsset = at(obj_id);

        bool loop_ch = (lhs_ptsset |= rhs_ptsset);
        if (loop_ch) {
          ret = true;
          change_.insert(obj_id);
        }
      }

      return ret;
    }

    bool hasChanged() {
      change_.unique();
      return !change_.empty();
    }

    void resetChanged() {
      change_.clear();
    }

    /*
    typedef std::map<ObjID, PtstoSet>::iterator iterator;
    typedef std::map<ObjID, PtstoSet>::const_iterator
      const_iterator;

    iterator begin() {
      return std::begin(data_);
    }

    iterator end() {
      return std::end(data_);
    }

    const_iterator begin() const {
      return std::begin(data_);
    }

    const_iterator end() const {
      return std::end(data_);
    }

    const_iterator cbegin() const {
      return data_.cbegin();
    }

    const_iterator cend() const {
      return data_.cend();
    }
    */

    bool empty() const {
      return data_.empty();
    }

    friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
        const PtstoGraph &g) {
      o << "( ";
      bool first = true;
      for (auto &ptspr : g.data_) {
        if (!first) {
          o << ", ";
        }

        o << ptspr.id() << "->" << ptspr.pts();

        first = false;
      }
      o << " )";
      return o;
    }

 private:
    class ChangeSet {
      //{{{
     public:
        ChangeSet() = default;

        void insert(ObjID id) {
          change_.push_back(id);
        }

        void unique() {
          std::sort(std::begin(change_), std::end(change_));
          auto it = std::unique(std::begin(change_), std::end(change_));
          change_.erase(it, std::end(change_));
        }

        bool empty() const {
          return change_.empty();
        }

        bool has(ObjID id) {
          return std::binary_search(std::begin(change_), std::end(change_),
              id);
        }

        void clear() {
          change_.clear();
        }

        typedef std::vector<ObjID>::iterator iterator;
        typedef std::vector<ObjID>::const_iterator const_iterator;

        const_iterator begin() const {
          return std::begin(change_);
        }

        const_iterator end() const {
          return std::end(change_);
        }

        const_iterator cbegin() const {
          return std::begin(change_);
        }

        const_iterator cend() const {
          return std::end(change_);
        }

        iterator begin() {
          return std::begin(change_);
        }

        iterator end() {
          return std::end(change_);
        }

     private:
        std::vector<ObjID> change_;
      //}}}
    };

    class PtsPair {
      //{{{
     public:
        explicit PtsPair(ObjID id) : id_(id) { }
        ObjID id() const {
          return id_;
        }

        bool operator<(const PtsPair &rhs) const {
          return id() < rhs.id();
        }

        bool operator<(ObjID rhs) const {
          return id() < rhs;
        }

        PtstoSet &pts() {
          return pts_;
        }

        const PtstoSet &pts() const {
          return pts_;
        }

     private:
        ObjID id_;
        PtstoSet pts_;
      //}}}
    };

    ChangeSet change_;
    // std::map<ObjID, PtstoSet> data_;
    std::vector<PtsPair> data_;
  //}}}
};

#endif  // INCLUDE_SOLVEHELPERS_H_
