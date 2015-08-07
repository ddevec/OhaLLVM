/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_SOLVEHELPERS_H_
#define INCLUDE_SOLVEHELPERS_H_

#include <map>
#include <queue>
#include <utility>
#include <vector>

#include "llvm/ADT/SparseBitVector.h"

// Bitmap used in many places (and by Andersen's) to represent ptsto
typedef llvm::SparseBitVector<> Bitmap;

// Required for using a Bitmap as a std::map key (used for ID gathering) {{{
struct BitmapLT {
  bool operator() (const Bitmap &b1, const Bitmap &b2) {
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
//}}}


class DUGNode;

// FIXME: Build a better (read - priority) work queue
class Worklist {
  //{{{
 public:
    DUGNode *pop() {
      auto ret = q_.front();
      q_.pop();
      return ret;
    }

    void push(DUGNode *pnd) {
      q_.push(pnd);
    }

 private:
    std::queue<DUGNode *> q_;
  //}}}
};

// FIXME: BDDs
class PtstoSet {
  //{{{
 public:
    typedef typename SEG<ObjectMap::ObjID>::NodeID NodeID;
    bool set(ObjectMap::ObjID id) {
      return ptsto_.test_and_set(id.val());
    }

    void clear() {
      ptsto_.clear();
    }

    bool operator|=(const PtstoSet &rhs) {
      return ptsto_ |= rhs.ptsto_;
    }

    bool size() const {
      return ptsto_.count();
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

        /*
        value_type operator->() const {
          return ObjectMap::ObjID(itr_.operator->());
        }
        */

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

    iterator begin() {
      return iterator(std::begin(ptsto_));
    }

    iterator end() {
      return iterator(std::end(ptsto_));
    }

 private:
    Bitmap ptsto_;
  //}}}
};

// This is fine?
// FIXME: Need to have a way to add objects to our ptsto graph
class PtstoGraph {
  //{{{
 public:
    typedef typename SEG<ObjectMap::ObjID>::NodeID NodeID;

    PtstoGraph() = default;

    explicit PtstoGraph(const std::vector<NodeID> &objs) {
      std::for_each(std::begin(objs), std::end(objs),
          [this] (const NodeID &id) {
        data_.emplace(std::piecewise_construct, std::make_tuple(id),
          std::make_tuple());
      });
    }

    // Allow move assignment {{{
    PtstoGraph(PtstoGraph &&) = delete;
    // Allow copying... needed in store?
    PtstoGraph(const PtstoGraph &) = default;

    PtstoGraph &operator=(PtstoGraph &&) = default;
    PtstoGraph &operator=(const PtstoGraph &) = delete;
    //}}}

    PtstoSet &at(NodeID id) {
      return data_.at(id);
    }

    bool operator|=(const PtstoGraph &rhs) {
      // Oh goody...
      bool ret = false;
      std::for_each(std::begin(rhs.data_), std::end(rhs.data_),
          [this, &ret] (const std::pair<const NodeID, PtstoSet> &pr) {
        ret |= (data_.at(pr.first) |= pr.second);
      });

      return ret;
    }

    void clear(NodeID id) {
      data_.at(id).clear();
    }

    typedef std::map<NodeID, PtstoSet>::iterator iterator;
    typedef std::map<NodeID, PtstoSet>::const_iterator const_iterator;

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

 private:
    std::map<NodeID, PtstoSet> data_;
  //}}}
};

#endif  // INCLUDE_SOLVEHELPERS_H_
