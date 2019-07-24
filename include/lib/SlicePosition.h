/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_LIB_SLICEPOSITION_H_
#define INCLUDE_LIB_SLICEPOSITION_H_

#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

class SlicePosition {
 public:
  SlicePosition() = default;
  SlicePosition(const llvm::Instruction *inst, const llvm::Module &m) {
    fcnNum_ = 0;
    auto fcn_goal = inst->getParent()->getParent();
    for (auto &fcn : m) {
      if (&fcn == fcn_goal) {
        break;
      }
      fcnNum_++;
    }

    instNum_ = 0;
    for (auto it = inst_begin(fcn_goal), en = inst_end(fcn_goal);
        it != en;
        ++it) {
      if (&(*it) == inst) {
        break;
      }
      instNum_++;
    }
  }

  const llvm::Instruction *inst(const llvm::Module &m) const {
    auto fcn_it = std::begin(m);
    std::advance(fcn_it, fcnNum_);
    auto inst_it = inst_begin(&(*fcn_it));
    std::advance(inst_it, instNum_);

    return &(*inst_it);
  }

  friend std::ostream &operator<<(std::ostream &os, const SlicePosition &pos) {
    os << pos.fcnNum_ << " " << pos.instNum_;

    return os;
  }

  friend std::istream &operator>>(std::istream &is, SlicePosition &pos) {
    is >> pos.fcnNum_;
    is >> pos.instNum_;

    return is;
  }

 private:
  int32_t fcnNum_ = -1;
  int32_t instNum_ = -1;
};

#endif  // INCLUDE_LIB_SLICEPOSITION_H_
