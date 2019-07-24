/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_INSTLABELER_H_
#define INCLUDE_INSTLABELER_H_

#include <map>
#include <set>
#include <sstream>
#include <vector>
#include <utility>

#include "include/util.h"

#include "include/lib/UnusedFunctions.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

class InstLabeler {
 //{{{
 public:
  InstLabeler(llvm::Module &m, const UnusedFunctions *dyn_info) {
    int64_t inst_id = 0;

    int fcn_cnt = 0;

    for (auto &fcn : m) {
      bool fcn_used = dyn_info == nullptr || dyn_info->isReallyUsed(fcn);
      if (!fcn.isDeclaration() && fcn_used) {
        usedFcns_.push_back(&fcn);
        fcnToID_[&fcn] = usedInsts_.size();
        usedInsts_.push_back(std::vector<const llvm::Instruction *>());

        for (auto &bb : fcn) {
          bool bb_used = dyn_info == nullptr || dyn_info->isReallyUsed(bb);
          if (bb_used) {
            for (auto &inst : bb) {
              usedInsts_[fcn_cnt].push_back(&inst);
              totalUsedInsts_++;
            }
          }
        }

        totalInsts_ += std::distance(inst_begin(fcn), inst_end(fcn));

        fcn_cnt++;
      }

      for (auto &bb : fcn) {
        for (auto &inst : bb) {
          idToInst_[inst_id] = &inst;
          instToID_[&inst] = inst_id;
          inst_id++;
        }
      }
    }
  }

  explicit InstLabeler(llvm::Module &m) : InstLabeler(m, nullptr) { }

  int64_t totalInsts() const {
    return totalInsts_;
  }

  int64_t totalUsedInsts() const {
    return totalUsedInsts_;
  }

  int64_t getNumUsedFcns() const {
    return usedInsts_.size();
  }

  const std::vector<const llvm::Instruction *> &
  getUsedInsts(int64_t fcn_id) const {
    assert(fcn_id >= 0 &&
        static_cast<size_t>(fcn_id) < usedInsts_.size());
    return usedInsts_[fcn_id];
  }

  const llvm::Instruction *getInst(int64_t inst_id) const {
    return idToInst_.at(inst_id);
  }

  bool hasID(const llvm::Instruction *inst) const {
    return instToID_.find(inst) != std::end(instToID_);
  }

  int64_t getID(const llvm::Instruction *inst) const {
    return instToID_.at(inst);
  }

 private:
  int64_t totalInsts_ = 0;
  int64_t totalUsedInsts_ = 0;

  std::vector<std::vector<const llvm::Instruction *>> usedInsts_;
  std::vector<const llvm::Function *> usedFcns_;

  std::map<const llvm::Function *, int64_t> fcnToID_;

  std::map<const llvm::Instruction *, int64_t> instToID_;
  std::map<int64_t, const llvm::Instruction *> idToInst_;

  std::vector<std::vector<const llvm::Instruction *>> reallyUsedInsts_;
  std::vector<const llvm::Function *> reallyUsedFcns_;
  //}}}
};

class InstWriter {
  //{{{
 public:
  template<typename iter_type>
  static void Write(std::ostream &os, int64_t header_id,
      iter_type cur, iter_type end,
      const InstLabeler &l) {
    // Okay, write out a label for each instruction
    os << header_id << ":";
    for (; cur != end; ++cur) {
      auto inst = dyn_cast<llvm::Instruction>(*cur);
      if (inst != nullptr && l.hasID(inst)) {
        auto id = l.getID(inst);
        // llvm::dbgs() << "Writing inst(" << id << "): " << *inst << "\n";
        os << " " << id;
      }
    }
    os << std::endl;
  }
  //}}}
};

class InstReader {
  //{{{
 public:
  static std::pair<int64_t, std::vector<const llvm::Instruction *>>
  Read(std::istream &is, const InstLabeler &l) {
    std::vector<const llvm::Instruction *> ret_vec;

    std::string line;

    if (!std::getline(is, line, ':')) {
      return std::make_pair(-1, std::move(ret_vec));
    }

    std::stringstream strm(line);
    int64_t header_id;
    strm >> header_id;

    std::getline(is, line);

    std::stringstream converter(line);

    int32_t inst_id;
    converter >> inst_id;
    while (!converter.fail()) {
      // llvm::dbgs() << "Reading id: " << inst_id << "\n";
      auto inst = l.getInst(inst_id);
      ret_vec.push_back(inst);
      // llvm::dbgs() << "got inst: " << *inst << "\n";

      converter >> inst_id;
    }

    return std::make_pair(header_id, std::move(ret_vec));
  }
  //}}}
};

#endif  // INCLUDE_INSTLABELER_H_
