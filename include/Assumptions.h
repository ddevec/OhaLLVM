/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_ASSUMPTIONS_H_
#define INCLUDE_ASSUMPTIONS_H_

#include <algorithm>
#include <map>
#include <memory>
#include <set>
#include <vector>

#include "include/util.h"

#include "include/ValueMap.h"
#include "include/ExtInfo.h"
#include "include/SolveHelpers.h"

#include "llvm/Constants.h"
#include "llvm/Function.h"
#include "llvm/Module.h"

// Okay how to handle this...
// Assumptions have dependencies...
//   For example, the DynPtsto assumption depends on instrumenting both the
//   pointer assignment, and the allocation/deallocation site of any pointer
//   that may be assigned to it.
//
// Lets have a "calc dependencies" routine

typedef std::unordered_multimap<ValueMap::Id, llvm::Value *>
    free_location_multimap;

class SetCache {  //{{{
 public:
  SetCache() = default;

  // Dedups some ids
  int32_t getID(const std::set<ValueMap::Id> &pts_set) {
    /*
    llvm::dbgs() << "Doing find on mappings!\n";
    llvm::dbgs() << "  mappings.size() is: " << mappings_.size() << "\n";
    llvm::dbgs() << "  pts_set is:";
    for (auto obj_id : pts_set) {
      llvm::dbgs() << " " << obj_id;
    }
    llvm::dbgs() << "\n";
    */

    auto it = mappings_.find(pts_set);
    if (it == std::end(mappings_)) {
      auto ret = mappings_.emplace(pts_set, curID_);
      assert(ret.second);
      curID_++;

      it = ret.first;
    }

    return it->second;
  }

  void addGVUse(ValueMap::Id gv) {
    gvUse_.insert(gv);
  }

  bool gvUsed(ValueMap::Id gv) const {
    return (gvUse_.find(gv) != std::end(gvUse_));
  }

  // Iterator... {{{
  class const_iterator :
    public std::map<std::set<ValueMap::Id>, int32_t>::const_iterator {
   public:
     typedef std::map<std::set<ValueMap::Id>, int32_t>::const_iterator
       base_iter;

     const_iterator() = default;
     explicit const_iterator(base_iter s) :
       base_iter(s) { }

     const std::set<ValueMap::Id> *operator->() {
       return &(base_iter::operator->()->first);
     }

     const std::set<ValueMap::Id> &operator*() {
       return base_iter::operator*().first;
     }
  };
  //}}}

  typedef std::set<ValueMap::Id>::const_iterator
    const_gv_iterator;

  void addRet(llvm::Function *fcn) {
    retFcns_.insert(fcn);
  }

  bool hasRet(llvm::Function *fcn) {
    return (retFcns_.find(fcn) != std::end(retFcns_));
  }

  const_iterator begin() const {
    return const_iterator(std::begin(mappings_));
  }

  const_iterator end() const {
    return const_iterator(std::begin(mappings_));
  }

  const_gv_iterator gv_begin() const {
    return std::begin(gvUse_);
  }

  const_gv_iterator gv_end() const {
    return std::end(gvUse_);
  }

 private:
  std::set<llvm::Function *> retFcns_;
  std::set<ValueMap::Id> gvUse_;
  std::map<std::set<ValueMap::Id>, int32_t> mappings_;
  int32_t curID_ = 0;
};
//}}}

// InstrumentationSite classes {{{
class InstrumentationSite {  //{{{
 public:
    enum class Kind {
      AllocInst,
      FreeInst,
      AssignmentInst,
      SetCheckInst,
      VisitInst
    };

    virtual bool operator<(const InstrumentationSite &is) const = 0;
    virtual bool operator==(const InstrumentationSite &is) const = 0;

    virtual int64_t approxCost() = 0;
    virtual bool doInstrument(llvm::Module &m, const ExtLibInfo &ext_info);

    virtual llvm::BasicBlock *getBB() const = 0;

    static bool classof(const InstrumentationSite *) {
      return true;
    }

    Kind getKind() const {
      return kind_;
    }

    friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
        const InstrumentationSite &fi) {
      fi.printInst(o);
      return o;
    }

 private:
    Kind kind_;

 protected:
    explicit InstrumentationSite(Kind kind) : kind_(kind) { }
    virtual void printInst(llvm::raw_ostream &o) const;
};
//}}}

class AllocInst : public InstrumentationSite {  //{{{
 public:
    AllocInst(llvm::Instruction *alloc_inst, ValueMap::Id alloc_obj) :
      InstrumentationSite(InstrumentationSite::Kind::AllocInst),
      allocInst_(alloc_inst), allocObj_(alloc_obj) { }

    bool operator<(const InstrumentationSite &is) const override {
      if (getKind() != is.getKind()) {
        return getKind() < is.getKind();
      }

      auto &ai = cast<AllocInst>(is);

      if (allocObj_ < ai.allocObj_) {
        return allocObj_ < ai.allocObj_;
      }

      return allocInst_ < ai.allocInst_;
    }

    bool operator==(const InstrumentationSite &is) const override {
      if (getKind() != is.getKind()) {
        return false;
      }

      auto &ai = cast<AllocInst>(is);

      return allocObj_ == ai.allocObj_ && allocInst_ == ai.allocInst_;
    }

    int64_t approxCost() override {
      return 1;
    }

    llvm::Instruction *getInst() const {
      return allocInst_;
    }

    bool doInstrument(llvm::Module &m, const ExtLibInfo &ext_info) override;

    static bool classof(const InstrumentationSite *is) {
      return is->getKind() == InstrumentationSite::Kind::AllocInst;
    }

    llvm::BasicBlock *getBB() const override {
      return allocInst_->getParent();
    }

 private:
    llvm::Instruction *allocInst_;
    ValueMap::Id allocObj_;

 protected:
    virtual void printInst(llvm::raw_ostream &o) const {
      o << "AllocInst " << allocObj_ << ": " << *allocInst_;
    }
};
//}}}

// Used to represent a free=alloc assumption made by the DynPtsto assumptions
class DoubleAllocInst : public AllocInst {  //{{{
 public:
    DoubleAllocInst(llvm::Instruction *alloc_inst, ValueMap::Id alloc_obj) :
      AllocInst(alloc_inst, alloc_obj) { }

    int64_t approxCost() override {
      return 2 * AllocInst::approxCost();
    }

    bool doInstrument(llvm::Module &, const ExtLibInfo &) override {
      llvm_unreachable("Shouldn't try to instrument a double alloc");
    }
};
//}}}

class FreeInst : public InstrumentationSite {  //{{{
 public:
    explicit FreeInst(llvm::Instruction *free_inst, SetCache &set_cache) :
      InstrumentationSite(InstrumentationSite::Kind::FreeInst),
      freeInst_(free_inst), setCache_(set_cache) { }

    bool operator<(const InstrumentationSite &is) const override {
      if (getKind() != is.getKind()) {
        return getKind() < is.getKind();
      }

      auto &fi = cast<FreeInst>(is);

      return freeInst_ < fi.freeInst_;
    }

    bool operator==(const InstrumentationSite &is) const override {
      if (getKind() != is.getKind()) {
        return false;
      }

      auto &fi = cast<FreeInst>(is);

      return freeInst_ == fi.freeInst_;
    }

    int64_t approxCost() override {
      return 1;
    }

    bool doInstrument(llvm::Module &m, const ExtLibInfo &info) override;

    static bool classof(const InstrumentationSite *is) {
      return is->getKind() == InstrumentationSite::Kind::FreeInst;
    }

    llvm::BasicBlock *getBB() const override {
      return freeInst_->getParent();
    }

 private:
    llvm::Instruction *freeInst_;
    SetCache &setCache_;

 protected:
    virtual void printInst(llvm::raw_ostream &o) const {
      o << "FreeInst " << *freeInst_;
    }
};
//}}}

// Checks a ptsto set when a pointer is assigned
class AssignmentInst : public InstrumentationSite {  //{{{
 public:
    AssignmentInst(llvm::Instruction *assign_inst,
        ValueMap::Id assign_val) :
      InstrumentationSite(InstrumentationSite::Kind::AssignmentInst),
      assignInst_(assign_inst), assignVal_(assign_val) { }

    bool operator<(const InstrumentationSite &is) const override {
      if (getKind() != is.getKind()) {
        return getKind() < is.getKind();
      }

      auto &ai = cast<AssignmentInst>(is);

      if (assignVal_ != ai.assignVal_) {
        return assignVal_ < ai.assignVal_;
      }

      return assignInst_ < ai.assignInst_;
    }

    bool operator==(const InstrumentationSite &is) const override {
      if (getKind() != is.getKind()) {
        return false;
      }

      auto &ai = cast<AssignmentInst>(is);

      return assignVal_ == ai.assignVal_ && assignInst_ == ai.assignInst_;
    }

    int64_t approxCost() override {
      return 1;
    }

    bool doInstrument(llvm::Module &m, const ExtLibInfo &ext_info) override;

    static bool classof(const InstrumentationSite *is) {
      return is->getKind() == InstrumentationSite::Kind::AssignmentInst;
    }

    llvm::BasicBlock *getBB() const override {
      return assignInst_->getParent();
    }

 private:
    llvm::Instruction *assignInst_;
    ValueMap::Id assignVal_;

 protected:
    virtual void printInst(llvm::raw_ostream &o) const {
      o << "AssignmentInst " << assignVal_ << ": " << *assignInst_;
    }
};
//}}}

// Checks to see if a value is allocated within a certain object set
class SetCheckInst : public InstrumentationSite {  //{{{
 public:
    SetCheckInst(const llvm::Value *assign_inst,
        const std::vector<ValueMap::Id> &check_set,
        SetCache &set_cache) :
      InstrumentationSite(InstrumentationSite::Kind::SetCheckInst),
      assignInst_(const_cast<llvm::Value *>(assign_inst)),
      checkSet_(std::begin(check_set), std::end(check_set)),
      setCache_(set_cache) { }

    bool operator<(const InstrumentationSite &is) const override {
      if (getKind() != is.getKind()) {
        return getKind() < is.getKind();
      }

      auto &ai = cast<SetCheckInst>(is);

      if (assignInst_ != ai.assignInst_) {
        return assignInst_ < ai.assignInst_;
      }

      return checkSet_ < ai.checkSet_;
    }

    bool operator==(const InstrumentationSite &is) const override {
      if (getKind() != is.getKind()) {
        return false;
      }

      auto &ai = cast<SetCheckInst>(is);

      return assignInst_ == ai.assignInst_ && checkSet_ == ai.checkSet_;
    }

    int64_t approxCost() override {
      return 1;
    }

    bool doInstrument(llvm::Module &m, const ExtLibInfo &ext_info) override;

    static bool classof(const InstrumentationSite *is) {
      return is->getKind() == InstrumentationSite::Kind::SetCheckInst;
    }

    llvm::BasicBlock *getBB() const override {
      if (auto arg = dyn_cast<llvm::Argument>(assignInst_)) {
        return &arg->getParent()->getEntryBlock();
      }

      return cast<llvm::Instruction>(assignInst_)->getParent();
    }

 private:
    llvm::Value *assignInst_;
    std::set<ValueMap::Id> checkSet_;

    SetCache &setCache_;

 protected:
    virtual void printInst(llvm::raw_ostream &o) const {
      o << "SetCheckInst " << *assignInst_;
    }
};
//}}}

// throws issue if block is visited
class VisitInst : public InstrumentationSite {  //{{{
 public:
    explicit VisitInst(llvm::BasicBlock *bb) :
      InstrumentationSite(InstrumentationSite::Kind::VisitInst),
      bb_(bb) { }

    bool operator<(const InstrumentationSite &is) const override {
      if (getKind() != is.getKind()) {
        return getKind() < is.getKind();
      }

      auto &vi = cast<VisitInst>(is);

      return bb_ < vi.bb_;
    }

    bool operator==(const InstrumentationSite &is) const override {
      if (getKind() != is.getKind()) {
        return false;
      }

      auto &vi = cast<VisitInst>(is);

      return bb_ == vi.bb_;
    }

    int64_t approxCost() override {
      return 1;
    }

    bool doInstrument(llvm::Module &m, const ExtLibInfo &ext_info) override;

    static bool classof(const InstrumentationSite *is) {
      return is->getKind() == InstrumentationSite::Kind::VisitInst;
    }

    llvm::BasicBlock *getBB() const override {
      return bb_;
    }

 private:
    llvm::BasicBlock *bb_;

 protected:
    virtual void printInst(llvm::raw_ostream &o) const {
      o << "VisitInst: " << bb_->getName();
    }
};
//}}}
//}}}

// Assumption classes {{{
class Assumption {  //{{{
 public:
    enum class Kind {
      DynPtsto,
      DeadCode
    };

    virtual Assumption *clone() const = 0;

    virtual void remap(const util::ObjectRemap<ValueMap::Id> &) { }

    Kind getKind() const {
      return kind_;
    }

    static bool classof(const Assumption *) {
      return true;
    }

    std::vector<std::unique_ptr<InstrumentationSite>> getInstrumentation(
        ValueMap &obj, llvm::Module &m,
        const free_location_multimap &free_locations, SetCache &cache) const {
      return calcDependencies(obj, m, free_locations, cache);
    }


    std::vector<std::unique_ptr<InstrumentationSite>>
    getApproxDependencies(ValueMap &omap, const llvm::Module &m) {
      return approxDependencies(omap, m);
    }

 private:
    Assumption::Kind kind_;

 protected:
    explicit Assumption(Assumption::Kind kind) : kind_(kind) { }

    // Considers what would have to be instrumented to make this assumption
    // NOTE: We may need a ptsto analysis to know the real dependencies
    virtual std::vector<std::unique_ptr<InstrumentationSite>>
      approxDependencies(
        ValueMap &omap, const llvm::Module &m) const = 0;

    // For some forms of instrumentation we'll need to know the ptsto set to
    //   calc the true dependencies
    virtual std::vector<std::unique_ptr<InstrumentationSite>> calcDependencies(
        ValueMap &omap, llvm::Module &m,
        const free_location_multimap &free_locations,
        SetCache &cache) const = 0;
};
//}}}

class PtstoAssumption : public Assumption {  //{{{
 public:
    PtstoAssumption(const llvm::Value *inst,
        const std::vector<const llvm::Value *> &ptstos) :
          Assumption(Assumption::Kind::DynPtsto),
          instOrArg_(inst), ptstos_(ptstos) { }

    static bool classof(const Assumption *a) {
      return a->getKind() == Assumption::Kind::DynPtsto;
    }

    Assumption *clone() const override {
      return new PtstoAssumption(*this);
    }

    // no more remap
    void remap(const util::ObjectRemap<ValueMap::Id> &) override { }

 protected:
    std::vector<std::unique_ptr<InstrumentationSite>>
      calcDependencies(
        ValueMap &omap, llvm::Module &m,
        const free_location_multimap &free_locations,
        SetCache &) const override;

    // To approx dependencies we make 2 alloc dependencies, and one inst
    // dependency.. we assume the cost of allow ~= the cost of free
    std::vector<std::unique_ptr<InstrumentationSite>>
      approxDependencies(
        ValueMap &omap, const llvm::Module &m) const override;

 private:
    // ValueMap::Id objID_;
    const llvm::Value *instOrArg_;
    std::vector<const llvm::Value *> ptstos_;
};
//}}}

class DeadCodeAssumption : public Assumption {  //{{{
 public:
    explicit DeadCodeAssumption(llvm::BasicBlock *bb) :
      Assumption(Assumption::Kind::DeadCode), bb_(bb) { }

    static bool classof(const Assumption *a) {
      return a->getKind() == Assumption::Kind::DeadCode;
    }

    Assumption *clone() const override {
      return new DeadCodeAssumption(*this);
    }

 private:
    llvm::BasicBlock *bb_;

 protected:
    std::vector<std::unique_ptr<InstrumentationSite>>
      calcDependencies(
        ValueMap &obj, llvm::Module &m,
        const free_location_multimap &free_locations,
        SetCache &) const override;

    // Approx dependencies == calcDependencies in this instance
    std::vector<std::unique_ptr<InstrumentationSite>> approxDependencies(
        ValueMap &obj, const llvm::Module &m) const override;
};
//}}}
//}}}
//
class AssumptionSet {
  //{{{
 public:
  // Constructors {{{
  AssumptionSet() = default;
  AssumptionSet(const AssumptionSet &as) : assumptions_(as.size()) {
    assumptions_.reserve(as.size());
    for (auto &pasm : as) {
      assumptions_.emplace_back(pasm->clone());
    }
  }

  AssumptionSet &operator=(const AssumptionSet &) = delete;

  AssumptionSet(AssumptionSet &&) = default;
  AssumptionSet &operator=(AssumptionSet &&) = default;
  //}}}

  // Accessors {{{
  size_t size() const {
    return assumptions_.size();
  }
  //}}}

  // Iteration {{{
  typedef std::vector<std::unique_ptr<Assumption>>::iterator iterator;
  typedef std::vector<std::unique_ptr<Assumption>>::const_iterator
    const_iterator;

  iterator begin() {
    return std::begin(assumptions_);
  }

  iterator end() {
    return std::end(assumptions_);
  }

  const_iterator cbegin() const {
    return std::begin(assumptions_);
  }

  const_iterator cend() const {
    return std::end(assumptions_);
  }

  const_iterator begin() const {
    return std::begin(assumptions_);
  }

  const_iterator end() const {
    return std::end(assumptions_);
  }
  //}}}

  void add(std::unique_ptr<Assumption> a) {
    assumptions_.emplace_back(std::move(a));
  }

  void updateObjIDs(const util::ObjectRemap<ValueMap::Id> &remap) {
    for (auto &pasm : assumptions_) {
      pasm->remap(remap);
    }
  }

 private:
  std::vector<std::unique_ptr<Assumption>> assumptions_;
  //}}}
};


// Helper functions {{{
llvm::Function *getAllocaFunction(llvm::Module &m);
llvm::Function *getAllocFunction(llvm::Module &m);
llvm::Function *getRetFunction(llvm::Module &m);
llvm::Function *getCallFunction(llvm::Module &m);
llvm::Function *getFreeFunction(llvm::Module &m);
llvm::Function *getAssignFunction(llvm::Module &m);
llvm::Function *getVisitFunction(llvm::Module &m);
//}}}

#endif  // INCLUDE_ASSUMPTIONS_H_
