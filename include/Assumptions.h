/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_ASSUMPTIONS_H_
#define INCLUDE_ASSUMPTIONS_H_

#include <memory>
#include <set>
#include <vector>

#include "include/SpecSFS.h"

#include "include/util.h"
#include "include/ObjectMap.h"

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

typedef std::unordered_multimap<ObjectMap::ObjID, ObjectMap::ObjID,
        ObjectMap::ObjID::hasher> free_location_multimap;

// InstrumentationSite classes {{{
class InstrumentationSite {  //{{{
 public:
    enum class Kind {
      AllocInst,
      FreeInst,
      AssignmentInst,
      VisitInst
    };

    virtual bool operator<(const InstrumentationSite &is) const = 0;

    virtual int64_t approxCost() = 0;
    virtual bool doInstrument(llvm::Module &m);

    static bool classof(const InstrumentationSite *) {
      return true;
    }

    Kind getKind() const {
      return kind_;
    }

 private:
    Kind kind_;

 protected:
    explicit InstrumentationSite(Kind kind) : kind_(kind) { }
};
//}}}

class AllocInst : public InstrumentationSite {  //{{{
 public:
    AllocInst(llvm::Instruction *alloc_inst, ObjectMap::ObjID alloc_obj) :
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

    int64_t approxCost() override {
      return 1;
    }

    llvm::Instruction *getInst() const {
      return allocInst_;
    }

    bool doInstrument(llvm::Module &m) override;

    static bool classof(const InstrumentationSite *is) {
      return is->getKind() == InstrumentationSite::Kind::AllocInst;
    }

 private:
    llvm::Instruction *allocInst_;
    ObjectMap::ObjID allocObj_;
};
//}}}

// Used to represent a free=alloc assumption made by the DynPtsto assumptions
class DoubleAllocInst : public AllocInst {  //{{{
 public:
    DoubleAllocInst(llvm::Instruction *alloc_inst, ObjectMap::ObjID alloc_obj) :
      AllocInst(alloc_inst, alloc_obj) { }

    int64_t approxCost() override {
      return 2 * AllocInst::approxCost();
    }

    bool doInstrument(llvm::Module &) override {
      llvm_unreachable("Shouldn't try to instrument a double alloc");
    }
};
//}}}

class FreeInst : public InstrumentationSite {  //{{{
 public:
    explicit FreeInst(llvm::Instruction *free_inst) :
      InstrumentationSite(InstrumentationSite::Kind::FreeInst),
      freeInst_(free_inst) { }

    bool operator<(const InstrumentationSite &is) const override {
      if (getKind() != is.getKind()) {
        return getKind() < is.getKind();
      }

      auto &fi = cast<FreeInst>(is);

      return freeInst_ < fi.freeInst_;
    }

    int64_t approxCost() override {
      return 1;
    }

    bool doInstrument(llvm::Module &m) override;

    static bool classof(const InstrumentationSite *is) {
      return is->getKind() == InstrumentationSite::Kind::FreeInst;
    }

 private:
    llvm::Instruction *freeInst_;
};
//}}}

// Checks a ptsto set when a pointer is assigned
class AssignmentInst : public InstrumentationSite {  //{{{
 public:
    AssignmentInst(llvm::Instruction *assign_inst,
        ObjectMap::ObjID assign_val) :
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

    int64_t approxCost() override {
      return 1;
    }

    bool doInstrument(llvm::Module &m) override;

    static bool classof(const InstrumentationSite *is) {
      return is->getKind() == InstrumentationSite::Kind::AssignmentInst;
    }

 private:
    llvm::Instruction *assignInst_;
    ObjectMap::ObjID assignVal_;
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

    int64_t approxCost() override {
      return 1;
    }

    bool doInstrument(llvm::Module &m) override;

    static bool classof(const InstrumentationSite *is) {
      return is->getKind() == InstrumentationSite::Kind::VisitInst;
    }

 private:
    llvm::BasicBlock *bb_;
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

    Kind getKind() const {
      return kind_;
    }

    static bool classof(const Assumption *) {
      return true;
    }

    std::vector<std::unique_ptr<InstrumentationSite>> getInstrumentation(
        const ObjectMap &obj, llvm::Module &m,
        const free_location_multimap &free_locations) const {
      return calcDependencies(obj, m, free_locations);
    }

    int64_t estimateCost(const ObjectMap &omap, const llvm::Module &m) {
      int64_t approx_cost = 0;

      for (auto &pinst : approxDependencies(omap, m)) {
        // FIXME: only do this for costs we haven't already taken?
        approx_cost += pinst->approxCost();
      }

      return approx_cost;
    }

 private:
    Assumption::Kind kind_;

 protected:
    explicit Assumption(Assumption::Kind kind) : kind_(kind) { }

    // Considers what would have to be instrumented to make this assumption
    // NOTE: We may need a ptsto analysis to know the real dependencies
    virtual std::vector<std::unique_ptr<InstrumentationSite>>
      approxDependencies(
        const ObjectMap &omap, const llvm::Module &m) const = 0;

    // For some forms of instrumentation we'll need to know the ptsto set to
    //   calc the true dependencies
    virtual std::vector<std::unique_ptr<InstrumentationSite>> calcDependencies(
        const ObjectMap &omap, llvm::Module &m,
        const free_location_multimap &free_locations) const = 0;
};
//}}}

class PtstoAssumption : public Assumption {  //{{{
 public:
    PtstoAssumption(ObjectMap::ObjID val_id,
        const std::set<ObjectMap::ObjID> &ptstos) :
          Assumption(Assumption::Kind::DynPtsto),
          objID_(val_id), ptstos_(ptstos) { }


    static bool classof(const Assumption *a) {
      return a->getKind() == Assumption::Kind::DynPtsto;
    }

 private:
    ObjectMap::ObjID objID_;
    std::set<ObjectMap::ObjID> ptstos_;

 protected:
    std::vector<std::unique_ptr<InstrumentationSite>>
      calcDependencies(
        const ObjectMap &omap, llvm::Module &m,
        const free_location_multimap &free_locations) const override;

    // To approx dependencies we make 2 alloc dependencies, and one inst
    // dependency.. we assume the cost of allow ~= the cost of free
    std::vector<std::unique_ptr<InstrumentationSite>>
      approxDependencies(
        const ObjectMap &omap, const llvm::Module &m) const override;
};
//}}}

class DeadCodeAssumption : public Assumption {  //{{{
 public:
    explicit DeadCodeAssumption(llvm::BasicBlock *bb) :
      Assumption(Assumption::Kind::DeadCode), bb_(bb) { }

    static bool classof(const Assumption *a) {
      return a->getKind() == Assumption::Kind::DeadCode;
    }

 private:
    llvm::BasicBlock *bb_;

 protected:
    std::vector<std::unique_ptr<InstrumentationSite>>
      calcDependencies(
        const ObjectMap &obj, llvm::Module &m,
        const free_location_multimap &free_locations) const override;

    // Approx dependencies == calcDependencies in this instance
    std::vector<std::unique_ptr<InstrumentationSite>> approxDependencies(
        const ObjectMap &obj, const llvm::Module &m) const override;
};
//}}}
//}}}

#endif  // INCLUDE_ASSUMPTIONS_H_
