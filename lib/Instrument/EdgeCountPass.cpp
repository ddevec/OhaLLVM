/*
 * Copyright (C) 2016 David Devecsery
 */

#include "include/lib/EdgeCountPass.h"

#include <algorithm>
#include <iostream>
#include <limits>
#include <set>
#include <string>
#include <sstream>
#include <vector>

#include "include/util.h"
#include "include/LLVMHelper.h"
#include "include/lib/CallDests.h"
#include "include/lib/CsCFG.h"
#include "include/lib/ExitInst.h"
#include "include/lib/UnusedFunctions.h"
#include "include/lib/IndirFcnTarget.h"

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

static llvm::cl::opt<std::string>
  DynEdgeFilename("dyn-edge-file", llvm::cl::init("profile.edge"),
      llvm::cl::value_desc("filename"),
      llvm::cl::desc("Edge file saved/loaded by EdgeCountPass analysis"));

static const std::string InitInstName = "__DynEdge_do_init";
static const std::string FinishInstName = "__DynEdge_do_finish";

static const std::string VisitInstName = "__DynEdge_do_visit";

class DynEdgeInst : public llvm::ModulePass {
 public:
  static char ID;
  DynEdgeInst();

  virtual bool runOnModule(llvm::Module &m);

  void getAnalysisUsage(llvm::AnalysisUsage &usage) const;

  llvm::StringRef getPassName() const override {
    return "DynEdgeInst";
  }

 private:
  llvm::Function *getInitFcn(llvm::Module &m);
  llvm::Function *getFinishFcn(llvm::Module &m);
  llvm::Function *getVisitFcn(llvm::Module &m);

  void setupTypes(llvm::Module &m);
  void addInitFunctions(llvm::Module &m);
  void callVisit(llvm::Module &m, llvm::BasicBlock *bb);

  std::unordered_map<const llvm::BasicBlock *, int32_t> bbToId_;

  llvm::Type *voidType_;
  llvm::Type *int32Type_;

  llvm::Function *initFcn_ = nullptr;
  llvm::Function *finishFcn_ = nullptr;
  llvm::Function *visitFcn_ = nullptr;
};

static void populateBBMap(llvm::Module &m,
    std::unordered_map<const llvm::BasicBlock *, int32_t> &bb_to_id) {
  int32_t id = 0;
  for (auto &fcn : m) {
    for (auto &bb : fcn) {
      bb_to_id[&bb] = id;
      assert(id != std::numeric_limits<int32_t>::max());
      id++;
    }
  }
}

char DynEdgeInst::ID = 0;
DynEdgeInst::DynEdgeInst() : llvm::ModulePass(ID) { }

namespace llvm {
static RegisterPass<DynEdgeInst> fX("spec-edge-profiling",
    "Instruments callsites, for use with speculative analyses",
    false, false);
}  // namespace llvm

void DynEdgeInst::getAnalysisUsage(llvm::AnalysisUsage &) const {
  // We don't need no stinkin analysis
}

void DynEdgeInst::setupTypes(llvm::Module &m) {
  int32Type_ = llvm::IntegerType::get(m.getContext(), 32);
  voidType_ = llvm::Type::getVoidTy(m.getContext());
}

llvm::Function *DynEdgeInst::getInitFcn(llvm::Module &m) {
  if (initFcn_ == nullptr) {
    std::vector<llvm::Type *> init_args = { };
    auto fcn_type = llvm::FunctionType::get(
        voidType_,
        init_args,
        false);
    initFcn_ = llvm::Function::Create(fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        InitInstName, &m);
  }
  return initFcn_;
}

llvm::Function *DynEdgeInst::getFinishFcn(llvm::Module &m) {
  if (finishFcn_ == nullptr) {
    std::vector<llvm::Type *> finish_args = { };
    auto fcn_type = llvm::FunctionType::get(
        voidType_,
        finish_args,
        false);
    finishFcn_ = llvm::Function::Create(fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        FinishInstName, &m);
  }
  return finishFcn_;
}

llvm::Function *DynEdgeInst::getVisitFcn(llvm::Module &m) {
  if (visitFcn_ == nullptr) {
    std::vector<llvm::Type *> visit_args = { int32Type_ };
    auto fcn_type = llvm::FunctionType::get(
        voidType_,
        visit_args,
        false);
    visitFcn_ = llvm::Function::Create(fcn_type,
        llvm::GlobalValue::ExternalLinkage,
        VisitInstName, &m);
  }
  return visitFcn_;
}

void DynEdgeInst::addInitFunctions(llvm::Module &m) {
  LLVMHelper::callAtEntry(m, getInitFcn(m), { });
  // LLVMHelper::callAtExit(m, getFinishFcn(m));
}

void DynEdgeInst::callVisit(llvm::Module &m, llvm::BasicBlock *bb) {
  std::vector<llvm::Value *> args =
      { llvm::ConstantInt::get(int32Type_, bbToId_.at(bb)) };

  auto insert_pos = bb->getFirstNonPHIOrDbg();

  // Insert here...
  auto visit_fcn = getVisitFcn(m);

  llvm::CallInst::Create(visit_fcn, args, "", insert_pos);
}


bool DynEdgeInst::runOnModule(llvm::Module &m) {
  setupTypes(m);

  populateBBMap(m, bbToId_);

  addInitFunctions(m);

  // Now, iterate all bbs:
  for (auto &fcn : m) {
    for (auto &bb : fcn) {
      callVisit(m, &bb);
    }
  }

  // Make sure to detect all exit conditions
  ExitInst ei(m, getFinishFcn(m));
  ei.addShims();

  return true;
}

char DynEdgeLoader::ID = 0;
DynEdgeLoader::DynEdgeLoader() : llvm::ModulePass(ID) { }

namespace llvm {
static RegisterPass<DynEdgeLoader> gX("spec-edge-loader",
    "Loads instrumented callsites, for use with speculative analyses",
    false, false);
}  // namespace llvm

void DynEdgeLoader::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  // We don't need no stinkin analysis
  usage.setPreservesAll();
}

bool DynEdgeLoader::runOnModule(llvm::Module &m) {
  std::unordered_map<const llvm::BasicBlock *, int32_t> bb_map;
  populateBBMap(m, bb_map);

  // id to count
  std::vector<size_t> raw_data(bb_map.size(), 0);

  // Load the datafile
  std::ifstream logfile(DynEdgeFilename, std::ifstream::in);
  // If we actually managed to get data...
  if (logfile.good()) {
    llvm::dbgs() << "DynEdgeLoader: Successfully Loaded!\n";

    // Then, load the lines of callstacks
    for (std::string line; std::getline(logfile, line); ) {
      std::stringstream converter(line);

      int32_t id;
      int32_t count;

      // Pump converter into id and count
      converter >> id;
      converter >> count;

      // += so we can handle files merged w/ cats
      raw_data[id] += count;

      loaded_ = true;
    }

    // Now, index the data
    for (auto &pr : bb_map) {
      auto bb = pr.first;
      auto id = pr.second;
      auto count = raw_data[id];

      // Make mapping of bb to count
      executionCounts_[bb] = count;
    }
  } else {
    llvm::dbgs() << "DynEdgeLoader: no logfile loaded!\n";
  }

  // We don't modify m, ever
  return false;
}


