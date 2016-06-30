/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/lib/BasicFcnCFG.h"

#include "include/lib/CallDests.h"
#include "include/Tarjans.h"
#include "include/LLVMHelper.h"


// Add Function CFG stuff here
// Get callsite info...
// Etc...

BasicFcnCFG::BasicFcnCFG(llvm::Module &m, DynamicInfo &di) {
  auto &dyn_info = di.used_info;
  // Populate our SEG to contain all of the functions as nodes
  // Step one, add a node for each function
  for (auto &fcn : m) {
    if (!dyn_info.isUsed(fcn)) {
      continue;
    }
    auto node_id = fcnGraph_.addNode<FcnNode>(&fcn);
    fcnMap_.emplace(&fcn, node_id);
  }

  // Add edges for all of the callsites
  for (auto &fcn : m) {
    if (!dyn_info.isUsed(fcn)) {
      continue;
    }

    auto fcn_id = fcnMap_.at(&fcn);
    for (auto &bb : fcn) {
      if (!dyn_info.isUsed(bb)) {
        continue;
      }

      for (auto &inst : bb) {
        auto pinst = &inst;

        if (auto ci = dyn_cast<llvm::CallInst>(pinst)) {
          llvm::ImmutableCallSite cs(ci);

          // Only consider direct calls...
          auto pdest_fcn = LLVMHelper::getFcnFromCall(cs);

          if (pdest_fcn != nullptr) {
            assert(dyn_info.isUsed(pdest_fcn));
            /*
            llvm::dbgs() << "ci is: " << ValPrinter(ci) << "\n";
            llvm::dbgs() << "fcn is: " << ValPrinter(pdest_fcn) << "\n";
            */
            auto dest_id = fcnMap_.at(pdest_fcn);
            fcnGraph_.addPred(dest_id, fcn_id);
          }
        } else if (auto ii = dyn_cast<llvm::InvokeInst>(pinst)) {
          llvm::dbgs() << "Unexpected invoke inst: " << *ii << "\n";
          llvm_unreachable("I don't support invokes!");
        }
      }
    }
  }

  // Calculate SCC
  {
    RunTarjans<> X(fcnGraph_);
  }
}

