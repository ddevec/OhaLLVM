/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/lib/FcnCFG.h"

#include "include/lib/CallDests.h"
#include "include/Tarjans.h"
#include "include/LLVMHelper.h"


// Add Function CFG stuff here
// Get callsite info...
// Etc...

/*
void addNodePreds(SEG &seg,
    const NodeMap &nmap,
    const FunctionCallInfo &call_info) {
  auto &callsite_to_fcn = call_info.getCallsiteToFcn();
  // For each callee in this function, add a pred to the SEG
  for (auto pci : callees_) {
    auto fcn_it = callsite_to_fcn.find(pci);
    if (fcn_it != std::end(callsite_to_fcn)) {
      for (auto vfcn : fcn_it->second) {
        auto fcn = cast<llvm::Function>(vfcn);
        // No edges for external functions :(
        if (!fcn->isDeclaration()) {
          // Add a pred from them to me
          seg.addPred(nmap.at(fcn), SEG::Node::id());
        }
      }
    }
  }
}
*/

char FcnCFG::ID = 0;
FcnCFG::FcnCFG() : llvm::ModulePass(ID) { }

namespace llvm {
static RegisterPass<FcnCFG> cX("FcnCFG",
    "Adds Control Flow Graph tracing for functions",
    false, false);
}  // namespace llvm

void FcnCFG::getAnalysisUsage(llvm::AnalysisUsage &usage) const {
  // Analysis that handles indirect function targets...
  usage.addRequired<CallDests>();

  // Unused Function Info
  usage.addRequired<UnusedFunctions>();

  // EOM
  usage.setPreservesAll();
}

bool FcnCFG::runOnModule(llvm::Module &m) {
  auto &call_info = getAnalysis<CallDests>();
  auto &dyn_info = getAnalysis<UnusedFunctions>();
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

          auto dests = call_info.getDests(cs);

          for (auto pdest_fcn : dests) {
            // This used to be an assert -- but due to the insanity of signals
            //   messing with things in redis, this isn't necessarily true
            if (dyn_info.isUsed(pdest_fcn)) {
              /*
              llvm::dbgs() << "ci is: " << ValPrinter(ci) << "\n";
              llvm::dbgs() << "fcn is: " << ValPrinter(pdest_fcn) << "\n";
              */
              auto dest_id = fcnMap_.at(pdest_fcn);
              fcnGraph_.addPred(dest_id, fcn_id);
            }
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

  // Done
  return false;
}

