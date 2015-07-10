/*
 * Copyright (C) 2015 David Devecsery
 *
 * NOTE: Components stolen from Andersens.cpp
 */

#include <cassert>
#include <cstdint>

#include <algorithm>
#include <functional>
#include <map>
#include <set>
#include <utility>
#include <vector>

#include "include/SpecSFS.h"

#define SPECSFS_DEBUG
#include "include/Debug.h"

#include "llvm/Constants.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Module.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm; // NOLINT

// Private namespace for file-local info {{{
namespace {

// Debugging functions {{{
if_debug(
  static void smart_print(const llvm::Value *val) {
    if (auto GV = dyn_cast<GlobalValue>(val)) {
      dout << GV->getName();
    } else {
      dout << *val;
    }
  }
)
//}}}

// Using AUX with CFG helpers {{{
// ID to keep track of anders return values
struct aux_id { };
typedef ID<aux_id, int32_t, -1> AuxID;

static void identifyAUXFcnCallRetInfo(DUG &graph, const ObjectMap &omap,
    const Andersens &aux) {

  // The mapping of andersen's values to functions
  std::map<AuxID, DUG::ObjID> anders_to_fcn;

  std::for_each(omap.functions_cbegin(), omap.functions_cend(),
      [&anders_to_fcn, &aux]
      (const std::pair<DUG::ObjID, const llvm::Value *> &pair) {
    anders_to_fcn[AuxID(aux.obj(pair.second))] = pair.first;
  });

  if_debug(
    dout << "Got ids for functions:";
    for (auto pr : anders_to_fcn) {
      dout << " {";
      auto val = omap.valueAtID(pr.second);
      smart_print(val);
      dout << ", " << pr.first << "}";
    }
    dout << "\n");

  // We iterate each indirect call in the DUG
  // to add the indirect info to the constraint map:
  std::for_each(graph.indirect_cbegin(), graph.indirect_cend(),
      // We take different arguments, depending on if we're debugging...
      [&graph, &aux, &anders_to_fcn, &omap]
      (const std::pair<DUG::ObjID, DUG::CFGid> &pair) {
    const llvm::CallInst *ci =
      cast<llvm::CallInst>(omap.valueAtID(pair.first));

    llvm::CallSite CS(const_cast<llvm::CallInst *>(ci));

    auto fptr = CS.getCalledValue();

    // This is the andersen's node for this element
    auto ptsto = aux.getPointsTo(fptr);

    if_debug(
      dout << "have ptsto:";
      for (auto aid : ptsto) {
        dout << " " << aid;
      }
      dout << "\n");

    DUG::CFGid call_id = graph.getCFGid();
    DUG::CFGid ret_id = graph.getCFGid();

    for (auto anders_int_id : ptsto) {
      AuxID anders_id(anders_int_id);

      DUG::ObjID fcn_id = anders_to_fcn.at(anders_id);

      // Add edge from call->fcn start node
      graph.addCFGEdge(call_id, graph.getCFGFunctionStart(fcn_id));
      // Add edge from fcn ret node->ret
      graph.addCFGEdge(graph.getCFGFunctionReturn(fcn_id), ret_id);
    }

    graph.addCFGCallRetInfo(omap.getValue(fptr), call_id, ret_id);
  });
}


//}}}

// Functions/Variables helping me track internal values {{{
int32_t CallReturnPos = 1;
int32_t CallFirstArgPos = 2;

ObjectMap::ObjID getValueReturn(const ObjectMap &omap, const Value *v) {
  return ObjectMap::getOffsID(omap.getValue(v), CallReturnPos);
}

ObjectMap::ObjID getValueUpdate(DUG &graph, ObjectMap &omap, const Value *v) {
  auto id = omap.getValue(v);

  graph.associateNode(id, v);

  return id;
}
//}}}

// Helpers for dealing with adding CFG constraints {{{
void addCFGLoad(DUG &graph, DUG::CFGid load_id, DUG::ObjID dest) {
  auto &node = graph.getCFGNode(load_id);

  // Set this as an important or "r" node
  node.setR();
  graph.addUse(load_id, dest);
}

void addCFGStore(DUG &graph, DUG::CFGid *store_id, DUG::ObjID dest) {
  // Well, stuff here

  auto &node = graph.getCFGNode(*store_id);

  // If this is a p-node, then there are no stores in it, and we can share it
  // with laods
  if (node.p()) {
    node.setM();
  // If this is a m-node (np-node), then it has a store, and we need to make a
  // new node
  } else {
    DUG::CFGid next_id = graph.getCFGid();

    graph.addCFGEdge(*store_id, next_id);

    // Advance the id
    *store_id = next_id;
  }

  graph.addDef(*store_id, dest);
}

void addCFGCallsite(DUG &graph, const ObjectMap &omap,
    llvm::Function *fcn, llvm::Instruction *ci, DUG::CFGid *pcall_id) {

  // Add a new node into the graph
  DUG::CFGid call_id = *pcall_id;
  DUG::CFGid next_id = graph.getCFGid();
  *pcall_id = next_id;

  if (fcn) {
    // We don't add edges now because we haven't identified the entry and return
    //   CFGid's for all functions yet
    // We also use a getObject(F) because functions are all associated with
    // objects, only some are associated with values
    graph.addCFGCallsite(call_id, omap.getObject(fcn), next_id);
  } else {
    // We also don't add edges between the call_id and the callsite for indirect
    //    calls because we don't know the destination until we run our AUX
    //    analysis.
    // All call instructions are associated with values, so we use getValue here
    graph.addCFGIndirectCall(call_id, omap.getValue(ci), next_id);
  }
}
//}}}

// Functions dealing with identifying known external functions {{{
static bool isMalloc(const Value *V) {
  const CallInst *CI = dyn_cast<CallInst>(V);
  if (!CI)
    return false;

  Function *Callee = CI->getCalledFunction();
  if (Callee == 0 || !Callee->isDeclaration())
    return false;
  if (Callee->getName() != "malloc" &&
      Callee->getName() != "calloc" &&
      Callee->getName() != "valloc" &&
      Callee->getName() != "realloc" &&
      Callee->getName() != "memalign" &&
      Callee->getName() != "fopen" &&
      Callee->getName() != "_Znwj" &&  // operator new(unsigned int)
      Callee->getName() != "_Znwm" &&  // operator new(unsigned long)
      Callee->getName() != "_Znaj" &&  // operator new[](unsigned int)
      Callee->getName() != "_Znam")    // operator new[](unsigned long)
    return false;

  // ddevec - TODO: check prototype
  return true;
}

// NOTE: Copy/pasted shamelessly from Andersens.cpp
static bool addConstraintsForExternalCall(DUG &graph, ObjectMap &omap,
    CallSite &CS, Function *F, DUG::CFGid *next_id) {
  assert(F->isDeclaration() && "Not an external call!");

  // These functions don't induce any points-to constraints.
  if (F->getName() == "atoi" || F->getName() == "atof" ||
      F->getName() == "atol" || F->getName() == "atoll" ||
      F->getName() == "remove" || F->getName() == "unlink" ||
      F->getName() == "rename" || F->getName() == "memcmp" ||
      F->getName() == "llvm.memset" ||
      F->getName() == "strcmp" || F->getName() == "strncmp" ||
      F->getName() == "execl" || F->getName() == "execlp" ||
      F->getName() == "execle" || F->getName() == "execv" ||
      F->getName() == "execvp" || F->getName() == "chmod" ||
      F->getName() == "puts" || F->getName() == "write" ||
      F->getName() == "open" || F->getName() == "create" ||
      F->getName() == "truncate" || F->getName() == "chdir" ||
      F->getName() == "mkdir" || F->getName() == "rmdir" ||
      F->getName() == "read" || F->getName() == "pipe" ||
      F->getName() == "wait" || F->getName() == "time" ||
      F->getName() == "stat" || F->getName() == "fstat" ||
      F->getName() == "lstat" || F->getName() == "strtod" ||
      F->getName() == "strtof" || F->getName() == "strtold" ||
      F->getName() == "fopen" || F->getName() == "fdopen" ||
      F->getName() == "fflush" || F->getName() == "feof" ||
      F->getName() == "fileno" || F->getName() == "clearerr" ||
      F->getName() == "rewind" || F->getName() == "ftell" ||
      F->getName() == "ferror" || F->getName() == "fgetc" ||
      F->getName() == "fgetc" || F->getName() == "_IO_getc" ||
      F->getName() == "fwrite" || F->getName() == "fread" ||
      F->getName() == "fgets" || F->getName() == "ungetc" ||
      F->getName() == "fputc" ||
      F->getName() == "fputs" || F->getName() == "putc" ||
      F->getName() == "ftell" || F->getName() == "rewind" ||
      F->getName() == "_IO_putc" || F->getName() == "fseek" ||
      F->getName() == "fgetpos" || F->getName() == "fsetpos" ||
      F->getName() == "printf" || F->getName() == "fprintf" ||
      F->getName() == "sprintf" || F->getName() == "vprintf" ||
      F->getName() == "vfprintf" || F->getName() == "vsprintf" ||
      F->getName() == "scanf" || F->getName() == "fscanf" ||
      F->getName() == "sscanf" || F->getName() == "__assert_fail" ||
      F->getName() == "modf") {
    return true;
  }

  // These functions do induce points-to edges.
  if (F->getName().find("llvm.memcpy") == 0 ||
      F->getName().find("llvm.memmove") == 0 ||
      F->getName().find("memmove") == 0) {
    const FunctionType *FTy = F->getFunctionType();

    if (FTy->getNumParams() > 1 &&
        isa<PointerType>(FTy->getParamType(0)) &&
        isa<PointerType>(FTy->getParamType(1))) {
      // *Dest = *Src, which requires an artificial graph node to
      // represent the constraint.
      // It is broken up into *Dest = temp, temp = *Src
      auto FirstArg = omap.getValue(CS.getArgument(0));
      auto SecondArg = omap.getValue(CS.getArgument(1));
      // Creates a new node in the graph, and a temp holder in omap
      auto TempArg = graph.addNode(omap);

      // Setup constraints
      graph.add(Constraint::Type::Store, FirstArg, TempArg);
      graph.add(Constraint::Type::Load, TempArg, SecondArg);
      graph.add(Constraint::Type::Copy, FirstArg, SecondArg);

      // Setup CFG
      // First setup the load
      addCFGLoad(graph, *next_id, omap.getValue(CS.getArgument(1)));
      // Then setup the store
      addCFGStore(graph, next_id, omap.getValue(CS.getArgument(0)));

      return true;
    }
  }

  // Result = Arg0
  if (F->getName() == "realloc" || F->getName() == "strchr" ||
      F->getName() == "strrchr" || F->getName() == "strstr" ||
      F->getName() == "strtok"  || F->getName() == "stpcpy" ||
      F->getName() == "getcwd"  || F->getName() == "strcat" ||
      F->getName() == "strcpy") {
    const FunctionType *FTy = F->getFunctionType();
    if (FTy->getNumParams() > 0 &&
        isa<PointerType>(FTy->getParamType(0))) {
      graph.add(Constraint::Type::Copy, omap.getValue(CS.getInstruction()),
          omap.getValue(CS.getArgument(0)));
      return true;
    }
  }

  if (F->getName() == "realpath") {
    const FunctionType *FTy = F->getFunctionType();
    if (FTy->getNumParams() > 0 &&
        isa<PointerType>(FTy->getParamType(1))) {
      graph.add(Constraint::Type::Copy, omap.getValue(CS.getInstruction()),
          omap.getValue(CS.getArgument(1)));
      return true;
    }
  }

  if (F->getName() == "freopen") {
    const FunctionType *FTy = F->getFunctionType();
    if (FTy->getNumParams() > 0 &&
        isa<PointerType>(FTy->getParamType(2))) {
      graph.add(Constraint::Type::Copy, omap.getValue(CS.getInstruction()),
          omap.getValue(CS.getArgument(2)));
      return true;
    }
  }

  Instruction *I = CS.getInstruction();
  if (I) {
    Function *ParentF = I->getParent()->getParent();
    if (IntrinsicInst *II = dyn_cast<IntrinsicInst>(I)) {
      Intrinsic::ID IID = II->getIntrinsicID();
      if (IID == Intrinsic::vastart) {
        assert(ParentF->getFunctionType()->isVarArg()
            && "va_start in non-vararg function!");
        Value *Arg = II->getArgOperand(0);
        auto TempArg = graph.addNode(omap);
        graph.add(Constraint::Type::AddressOf, TempArg,
            omap.getVarArg(ParentF));
        graph.add(Constraint::Type::Store, omap.getValue(Arg),
            TempArg);
        addCFGStore(graph, next_id, omap.getValue(Arg));
        return true;
      } else if (IID == Intrinsic::vaend) {
        return true;
      }
    }
  }

  if (F->getName() == "pthread_create") {
    const FunctionType *FTy = F->getFunctionType();
    if (FTy->getNumParams() == 4
        && isa<PointerType>(FTy->getParamType(0))
        && isa<PointerType>(FTy->getParamType(1))
        && isa<PointerType>(FTy->getParamType(2))
        && isa<PointerType>(FTy->getParamType(3))) {
      // Copy the actual argument into the formal argument.
      Value *ThrFunc = I->getOperand(2);
      Value *Arg = I->getOperand(3);
      graph.add(Constraint::Type::Store, omap.getValue(ThrFunc),
          omap.getValue(Arg), CallFirstArgPos);
      addCFGStore(graph, next_id,
          omap.getOffsID(omap.getValue(Arg), CallFirstArgPos));
      return true;
    }
  }

  if (F->getName() == "pthread_getspecific") {
    const FunctionType *FTy = F->getFunctionType();
    if (FTy->getNumParams() == 1 && isa<PointerType>(FTy->getReturnType())) {
      graph.add(Constraint::Type::Store, omap.getValue(CS.getInstruction()),
          ObjectMap::PthreadSpecificValue);
      addCFGStore(graph, next_id, ObjectMap::PthreadSpecificValue);
      return true;
    }
  } else if (F->getName() == "pthread_setspecific") {
    const FunctionType *FTy = F->getFunctionType();
    if (FTy->getNumParams() == 2 && isa<PointerType>(FTy->getParamType(1))) {
      graph.add(Constraint::Type::Copy, ObjectMap::PthreadSpecificValue,
          omap.getValue(CS.getInstruction()->getOperand(1)));
      return true;
    }
  }

  return false;
}
//}}}

// Constraint helpers {{{
static void addGlobalInitializerConstraints(DUG &graph, ObjectMap &omap,
    ObjectMap::ObjID id, const Constant *C) {
  // Simple case, single initializer
  if (C->getType()->isSingleValueType()) {
    if (isa<PointerType>(C->getType())) {
      graph.add(Constraint::Type::Copy, id,
          omap.getConstValue(C));
    }

  // Initialized to null value
  } else if (C->isNullValue()) {
    graph.add(Constraint::Type::Copy, id, ObjectMap::NullValue);

  // Set to some other defined value
  } else if (!isa<UndefValue>(C)) {
    // It must be an array, or struct
    assert(isa<ConstantArray>(C) || isa<ConstantStruct>(C) ||
        isa<ConstantDataSequential>(C));

    // For each field of the initializer, add a constraint for the field
    std::for_each(C->op_begin(), C->op_end(),
        [&graph, &omap, id, C] (const Value *op) {
      addGlobalInitializerConstraints(graph, omap, id,
        cast<Constant>(op));
    });
  }
}

/*
static void addGlobalInitializerConstraints(DUG &graph, ObjectMap &omap,
    ObjectMap::ObjID id, const Value *V) {
  addGlobalInitializerConstraints(graph, omap, id, cast<const Constant>(V));
}
*/

static void addConstraintForConstPtr(DUG &graph, ObjectMap &omap,
    const GlobalValue &glbl) {
  bool inserted = false;
  // NOTE: We don't use a std::for_each here b/c we need to break
  for (auto I = glbl.use_begin(), E = glbl.use_end(); I != E; ++I) {
    auto use = *I;

    // If this use is a constant expr, we can add the constraint now
    if (auto *CE = dyn_cast<const ConstantExpr>(use)) {
      // If its a ptr to int, add an "intvalue"
      if (CE->getOpcode() == Instruction::PtrToInt) {
        if (!inserted) {
          graph.add(Constraint::Type::Copy, ObjectMap::IntValue,
            omap.getValue(&glbl));

          inserted = true;
        }

        // The intvalue constraint will essentially set this to global set,
        // so we don't need to process more
        break;
      }
    }
  }
}

// Look at the uses of this function, if they are "complex" like address
// escapes, return true
static bool analyzeUsesOfFunction(const Value &val) {
  if (!isa<PointerType>(val.getType())) {
    return true;
  }

  for (auto UI = val.use_begin(), UE = val.use_end(); UI != UE; ++UI) {
    if (isa<LoadInst>(*UI)) {
      return false;
    } else if (auto SI = dyn_cast<StoreInst>(*UI)) {
      if (&val == SI->getOperand(1)) {
        return false;

      // This pointer is being stored
      } else if (SI->getOperand(1)) {
        return true;
      }
    } else if (auto GEP = dyn_cast<GetElementPtrInst>(*UI)) {
      if (analyzeUsesOfFunction(*GEP)) {
        return true;
      }
    } else if (auto CI = dyn_cast<CallInst>(*UI)) {
      CallSite CS((CallInst *)CI);
      // Can't use std::for_each because of return
      for (size_t i = 0, e = CS.arg_size(); i < e; i++) {
        if (CS.getArgument(i) == &val) {
          return true;
        }
      }
    } else if (auto CE = dyn_cast<ConstantExpr>(*UI)) {
      if (CE->getOpcode() == Instruction::GetElementPtr ||
          CE->getOpcode() == Instruction::BitCast) {
        if (analyzeUsesOfFunction(*CE)) {
          return true;
        }
      } else {
        return true;
      }
    } else if (dyn_cast<ICmpInst>(*UI) != nullptr) {
      return true;
    } else {
      return true;
    }
  }

  return false;
}

static void addConstraintsForNonInternalLinkage(DUG &graph, ObjectMap &omap,
    const Function &fcn) {
  std::for_each(fcn.arg_begin(), fcn.arg_end(),
      [&graph, &omap] (const Argument &arg) {
    if (isa<PointerType>(arg.getType())) {
      graph.add(Constraint::Type::Copy, omap.getValue(&arg),
        ObjectMap::UniversalValue);
    }
  });
}


static void addConstraintsForIndirectCall(DUG &graph, ObjectMap &omap,
    CallSite &CS) {
  auto &called_val = *CS.getCalledValue();

  if (isa<InlineAsm>(&called_val)) {
    errs() << "Ignoring inline asm!\n";
    return;
  }

  getValueUpdate(graph, omap, &called_val);


  // FIXME: This is sloppy?
  // We take care of adding the constriants to the map in addCFGCallsite, caleld
  //    from addConstraintsForCall() before this
}

static void addConstraintsForDirectCall(DUG &graph, ObjectMap &omap,
    CallSite &CS, Function *F) {
  auto &called_val = *CS.getCalledValue();

  // If this call returns a pointer
  if (isa<PointerType>(CS.getType())) {
    auto val = omap.getValue(CS.getInstruction());

    // If the function that's called also returns a pointer
    if (isa<PointerType>(F->getFunctionType()->getReturnType())) {
      // Add a copy from the return value into this value
      graph.add(Constraint::Type::Copy, val,
          omap.getValueReturn(&called_val));

    // The callsite returns a pointer, but the function returns a
    // non-pointer value, treat it as a non-pointer cast to a pointer
    } else {
      graph.add(Constraint::Type::Copy, val, ObjectMap::UniversalValue);
    }
  // The callsite returns a non-pointer, but the function returns a
  // pointer value, treat it as a pointer cast to a non-pointer
  } else if (F && isa<PointerType>(F->getFunctionType()->getReturnType())) {
    graph.add(Constraint::Type::Copy, omap.getValueReturn(&called_val),
        ObjectMap::UniversalValue);
  }

  auto ArgI = CS.arg_begin();
  auto ArgE = CS.arg_end();

  bool external = F->isDeclaration();

  auto FargI = F->arg_begin();
  auto FargE = F->arg_end();

  // For each arg
  for (; FargI != FargE && ArgI != ArgE; ++FargI, ++ArgI) {
    if (external && isa<PointerType>((*ArgI)->getType())) {
      dout << "Adding arg to universal value :(\n";
      graph.add(Constraint::Type::Copy, omap.getValue(*ArgI),
          ObjectMap::UniversalValue);
    }

    // If we expect a pointer type
    if (isa<PointerType>(FargI->getType())) {
      // And we get one!
      if (isa<PointerType>((*ArgI)->getType())) {
        dout << "Adding arg copy!\n";
        graph.add(Constraint::Type::Copy, omap.getValue(FargI),
            omap.getValue(*ArgI));
      // But if its not a pointer type...
      } else {
        // Map it to everything (i2p)
        dout << "Adding i2p universal value :(\n";
        graph.add(Constraint::Type::Copy, omap.getValue(FargI),
            ObjectMap::UniversalValue);
      }
    }
  }

  // Varargs magic :(
  if (F->getFunctionType()->isVarArg()) {
    for (; ArgI != ArgE; ++ArgI) {
      if (isa<PointerType>((*ArgI)->getType())) {
        graph.add(Constraint::Type::Copy, omap.getVarArg(F),
            omap.getValue(*ArgI));
      }
    }
  }
}

static bool addConstraintsForCall(DUG &graph, ObjectMap &omap,
    CallSite &CS, Function *F, DUG::CFGid *next_id) {
  // bool isIndirect = (F == NULL);

  // Try to recover the function from a bitcast (taken from sfs code)
  // If this function was just cast to a function pointer from the prior
  // instruction, this will determine so statically, and treat it as a direct
  // call
  if (!F) {
    Value *callee = CS.getInstruction()->getOperand(0);

    ConstantExpr *E = dyn_cast<ConstantExpr>(callee);
    if (E && E->getOpcode() == Instruction::BitCast) {
      F = dyn_cast<Function>(E->getOperand(0));
    }
  }

  // If this is direct && is external
  if (F && F->isDeclaration()) {
    // Add it as an external function
    if (addConstraintsForExternalCall(graph, omap, CS, F, next_id)) {
      // If This is an external call that I identified, then we don't add a node
      // for it constraints for it, because we've already added constriants for
      // its properties
      return false;
    }
  }

  // next_id will be nullptr when called to add this call's constraints from
  // SpecSFS::addIndirectCalls()  In that instance, we've already created
  // callsite nodes in the CFG, and shouldn't make more
  if (next_id != nullptr) {
    addCFGCallsite(graph, omap, F, CS.getInstruction(), next_id);
  }
  if (F) {
    addConstraintsForDirectCall(graph, omap, CS, F);
  } else {
    addConstraintsForIndirectCall(graph, omap, CS);
  }

  return true;
}
//}}}

// Helpers for individual instruction constraints {{{
static void idRetInst(DUG &graph, ObjectMap &omap, const Instruction &inst) {
  auto &ret = *cast<const ReturnInst>(&inst);

  // Returns without arguments (void) don't add constraints
  if (ret.getNumOperands() == 0) {
    return;
  }

  // Get the return value
  Value *src = ret.getOperand(0);

  // If its not a pointer, we don't care about it
  if (!isa<PointerType>(src->getType())) {
    return;
  }

  // The function in which ret was called
  const Function *F = ret.getParent()->getParent();

  graph.add(Constraint::Type::Copy,
      omap.getReturn(F), omap.getValue(src));
}

static bool idCallInst(DUG &graph, ObjectMap &omap, const Instruction &inst,
    DUG::CFGid *bb_id) {
  // Meh, Callsites don't take consts... bleh
  CallSite CS(const_cast<Instruction *>(&inst));

  if (isMalloc(&inst)) {
    graph.associateNode(omap.getObject(&inst), &inst);
    graph.add(Constraint::Type::AddressOf, getValueUpdate(graph, omap, &inst),
        omap.getObject(&inst));
  }

  if (isa<PointerType>(CS.getType())) {
    getValueUpdate(graph, omap, &inst);
  }

  return addConstraintsForCall(graph, omap, CS, CS.getCalledFunction(), bb_id);
}

static void idAllocaInst(DUG &graph, ObjectMap &omap,
    const Instruction &inst) {
  auto &alloc = *cast<const AllocaInst>(&inst);

  // Get the object associated with this allocation
  auto obj_id = omap.getObject(&alloc);

  // Associate that obj with this value
  graph.associateNode(obj_id, &alloc);

  // Add a constraint pointing this value to that object
  graph.add(Constraint::Type::AddressOf, getValueUpdate(graph, omap, &alloc),
      obj_id);
}

// FIXME -- Also handle pointer args going through here
//    (like in Andersens.cpp)
static void idLoadInst(DUG &graph, ObjectMap &omap, const Instruction &inst,
    DUG::CFGid next_id) {
  auto &ld = *cast<const LoadInst>(&inst);

  if (isa<PointerType>(ld.getType())) {
    graph.add(Constraint::Type::Load, getValueUpdate(graph, omap, &ld),
        omap.getValue(ld.getOperand(0)));

    // Add this to the uses
    addCFGLoad(graph, next_id, omap.getValue(&ld));
  } else if (isa<PointerType>(ld.getOperand(0)->getType()) &&
      isa<IntegerType>(ld.getType())) {
    errs() << "FIXME: Unhandled load info!\n";
  } else if (isa<StructType>(ld.getType())) {
    errs() << "FIXME: Unhandled struct load!\n";
  }
}

static void idStoreInst(DUG &graph, ObjectMap &omap,
    const Instruction &inst, DUG::CFGid *next_id) {
  auto &st = *cast<const StoreInst>(&inst);

  if (isa<PointerType>(st.getOperand(0)->getType())) {
    // Store from ptr
    graph.add(Constraint::Type::Store, omap.getValue(st.getOperand(1)),
        omap.getValue(st.getOperand(0)));
  } else if (ConstantExpr *ce = dyn_cast<ConstantExpr>(st.getOperand(0))) {
    // If we just cast a ptr to an int then stored it.. we can keep info on it
    if (ce->getOpcode() == Instruction::PtrToInt) {
      graph.add(Constraint::Type::Store, omap.getValue(st.getOperand(1)),
          omap.getValue(ce->getOperand(0)));
    // Uhh, dunno what to do now
    } else {
      errs() << "FIXME: Unhandled constexpr case!\n";
    }
  // put int value into the int pool
  } else if (isa<IntegerType>(st.getOperand(0)->getType()) &&
      isa<PointerType>(st.getOperand(1)->getType())) {
    graph.add(Constraint::Type::Store, omap.getValue(st.getOperand(1)),
        ObjectMap::IntValue);
  // Poop... structs
  } else if (isa<StructType>(st.getOperand(0)->getType())) {
    errs() << "FIXME: Ignoring struct store\n";
    /*
    graph.add(Constraint::Type::Store, omap.getValue(st.getOperand(1)),
        ObjectMap::AgregateNode);
        */
  }
  addCFGStore(graph, next_id, omap.getValue(st.getOperand(1)));
}

static void idGEPInst(DUG &graph, ObjectMap &omap, const Instruction &inst) {
  auto &gep = *cast<const GetElementPtrInst>(&inst);

  graph.add(Constraint::Type::Copy, getValueUpdate(graph, omap, &gep),
      omap.getValue(gep.getOperand(0)));
}

static void idI2PInst(DUG &graph, ObjectMap &omap, const Instruction &inst) {
  // ddevec - FIXME: Could trace through I2P here, by keeping a listing
  //    of i2ps...
  // sfs does this, Andersens doesn't.  I don't think its a sound approach, as
  // something external may modify any int reference passed to it (where we're
  // unaware of what's in it) and screw up our tracking
  // Instead I'm just going to go w/ the Andersen's, approach, give it an
  // int value
  graph.add(Constraint::Type::Copy, getValueUpdate(graph, omap, &inst),
      ObjectMap::IntValue);
}

static void idBitcastInst(DUG &graph, ObjectMap &omap,
    const Instruction &inst) {
  auto &bcast = *cast<const BitCastInst>(&inst);

  assert(isa<PointerType>(inst.getType()));

  auto id = getValueUpdate(graph, omap, &bcast);

  assert(isa<PointerType>(bcast.getOperand(0)->getType()));
  auto op = omap.getValue(bcast.getOperand(0));

  graph.add(Constraint::Type::Copy, id, op);
}

static void idPhiInst(DUG &graph, ObjectMap &omap, const Instruction &inst) {
  auto &phi = *cast<const PHINode>(&inst);

  assert(isa<PointerType>(phi.getType()));

  // hheheheheh PHI-d
  auto phid = getValueUpdate(graph, omap, &phi);

  for (size_t i = 0, e = phi.getNumIncomingValues(); i != e; ++i) {
    graph.add(Constraint::Type::Copy, phid,
        omap.getValue(phi.getIncomingValue(i)));
  }
}

static void idSelectInst(DUG &graph, ObjectMap &omap,
    const Instruction &inst) {
  auto &select = *cast<const SelectInst>(&inst);

  // this inst --> select: op(0) ? op(1) : op(2)

  if (isa<PointerType>(select.getType())) {
    auto sid = getValueUpdate(graph, omap, &select);

    graph.add(Constraint::Type::Copy, sid,
        omap.getValue(select.getOperand(1)));
    graph.add(Constraint::Type::Copy, sid,
        omap.getValue(select.getOperand(2)));

  } else if (isa<StructType>(select.getType())) {
    errs() << "Warning, unsupported select on struct!\n";
  }
}

static void idVAArgInst(DUG &, ObjectMap &,
    const Instruction &) {
  llvm_unreachable("Vaarg not handled yet");
}

static void idExtractInst(DUG &, ObjectMap &,
    const Instruction &) {
  llvm_unreachable("ExtractValue not handled yet");
}
//}}}

// Instruction parsing helpers {{{
static void processBlock(DUG &graph, std::set<const BasicBlock *> &seen,
    ObjectMap &omap, const BasicBlock &BB, DUG::CFGid parent_id) {
  // Make sure we don't follow the same block twice
  assert(seen.count(&BB) == 0);
  seen.insert(&BB);

  // Extract the basic block info about this block for our CFG (required for
  //    computing SSA on address-taken variables)
  // This is for the basic block, not a value, so it's "anon"
  DUG::CFGid next_id = graph.getCFGid();
  // Add an edge from our parent, if we have one
  if (parent_id.valid()) {
    graph.addCFGEdge(parent_id, next_id);
  // Or if we don't have a parent denote that we should get edges from calls
  } else {
    graph.addCFGFunctionStart(omap.getObject(BB.getParent()), next_id);
  }


  bool block_has_call = false;

  // Now, analyze each instruction, extract constraints
  for (auto &inst : BB) {
    bool is_ptr = isa<PointerType>(inst.getType());

    switch (inst.getOpcode()) {
      case Instruction::Ret:
        {
          assert(!is_ptr);

          // We add a "return node" for this block if there is a call within it
          if (block_has_call) {
            // Get a new "anon" cfg node for the ret node
            DUG::CFGid ret_id = graph.getCFGid();
            graph.addCFGEdge(next_id, ret_id);
            next_id = ret_id;
          // Otherwise, we consider the entry node as the return node
          }

          graph.addCFGFunctionReturn(omap.getObject(BB.getParent()), next_id);

          idRetInst(graph, omap, inst);
        }
        break;
      case Instruction::Invoke:
      case Instruction::Call:
        block_has_call |= idCallInst(graph, omap, inst, &next_id);
        break;
      case Instruction::Alloca:
        assert(is_ptr);
        idAllocaInst(graph, omap, inst);
        break;
      case Instruction::Load:
        idLoadInst(graph, omap, inst, next_id);
        break;
      case Instruction::Store:
        assert(!is_ptr);
        idStoreInst(graph, omap, inst, &next_id);
        break;
      case Instruction::GetElementPtr:
        assert(is_ptr);
        idGEPInst(graph, omap, inst);
        break;
      case Instruction::IntToPtr:
        assert(is_ptr);
        idI2PInst(graph, omap, inst);
        break;
      case Instruction::BitCast:
        if (is_ptr) {
          idBitcastInst(graph, omap, inst);
        }
        break;
      case Instruction::PHI:
        if (is_ptr) {
          idPhiInst(graph, omap, inst);
        }
        break;
      case Instruction::Select:
          idSelectInst(graph, omap, inst);
        break;
      case Instruction::VAArg:
        if (is_ptr) {
          idVAArgInst(graph, omap, inst);
        }
        break;
      case Instruction::ExtractValue:
        if (is_ptr) {
          idExtractInst(graph, omap, inst);
        }
        break;
      default:
        assert(!is_ptr && "Unknown instruction has a pointer return type!");
    }
  }

  // Process all of our successor blocks (In DFS order)
  std::for_each(succ_begin(&BB), succ_end(&BB),
      [&graph, &seen, &omap, next_id] (const BasicBlock *succBB) {
    if (!seen.count(succBB)) {
      processBlock(graph, seen, omap, *succBB, next_id);
    }
  });
}

void scanFcn(DUG &graph, ObjectMap &omap, const Function &fcn) {
  // SFS adds instructions to graph, we've already added them?
  //   So we don't need to worry about it
  // Add instructions to graph
  /*
  std::for_each(inst_begin(fcn), inst_end(fcn),
      [&graph, &omap] (const Instruction &inst) {
    if (isa<PointerType>(inst.getType())) {
      graph.addNode(&inst);
    }
  });
  */

  // Now create constraints in depth first order:
  std::set<const BasicBlock *> seen;
  for (auto &BB : fcn) {
    processBlock(graph, seen, omap, BB, DUG::CFGid::invalid());
  }
}
//}}}

}  // End private namespace
//}}}

bool SpecSFS::identifyObjects(ObjectMap &omap, const Module &M) {
  //{{{
  // Okay, we need to identify all possible objects within the module, then
  //   insert them into our object map

  // Id all globals
  std::for_each(M.global_begin(), M.global_end(), [&omap](const Value &glbl) {
    omap.addValue(&glbl);
    omap.addObject(&glbl);
  });

  // Functions are memory objects
  std::for_each(std::begin(M), std::end(M),
      [&omap](const Function &fcn) {
    omap.addObject(&fcn);
  });

  // Now add nodes for the functions, and all the operations within
  for (auto &fcn : M) {
    omap.addValueFunction(&fcn);

    // If this is a function which returns a pointer, we'll need a node for it
    if (isa<PointerType>(fcn.getFunctionType()->getReturnType())) {
      omap.addReturn(&fcn);
    }

    // If this is a vararg function... I've got problems!
    if (fcn.getFunctionType()->isVarArg()) {
      omap.addVarArg(&fcn);
    }

    // Args are also values...
    std::for_each(fcn.arg_begin(), fcn.arg_end(), [&omap](const Argument &arg) {
      if (isa<PointerType>(arg.getType())) {
        omap.addValue(&arg);
      }
    });

    // Each BB in each function gets an ObjID as an object
    std::for_each(std::begin(fcn), std::end(fcn),
        [&omap](const BasicBlock &bb) {
      omap.addObject(&bb);
    });

    // For each instruction:
    std::for_each(inst_begin(fcn), inst_end(fcn),
        [&omap](const Instruction &inst) {
      // Add pointer values
      if (isa<PointerType>(inst.getType())) {
        omap.addValue(&inst);
      }

      // Add alloc objects
      if (auto AI = dyn_cast<AllocaInst>(&inst)) {
        omap.addObject(AI);
      }

      if (isMalloc(&inst)) {
        omap.addObject(&inst);
      }
    });
  }

  return false;
  //}}}
}

bool SpecSFS::createConstraints(DUG &graph, ObjectMap &omap,
    const Module &M) {
  //{{{

  // Special Constraints {{{
  // First, we set up some constraints for our special constraints:
  // Universal value
  graph.add(Constraint::Type::AddressOf, ObjectMap::UniversalValue,
      ObjectMap::UniversalValue);
  graph.add(Constraint::Type::Store, ObjectMap::UniversalValue,
      ObjectMap::UniversalValue);

  // Null value pts to null object
  graph.add(Constraint::Type::AddressOf, ObjectMap::NullValue,
      ObjectMap::NullObjectValue);
  //}}}

  // Global Variables {{{
  // Okay, first create nodes for all global variables:
  std::for_each(M.global_begin(), M.global_end(),
      [&graph, &omap](const GlobalVariable &glbl) {
    // Associate the global address with a node:
    auto obj_id = omap.getObject(&glbl);
    graph.associateNode(obj_id, &glbl);

    // Create the constraint for the actual global
    graph.add(Constraint::Type::AddressOf, getValueUpdate(graph, omap, &glbl),
        obj_id);

    // If its a global w/ an initalizer
    if (glbl.hasDefinitiveInitializer()) {
      addGlobalInitializerConstraints(graph, omap, omap.getObject(&glbl),
        glbl.getInitializer());

      // If the global is a pointer constraint, it needs a const ptr
      //   (as it has an initializer)
      if (isa<PointerType>(glbl.getType())) {
        addConstraintForConstPtr(graph, omap, glbl);
      }

    // Doesn't have initializer
    } else {
      graph.add(Constraint::Type::Copy, omap.getObject(&glbl),
          ObjectMap::UniversalValue);
      graph.add(Constraint::Type::Copy, omap.getValue(&glbl),
          ObjectMap::UniversalValue);
    }
  });
  //}}}

  // Functions {{{
  // Now that we've dealt with globals, move on to functions
  for (auto &fcn : M) {
    auto obj_id = omap.getObject(&fcn);
    graph.associateNode(obj_id, &fcn);

    graph.add(Constraint::Type::AddressOf, getValueUpdate(graph, omap, &fcn),
        obj_id);

    // Functions are constant pointers
    addConstraintForConstPtr(graph, omap, fcn);
  }

  // Now we deal with the actual internals of functions
  for (auto &fcn : M) {
    // If we return a pointer
    if (isa<PointerType>(fcn.getFunctionType()->getReturnType())) {
      // Create a node for this fcn's return
      graph.associateNode(omap.getReturn(&fcn), &fcn);
    }
    // Set up our vararg node
    if (fcn.getFunctionType()->isVarArg()) {
      graph.associateNode(omap.getVarArg(&fcn), &fcn);
    }

    // Update the value for each arg
    std::for_each(fcn.arg_begin(), fcn.arg_end(),
        [&graph, &omap](const Argument &arg) {
      if (isa<PointerType>(arg.getType())) {
        getValueUpdate(graph, omap, &arg);
      }
    });

    // ddevec - I assume that this function is indirect, so it shouldn't be
    //   linked to the universal value
    /*
    // If this function isn't used locally
    if (!fcn.hasLocalLinkage() || analyzeUsesOfFunction(fcn)) {
      addConstraintsForNonInternalLinkage(graph, omap, fcn);
    }
    */

    if (!fcn.hasLocalLinkage() || analyzeUsesOfFunction(fcn)) {
      // If it appears that the function is unused, I'm going to add some fake
      // constraints for the arguments, to stop HU from combining them together
      // with other arguments that aren't filled until after HU
      // We add in a fake address of to make the node unusable
      std::vector<DUG::ConsID> con_ids;
      std::for_each(fcn.arg_begin(), fcn.arg_end(),
          [&graph, &omap, &con_ids](const Argument &arg) {
        auto arg_id = omap.getValue(&arg);
        auto id = omap.makeTempValue();
        con_ids.emplace_back(
          graph.add(Constraint::Type::AddressOf, arg_id, id));
      });
      graph.addUnusedFunction(omap.getObject(&fcn), std::move(con_ids));
    }

    // If this function has a body
    if (!fcn.isDeclaration()) {
      scanFcn(graph, omap, fcn);
    // There is no body...
    } else {
      if (isa<PointerType>(fcn.getFunctionType()->getReturnType())) {
        graph.add(Constraint::Type::Copy, omap.getReturn(&fcn),
            ObjectMap::UniversalValue);
      }

      // Add a universal constraint for each pointer arg
      std::for_each(fcn.arg_begin(), fcn.arg_end(),
          [&graph, &omap](const Argument &arg) {
        if (isa<PointerType>(arg.getType())) {
          // Must deal with pointers passed into extrernal fcns
          graph.add(Constraint::Type::Store, omap.getValue(&arg),
            ObjectMap::UniversalValue);

          // must deal w/ memory object passed into external fcns
          graph.add(Constraint::Type::Copy, omap.getValue(&arg),
            ObjectMap::UniversalValue);
        }
      });

      if (fcn.getFunctionType()->isVarArg()) {
        graph.add(Constraint::Type::Store, omap.getVarArg(&fcn),
            ObjectMap::UniversalValue);
      }
    }
  }
  //}}}

  return false;
  //}}}
}


bool SpecSFS::addIndirectCalls(DUG &graph, const Andersens &aux,
    ObjectMap &omap) {
  //{{{
  identifyAUXFcnCallRetInfo(graph, omap, aux);

  if_debug(
    dout << "initial unused functions are: ";
    std::for_each(graph.unused_function_begin(), graph.unused_function_end(),
        [&graph, &omap] (DUG::const_unused_function_iterator::reference pr) {
      const llvm::Function *fcn = cast<Function>(omap.valueAtID(pr.first));
      dout << " " << fcn->getName();
    });
    dout << "\n");

  // We iterate each indirect call in the DUG
  // to add the indirect info to the constraint map:
  TODO("Is using indirect_cbegin() correct here... I think I should switch it"
      " to the indirect call values added by the CFG components...");
  std::for_each(graph.indirect_cbegin(), graph.indirect_cend(),
      // We take different arguments, depending on if we're debugging...
      [&graph, &aux, &omap]
      (const std::pair<DUG::ObjID, DUG::CFGid> &pair) {
    const llvm::CallInst *ci =
      cast<llvm::CallInst>(omap.valueAtID(pair.first));
    llvm::CallSite CS(const_cast<llvm::CallInst *>(ci));
    auto fptr = CS.getCalledValue();

    // Get the functon call/ret info for this function:
    auto &pr = graph.getCFGCallRetInfo(omap.getValue(fptr));
    DUG::CFGid aux_call_id = pr.first;
    DUG::CFGid aux_ret_id = pr.second;

    // Add an edge from this call to the fcn
    DUG::CFGid call_id = pair.second;
    DUG::CFGid ret_id = graph.getCFGCallSuccessor(call_id);

    // Now add edges
    graph.addCFGEdge(call_id, aux_call_id);
    graph.addCFGEdge(aux_ret_id, ret_id);

    bool is_ext = false;
    const std::vector<DUG::ObjID> &fcnTargets = graph.getIndirFcns(pair.first);

    // Also, add constraints if needed
    std::for_each(std::begin(fcnTargets), std::end(fcnTargets),
          [&graph, &omap, &CS, &is_ext] (const DUG::ObjID fcn_id) {
      const llvm::Function *fcn = cast<llvm::Function>(omap.valueAtID(fcn_id));

      is_ext |= addConstraintsForCall(graph, omap, CS,
        const_cast<llvm::Function *>(fcn), nullptr);
    });

    if (is_ext) {
      // Add edge through this point due to inserted constraint?
      graph.addCFGEdge(call_id, ret_id);
    }
  });

  // Also, add call nodes for the direct calls.  Note, we couldn't do this
  // earlier, as we hadn't filled out the start/end nodes for all calls yet
  std::for_each(graph.direct_cbegin(), graph.direct_cend(),
      [&graph, &omap]
      (const std::pair<DUG::ObjID, DUG::CFGid> &pair) {
    llvm::CallInst *ci =
      cast<llvm::CallInst>(omap.valueAtID(pair.first));
    llvm::CallSite CS(const_cast<llvm::CallInst *>(ci));

    DUG::CFGid fcn_call_id =
      graph.getCFGFunctionStart(omap.getObject(CS.getCalledFunction()));
    DUG::CFGid fcn_ret_id = graph.getCFGFunctionEnd(fcn_call_id);

    DU::CFGID call_id = pair.second;
    DUG::CFGid ret_id = graph.getCFGCallSUccessor(call_id);

    graph.addCFGEdge(call_id, fcn_call_id);
    graph.addCFGEdge(fcn_ret_id, ret_id);
  });

  if_debug(
    dout << "Post insert unused functions are: ";
    std::for_each(graph.unused_function_begin(), graph.unused_function_end(),
        [&graph, &omap] (DUG::const_unused_function_iterator::reference pr) {
      const llvm::Function *fcn = cast<Function>(omap.valueAtID(pr.first));
      dout << " " << fcn->getName();
    });
    dout << "\n";
  )

  std::for_each(graph.unused_function_begin(), graph.unused_function_end(),
      [&graph, &omap]
      (const std::pair<DUG::ObjID, std::vector<DUG::ConsID>> &pr) {
    const llvm::Function *fcn =
      cast<const llvm::Function>(omap.valueAtID(pr.first));
    addConstraintsForNonInternalLinkage(graph, omap, *fcn);
    for (auto id : pr.second) {
      auto &cons = graph.getConstraint(id);
      cons.makeNoop();
    }
  });

  return false;
  //}}}
}

