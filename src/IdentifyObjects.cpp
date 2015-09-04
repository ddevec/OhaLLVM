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
#include "include/ObjectMap.h"
#include "include/ConstraintGraph.h"
#include "include/DUG.h"

#define SPECSFS_DEBUG
#include "include/Debug.h"

#include "llvm/Constants.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Module.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/raw_ostream.h"

// Private namespace for file-local info {{{
namespace {

// Structure Identification/offset helpers {{{
// Called from malloc-like allocations, to find the largest strcuture size the
// untyped allocation is cast to.
const llvm::Type *findLargestType(ObjectMap &omap,
    const llvm::Instruction &ins) {
  auto biggest_type = ins.getType()->getContainedType(0);

  bool found = false;
  int32_t max_size = 0;

  while (auto at = llvm::dyn_cast<llvm::ArrayType>(biggest_type)) {
    biggest_type = at->getElementType();
  }

  if (auto st = llvm::dyn_cast<llvm::StructType>(biggest_type)) {
    max_size = omap.getStructInfo(st).size();
  }

  // Now, see how each use is cast...
  std::for_each(ins.use_begin(), ins.use_end(),
      [&max_size, &found, &biggest_type, &omap]
      (const llvm::User *use) {
    auto cast = llvm::dyn_cast<llvm::CastInst>(use);

    if (cast && llvm::isa<llvm::PointerType>(cast->getType())) {
      found = true;

      // This is the type were casting to
      auto cast_type = cast->getType()->getContainedType(0);

      int32_t size = 0;

      // Strip off array qualifiers
      while (auto at = llvm::dyn_cast<llvm::ArrayType>(cast_type)) {
        cast_type = at->getElementType();
      }

      // If we're casting to a strucutre
      if (auto st = llvm::dyn_cast<llvm::StructType>(cast_type)) {
        size = omap.getStructInfo(st).size();
      }

      if (size > max_size) {
        max_size = size;
        biggest_type = cast_type;
      }
    }
  });

  if (!found && max_size == 0) {
    return omap.getMaxStructInfo().type();
  }

  return biggest_type;
}

std::pair<ObjectMap::ObjID, int32_t>
getGEPOffs(ObjectMap &omap, const llvm::GetElementPtrInst &gep) {
  auto obj_id = omap.getValue(&gep);
  int32_t offs = 0;

  auto type = gep.getPointerOperandType();

  // If this isn't a struct (for example, its an array), ignore it
  if (auto st_type = llvm::dyn_cast<llvm::StructType>(type)) {
    auto &si = omap.getStructInfo(st_type);

    // This loop is essentially to handle the nested nature of
    //   GEP instructions
    // It basically says, For the outer-layer of the struct
    for (auto gi = llvm::gep_type_begin(gep),
          en = llvm::gep_type_end(gep);
        gi != en; ++gi) {
      auto type = *gi;
      auto operand = gi.getOperand();
      // If it isn't a struct field, don't add subfield offsets
      if (!llvm::isa<llvm::StructType>(type)) {
        continue;
      }

      // Get the offset from this const value
      auto cons_op = llvm::dyn_cast<llvm::ConstantInt>(operand);
      assert(cons_op);
      uint32_t idx = cons_op ? cons_op->getZExtValue() : 0;

      // Add the translated offset
      offs += si.getFieldOffset(idx);
    }
  }

  return std::make_pair(obj_id, offs);
}
// }}}

// Using AUX with CFG helpers {{{
// ID to keep track of anders return values
struct aux_id { };
typedef ID<aux_id, int32_t, -1> AuxID;

static void identifyAUXFcnCallRetInfo(CFG &cfg,
    const ObjectMap &omap, const Andersens &aux) {

  // The mapping of andersen's values to functions
  std::map<AuxID, ObjectMap::ObjID> anders_to_fcn;

  std::for_each(omap.functions_cbegin(), omap.functions_cend(),
      [&anders_to_fcn, &aux]
      (const std::pair<ObjectMap::ObjID, const llvm::Value *> &pair) {
    anders_to_fcn[AuxID(aux.obj(pair.second))] = pair.first;
  });

  if_debug(
    dout << "Got ids for functions:";
    for (auto pr : anders_to_fcn) {
      dout << " {" << ValPrint(pr.second) << ", " << pr.first << "}";
    }
    dout << "\n");

  // We iterate each indirect call in the CFG
  // to add the indirect info to the constraint map:
  std::for_each(cfg.indirect_cbegin(), cfg.indirect_cend(),
      // We take different arguments, depending on if we're debugging...
      [&cfg, &aux, &anders_to_fcn, &omap]
      (const std::pair<ConstraintGraph::ObjID, CFG::CFGid> &pair) {
    const llvm::CallInst *ci =
      llvm::cast<llvm::CallInst>(omap.valueAtID(pair.first));

    llvm::CallSite CS(const_cast<llvm::CallInst *>(ci));

    auto fptr = CS.getCalledValue();

    // This is the andersen's node for this element
    auto ptsto = aux.getPointsTo(fptr);

    llvm::dbgs() << "have ptsto:";
    for (auto aid : ptsto) {
      llvm::dbgs() << " " << aid;
    }
    llvm::dbgs() << "\n";

    CFG::CFGid call_id = cfg.nextNode();
    CFG::CFGid ret_id = cfg.nextNode();

    for (auto anders_int_id : ptsto) {
      AuxID anders_id(anders_int_id);

      ObjectMap::ObjID fcn_id = anders_to_fcn.at(anders_id);

      cfg.addIndirFcn(pair.first, fcn_id);

      // Add edge from call->fcn start node
      dout << "Getting cfgfunctionstart for: " << fcn_id << "\n";
      dout << "Function is: " <<
        llvm::cast<const llvm::Function>(omap.valueAtID(fcn_id))->getName() <<
        "\n";
      cfg.addEdge(call_id, cfg.getFunctionStart(fcn_id));

      // Add edge from fcn ret node->ret
      cfg.addEdge(cfg.getFunctionReturn(fcn_id), ret_id);
    }

    cfg.addCallRetInfo(omap.getValue(fptr), call_id, ret_id);
  });
}


//}}}

// Functions/Variables helping me track internal values {{{
int32_t CallReturnPos = 1;
int32_t CallFirstArgPos = 2;

ObjectMap::ObjID getValueReturn(const ObjectMap &omap, const llvm::Value *v) {
  return ObjectMap::getOffsID(omap.getValue(v), CallReturnPos);
}

ObjectMap::ObjID getValueUpdate(ConstraintGraph &, ObjectMap &omap,
    const llvm::Value *v) {
  auto id = omap.getValue(v);

  // graph.associateNode(id, id);

  return id;
}
//}}}

// Helpers for dealing with adding CFG constraints {{{
void addCFGLoad(CFG &graph, CFG::CFGid load_id, ConstraintGraph::ObjID dest) {
  auto &node = graph.getNode(load_id);

  // Set this as an important or "r" node
  node.setR();
  llvm::dbgs() << "ADDING USE to cfg\n";
  graph.addUse(load_id, dest);

  node.debug_uses();
}

void addCFGStore(CFG &graph, CFG::CFGid *store_id,
    ConstraintGraph::ObjID dest) {
  // Well, stuff here
  llvm::dbgs() << "addStore called with store_id: " << *store_id << "\n";
  auto node = &graph.getNode(*store_id);

  // If this is a m-node (np-node), then it has a store, and we need to make a
  // new node
  if (node->m()) {
    CFG::CFGid next_id = graph.nextNode();

    graph.addEdge(*store_id, next_id);

    // Advance the id
    *store_id = next_id;

    llvm::dbgs() << "Have np-node, added new id: " << *store_id << "\n";
    node = &graph.getNode(*store_id);
  }
  llvm::dbgs() << "Setting M for store_id: " << *store_id << "\n";
  node->setM();

  llvm::dbgs() << "Adding def for: " << *store_id << "\n";
  graph.addDef(*store_id, dest);
}

void addCFGCallsite(CFG &cfg, ObjectMap &omap,
    llvm::Function *fcn, llvm::Instruction *ci, CFG::CFGid *pcall_id) {

  // Ignore the llvm debug function...
  if (fcn != nullptr && fcn->getName() == "llvm.dbg.declare") {
    return;
  }

  // Add a new node into the graph
  CFG::CFGid call_id = *pcall_id;
  CFG::CFGid next_id = cfg.nextNode();
  *pcall_id = next_id;

  if (fcn) {
    // We don't add edges now because we haven't identified the entry and return
    //   CFGid's for all functions yet
    // We also use a getObject(F) because functions are all associated with
    // objects, only some are associated with values
    dout << "Adding direct call to: " << fcn->getName() << " id: "
        << omap.getObject(fcn) << "\n";
    cfg.addCallsite(call_id, omap.getFunction(fcn), next_id);
  } else {
    // We also don't add edges between the call_id and the callsite for indirect
    //    calls because we don't know the destination until we run our AUX
    //    analysis.
    // All call instructions are associated with values, so we use getValue here
    dout << "Adding INDIRECT call to: " << *ci << "\n";
    ConstraintGraph::ObjID obj_id = omap.getValue(ci);
    if (obj_id == ObjectMap::NullValue) {
      omap.addValue(ci);
      obj_id = omap.getValue(ci);
    }
    dout << "ci has id: " << obj_id << "\n";
    assert(obj_id != ObjectMap::NullValue);
    cfg.addIndirectCall(call_id, obj_id, next_id);
  }
}
//}}}

// Functions dealing with identifying known external functions {{{
static bool isMalloc(const llvm::Value *V) {
  const llvm::CallInst *CI = llvm::dyn_cast<llvm::CallInst>(V);
  if (!CI)
    return false;

  llvm::Function *Callee = CI->getCalledFunction();
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
static bool addConstraintsForExternalCall(ConstraintGraph &cg, CFG &cfg,
    ObjectMap &omap, llvm::CallSite &CS, llvm::Function *F,
    CFG::CFGid *next_id) {
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
    const llvm::FunctionType *FTy = F->getFunctionType();

    if (FTy->getNumParams() > 1 &&
        llvm::isa<llvm::PointerType>(FTy->getParamType(0)) &&
        llvm::isa<llvm::PointerType>(FTy->getParamType(1))) {
      // *Dest = *Src, which requires an artificial graph node to
      // represent the constraint.
      // It is broken up into *Dest = temp, temp = *Src
      auto FirstArg = omap.getValue(CS.getArgument(0));
      auto SecondArg = omap.getValue(CS.getArgument(1));
      // Creates a new node in the graph, and a temp holder in omap
      auto TempArg = omap.createPhonyID();

      // Setup constraints
      llvm::dbgs() << "FIXME: Handle memcpy load/store properly!\n";
      cg.add(ConstraintType::Store, FirstArg, TempArg);
      cg.add(ConstraintType::Load, TempArg, SecondArg, TempArg);
      cg.add(ConstraintType::Copy, FirstArg, SecondArg);

      // Setup CFG
      // First setup the load
      addCFGLoad(cfg, *next_id, omap.getValue(CS.getArgument(1)));
      // Then setup the store
      addCFGStore(cfg, next_id, omap.getValue(CS.getArgument(0)));

      return true;
    }
  }

  // Result = Arg0
  if (F->getName() == "realloc" || F->getName() == "strchr" ||
      F->getName() == "strrchr" || F->getName() == "strstr" ||
      F->getName() == "strtok"  || F->getName() == "stpcpy" ||
      F->getName() == "getcwd"  || F->getName() == "strcat" ||
      F->getName() == "strcpy") {
    const llvm::FunctionType *FTy = F->getFunctionType();
    if (FTy->getNumParams() > 0 &&
        llvm::isa<llvm::PointerType>(FTy->getParamType(0))) {
      cg.add(ConstraintType::Copy,
          omap.getValue(CS.getInstruction()),
          omap.getValue(CS.getArgument(0)));
      return true;
    }
  }

  if (F->getName() == "realpath") {
    const llvm::FunctionType *FTy = F->getFunctionType();
    if (FTy->getNumParams() > 0 &&
        llvm::isa<llvm::PointerType>(FTy->getParamType(1))) {
      cg.add(ConstraintType::Copy,
          omap.getValue(CS.getInstruction()),
          omap.getValue(CS.getArgument(1)));
      return true;
    }
  }

  if (F->getName() == "freopen") {
    const llvm::FunctionType *FTy = F->getFunctionType();
    if (FTy->getNumParams() > 0 &&
        llvm::isa<llvm::PointerType>(FTy->getParamType(2))) {
      cg.add(ConstraintType::Copy,
          omap.getValue(CS.getInstruction()),
          omap.getValue(CS.getArgument(2)));
      return true;
    }
  }

  llvm::Instruction *I = CS.getInstruction();
  if (I) {
    llvm::Function *ParentF = I->getParent()->getParent();
    if (llvm::IntrinsicInst *II = llvm::dyn_cast<llvm::IntrinsicInst>(I)) {
      llvm::Intrinsic::ID IID = II->getIntrinsicID();
      if (IID == llvm::Intrinsic::vastart) {
        assert(ParentF->getFunctionType()->isVarArg()
            && "va_start in non-vararg function!");
        llvm::Value *Arg = II->getArgOperand(0);
        auto TempArg = omap.createPhonyID();
        llvm::dbgs() << "FIXME: ???VARAG???\n";
        cg.add(ConstraintType::AddressOf, TempArg,
            omap.getVarArg(ParentF));
        cg.add(ConstraintType::Store, omap.getValue(Arg),
            TempArg);
        addCFGStore(cfg, next_id, omap.getValue(Arg));
        return true;
      } else if (IID == llvm::Intrinsic::vaend) {
        return true;
      }
    }
  }

  if (F->getName() == "pthread_create") {
    const llvm::FunctionType *FTy = F->getFunctionType();
    if (FTy->getNumParams() == 4
        && llvm::isa<llvm::PointerType>(FTy->getParamType(0))
        && llvm::isa<llvm::PointerType>(FTy->getParamType(1))
        && llvm::isa<llvm::PointerType>(FTy->getParamType(2))
        && llvm::isa<llvm::PointerType>(FTy->getParamType(3))) {
      // Copy the actual argument into the formal argument.
      llvm::dbgs() << "FIXME: Handle pthread_create store!\n";
      llvm::Value *ThrFunc = I->getOperand(2);
      llvm::Value *Arg = I->getOperand(3);
      cg.add(ConstraintType::Store, omap.getValue(ThrFunc),
          omap.getValue(Arg), CallFirstArgPos);
      addCFGStore(cfg, next_id,
          omap.getOffsID(omap.getValue(Arg), CallFirstArgPos));
      return true;
    }
  }

  if (F->getName() == "pthread_getspecific") {
    const llvm::FunctionType *FTy = F->getFunctionType();
    if (FTy->getNumParams() == 1 &&
        llvm::isa<llvm::PointerType>(FTy->getReturnType())) {
      llvm::dbgs() << "FIXME: Handle pthread_getspecific store!\n";
      cg.add(ConstraintType::Store,
          omap.getValue(CS.getInstruction()),
          ObjectMap::PthreadSpecificValue);
      addCFGStore(cfg, next_id, ObjectMap::PthreadSpecificValue);
      return true;
    }
  } else if (F->getName() == "pthread_setspecific") {
    const llvm::FunctionType *FTy = F->getFunctionType();
    if (FTy->getNumParams() == 2 &&
        llvm::isa<llvm::PointerType>(FTy->getParamType(1))) {
      cg.add(ConstraintType::Copy,
          ObjectMap::PthreadSpecificValue,
          omap.getValue(CS.getInstruction()->getOperand(1)));
      return true;
    }
  }

  return false;
}
//}}}

// Constraint helpers {{{
// FIXME: This needs to handle structure fields... if I'm initializing the
//   fields of the struct
static int32_t addGlobalInitializerConstraints(ConstraintGraph &cg, CFG &cfg,
    ObjectMap &omap, ObjectMap::ObjID dest, const llvm::Constant *C) {
  int32_t offset = 0;
  // Simple case, single initializer
  if (C->getType()->isSingleValueType()) {
    if (llvm::isa<llvm::PointerType>(C->getType())) {
      llvm::dbgs() << "FIXME: Ignoring global init constraint, because "
        "Andersen's doesn't include it, and it causes my analysis to break\n";
      llvm::dbgs() << "   To resolve this I should make Andersen's include "
        "the constraint\n";
      // NOTE: This is just to make us match Andersens... the "Correct" code is
      // below
      // auto dest_val = omap.valueAtID(dest);
      // auto dest_obj = omap.getObject(dest_val);
      auto glbl_id = omap.createPhonyID();
      // cg.add(ConstraintType::GlobalInit, glbl_id, dest_obj, dest);
      cg.add(ConstraintType::GlobalInit, glbl_id, dest, dest);
      /*
      cg.add(ConstraintType::GlobalInit, glbl_id,
          omap.getConstValue(C), dest);
      */
      cfg.addGlobalInit(glbl_id);

      offset = 1;
    }

  // Initialized to null value
  } else if (C->isNullValue()) {
    auto glbl_id = omap.createPhonyID();
    cg.add(ConstraintType::GlobalInit, glbl_id, ObjectMap::NullValue, dest);
    cfg.addGlobalInit(glbl_id);

    offset = 1;

  // Set to some other defined value
  } else if (!llvm::isa<llvm::UndefValue>(C)) {
    // It must be an array, or struct
    assert(llvm::isa<llvm::ConstantArray>(C) ||
        llvm::isa<llvm::ConstantStruct>(C) ||
        llvm::isa<llvm::ConstantDataSequential>(C));

    // For each field of the initializer, add a constraint for the field
    // This is done differently for structs than for array
    if (auto cs = llvm::dyn_cast<llvm::ConstantStruct>(C)) {
      std::for_each(cs->op_begin(), cs->op_end(),
          [&offset, &cg, &cfg, &cs, &omap, &dest]
          (const llvm::Use &field) {
        auto field_cons = llvm::cast<const llvm::Constant>(field);
        offset += addGlobalInitializerConstraints(cg, cfg, omap,
          omap.getOffsID(dest, offset), field_cons);
      });
    } else {
      std::for_each(C->op_begin(), C->op_end(),
          [&offset, &cg, &cfg, &cs, &omap, &dest]
          (const llvm::Use &field) {
        auto field_cons = llvm::cast<const llvm::Constant>(field);
        offset = addGlobalInitializerConstraints(cg, cfg, omap,
          dest, field_cons);
      });
    }
  } else {
    llvm::dbgs() << "FIXME: Unknown constant init: " << *C << "\n";
  }

  return offset;
}

static void addConstraintForConstPtr(ConstraintGraph &cg,
    ObjectMap &omap, const llvm::GlobalValue &glbl) {
  bool inserted = false;
  // NOTE: We don't use a std::for_each here b/c we need to break
  for (auto I = glbl.use_begin(), E = glbl.use_end(); I != E; ++I) {
    auto use = *I;

    // If this use is a constant expr, we can add the constraint now
    if (auto *CE = llvm::dyn_cast<const llvm::ConstantExpr>(use)) {
      // If its a ptr to int, add an "intvalue"
      if (CE->getOpcode() == llvm::Instruction::PtrToInt) {
        if (!inserted) {
          cg.add(ConstraintType::Copy, ObjectMap::IntValue,
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
static bool analyzeUsesOfFunction(const llvm::Value &val) {
  if (!llvm::isa<llvm::PointerType>(val.getType())) {
    return true;
  }

  for (auto UI = val.use_begin(), UE = val.use_end(); UI != UE; ++UI) {
    if (llvm::isa<llvm::LoadInst>(*UI)) {
      return false;
    } else if (auto SI = llvm::dyn_cast<llvm::StoreInst>(*UI)) {
      if (&val == SI->getOperand(1)) {
        return false;

      // This pointer is being stored
      } else if (SI->getOperand(1)) {
        return true;
      }
    } else if (auto GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(*UI)) {
      if (analyzeUsesOfFunction(*GEP)) {
        return true;
      }
    } else if (auto CI = llvm::dyn_cast<llvm::CallInst>(*UI)) {
      llvm::CallSite CS((llvm::CallInst *)CI);
      // Can't use std::for_each because of return
      for (size_t i = 0, e = CS.arg_size(); i < e; i++) {
        if (CS.getArgument(i) == &val) {
          return true;
        }
      }
    } else if (auto CE = llvm::dyn_cast<llvm::ConstantExpr>(*UI)) {
      if (CE->getOpcode() == llvm::Instruction::GetElementPtr ||
          CE->getOpcode() == llvm::Instruction::BitCast) {
        if (analyzeUsesOfFunction(*CE)) {
          return true;
        }
      } else {
        return true;
      }
    } else if (llvm::dyn_cast<llvm::ICmpInst>(*UI) != nullptr) {
      return true;
    } else {
      return true;
    }
  }

  return false;
}

static void addConstraintsForNonInternalLinkage(ConstraintGraph &cg,
    ObjectMap &omap,
    const llvm::Function &fcn) {
  std::for_each(fcn.arg_begin(), fcn.arg_end(),
      [&cg, &omap] (const llvm::Argument &arg) {
    if (llvm::isa<llvm::PointerType>(arg.getType())) {
      cg.add(ConstraintType::Copy, omap.getValue(&arg),
        ObjectMap::UniversalValue);
    }
  });
}


static void addConstraintsForIndirectCall(ConstraintGraph &cg, ObjectMap &omap,
    llvm::CallSite &CS) {
  auto &called_val = *CS.getCalledValue();

  if (llvm::isa<llvm::InlineAsm>(&called_val)) {
    llvm::errs() << "WARNING: Ignoring inline asm!\n";
    return;
  }

  getValueUpdate(cg, omap, &called_val);

  // We take care of adding the constriants to the map in addCFGCallsite, called
  //    from addConstraintsForCall() before this
}

static void addConstraintsForDirectCall(ConstraintGraph &cg, ObjectMap &omap,
    llvm::CallSite &CS, llvm::Function *F) {
  auto &called_val = *CS.getCalledValue();

  // If this call returns a pointer
  if (llvm::isa<llvm::PointerType>(CS.getType())) {
    auto val = omap.getValue(CS.getInstruction());

    // If the function that's called also returns a pointer
    if (llvm::isa<llvm::PointerType>(F->getFunctionType()->getReturnType())) {
      // Add a copy from the return value into this value
      cg.add(ConstraintType::Copy, val,
          omap.getValueReturn(&called_val));

    // The callsite returns a pointer, but the function returns a
    // non-pointer value, treat it as a non-pointer cast to a pointer
    } else {
      cg.add(ConstraintType::Copy, val,
          ObjectMap::UniversalValue);
    }
  // The callsite returns a non-pointer, but the function returns a
  // pointer value, treat it as a pointer cast to a non-pointer
  } else if (F &&
      llvm::isa<llvm::PointerType>(F->getFunctionType()->getReturnType())) {
    cg.add(ConstraintType::Copy,
        omap.getValueReturn(&called_val),
        ObjectMap::UniversalValue);
  }

  auto ArgI = CS.arg_begin();
  auto ArgE = CS.arg_end();

  bool external = F->isDeclaration();

  auto FargI = F->arg_begin();
  auto FargE = F->arg_end();

  // For each arg
  for (; FargI != FargE && ArgI != ArgE; ++FargI, ++ArgI) {
    if (external && llvm::isa<llvm::PointerType>((*ArgI)->getType())) {
      llvm::dbgs() << "Adding arg to universal value :(\n";
      cg.add(ConstraintType::Copy, omap.getValue(*ArgI),
          ObjectMap::UniversalValue);
    }

    // If we expect a pointer type
    if (llvm::isa<llvm::PointerType>(FargI->getType())) {
      // And we get one!
      if (llvm::isa<llvm::PointerType>((*ArgI)->getType())) {
        dout << "Adding arg copy!\n";
        cg.add(ConstraintType::Copy, omap.getValue(FargI),
            omap.getValue(*ArgI));
      // But if its not a pointer type...
      } else {
        // Map it to everything (i2p)
        dout << "Adding i2p universal value :(\n";
        cg.add(ConstraintType::Copy, omap.getValue(FargI),
            ObjectMap::UniversalValue);
      }
    }
  }

  // Varargs magic :(
  if (F->getFunctionType()->isVarArg()) {
    for (; ArgI != ArgE; ++ArgI) {
      if (llvm::isa<llvm::PointerType>((*ArgI)->getType())) {
        cg.add(ConstraintType::Copy, omap.getVarArg(F),
            omap.getValue(*ArgI));
      }
    }
  }
}

static bool addConstraintsForCall(ConstraintGraph &cg, CFG &cfg,
    ObjectMap &omap, llvm::CallSite &CS, llvm::Function *F,
    CFG::CFGid *next_id) {
  // bool isIndirect = (F == NULL);

  // Try to recover the function from a bitcast (taken from sfs code)
  // If this function was just cast to a function pointer from the prior
  // instruction, this will determine so statically, and treat it as a direct
  // call
  if (!F) {
    llvm::Value *callee = CS.getInstruction()->getOperand(0);

    llvm::ConstantExpr *E =
      llvm::dyn_cast<llvm::ConstantExpr>(callee);
    if (E && E->getOpcode() == llvm::Instruction::BitCast) {
      F = llvm::dyn_cast<llvm::Function>(E->getOperand(0));
    }
  }

  // If this is direct && is external
  if (F && F->isDeclaration()) {
    // Add it as an external function
    if (addConstraintsForExternalCall(cg, cfg, omap, CS, F, next_id)) {
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
    addCFGCallsite(cfg, omap, F, CS.getInstruction(), next_id);
  }
  if (F) {
    addConstraintsForDirectCall(cg, omap, CS, F);
  } else {
    addConstraintsForIndirectCall(cg, omap, CS);
  }

  return true;
}
//}}}

// Helpers for individual instruction constraints {{{
static void idRetInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  auto &ret = *llvm::cast<const llvm::ReturnInst>(&inst);

  // Returns without arguments (void) don't add constraints
  if (ret.getNumOperands() == 0) {
    return;
  }

  // Get the return value
  llvm::Value *src = ret.getOperand(0);

  // If its not a pointer, we don't care about it
  if (!llvm::isa<llvm::PointerType>(src->getType())) {
    return;
  }

  // The function in which ret was called
  const llvm::Function *F = ret.getParent()->getParent();

  cg.add(ConstraintType::Copy,
      omap.getReturn(F), omap.getValue(src));
}

static bool idCallInst(ConstraintGraph &cg, CFG &cfg, ObjectMap &omap,
    const llvm::Instruction &inst, CFG::CFGid *bb_id) {
  // Meh, Callsites don't take consts... bleh
  llvm::CallSite CS(const_cast<llvm::Instruction *>(&inst));

  if (isMalloc(&inst)) {
    // If its a malloc, we don't add constriants for the call, we instead
    //   pretend the call is actually a addressof operation
    //
    // Unfortunately, malloc doesn't tell us what size strucutre is
    //   being allocated, we infer this information from its uses
    auto inferred_type = findLargestType(omap, inst);
    // Now, allocate space for this in the object map:
    auto src_obj = omap.getObject(&inst);
    if (auto st = llvm::dyn_cast<llvm::StructType>(inferred_type)) {
      // Create a new dest for this malloc
      llvm::dbgs() << "Adding type for malloc: " << inst << "\n";
      src_obj = omap.addObject(st, &inst);
    }
    cg.add(ConstraintType::AddressOf,
        getValueUpdate(cg, omap, &inst),
        src_obj);

    return false;
  }

  if (llvm::isa<llvm::PointerType>(CS.getType())) {
    getValueUpdate(cg, omap, &inst);
  }

  return addConstraintsForCall(cg, cfg, omap, CS, CS.getCalledFunction(),
      bb_id);
}

static void idAllocaInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  auto &alloc = *llvm::cast<const llvm::AllocaInst>(&inst);

  // Get the object associated with this allocation
  // auto obj_id = omap.getObject(&alloc);

  // Associate that obj with this value
  // cg.associateNode(obj_id, omap.getValue(&inst));

  // Add a constraint pointing this value to that object
  auto cons_id = cg.add(ConstraintType::AddressOf,
      getValueUpdate(cg, omap, &alloc),
      omap.getObject(&alloc));

  auto &cons = cg.getConstraint(cons_id);

  // If this is a concrete location (read non-array) set it to be strong
  auto T = alloc.getAllocatedType();
  if (auto at = llvm::dyn_cast<llvm::ArrayType>(T)) {
    cons.setStrong(false);
    T = at->getElementType();
  } else {
    cons.setStrong(true);
  }

  // FIXME: Now, handle structure fields...
  // if (structtype...)
}

static void idLoadInst(ConstraintGraph &cg, CFG &cfg, ObjectMap &omap,
    const llvm::Instruction &inst, CFG::CFGid next_id) {
  auto &ld = *llvm::cast<const llvm::LoadInst>(&inst);

  if (llvm::isa<llvm::PointerType>(ld.getType())) {
    auto ld_id = getValueUpdate(cg, omap, &ld);

    auto cons_id = cg.add(ConstraintType::Load, ld_id,
        omap.getValue(ld.getOperand(0)),
        ld_id);

    llvm::dbgs() << "Adding load (" << ld_id << ") " << inst << " to cons: " <<
      cons_id << "\n";

    // Add this to the uses
    addCFGLoad(cfg, next_id, ld_id);
  } else if (llvm::isa<llvm::PointerType>(ld.getOperand(0)->getType()) &&
      llvm::isa<llvm::IntegerType>(ld.getType())) {
    // Ld is an int value... those will alias.  So we instead create a phony id
    auto ld_id = omap.getValue(&ld);

    cg.add(ConstraintType::Load, ld_id,
        omap.getValue(ld.getOperand(0)),
        ObjectMap::IntValue);

    addCFGLoad(cfg, next_id, ld_id);
  } else if (llvm::isa<llvm::StructType>(ld.getType())) {
    llvm::errs() << "FIXME: Unhandled struct load!\n";
  }
}

static void idStoreInst(ConstraintGraph &cg, CFG &cfg, ObjectMap &omap,
    const llvm::Instruction &inst, CFG::CFGid *next_id) {
  auto &st = llvm::cast<const llvm::StoreInst>(inst);

  auto st_id = omap.getValue(&st);

  if (llvm::isa<llvm::PointerType>(st.getOperand(0)->getType())) {
    // Store from ptr
    // auto dest = omap.getObject(st.getOperand(1));
    auto dest = omap.getValue(st.getOperand(1));
    if (dest == ObjectMap::NullValue) {
      // If this is not an object, store to the value
      dest = omap.getValue(st.getOperand(1));
      llvm::dbgs() << "No object for store dest: " << dest << " : " <<
        ValPrint(dest) << "\n";
    }
    cg.add(ConstraintType::Store,
        st_id,
        omap.getValue(st.getOperand(0)),
        dest);
  } else if (llvm::ConstantExpr *ce =
      llvm::dyn_cast<llvm::ConstantExpr>(st.getOperand(0))) {
    // If we just cast a ptr to an int then stored it.. we can keep info on it
    if (ce->getOpcode() == llvm::Instruction::PtrToInt) {
      // auto dest = omap.getObject(st.getOperand(1));
      auto dest = omap.getValue(st.getOperand(1));
      if (dest == ObjectMap::NullValue) {
        // If this is not an object, store to the value
        dest = omap.getValue(st.getOperand(1));
        llvm::dbgs() << "No object for store dest: " << dest << " : " <<
          ValPrint(dest) << "\n";
      }
      cg.add(ConstraintType::Store,
          st_id,
          omap.getValue(st.getOperand(0)),
          dest);
    // Uhh, dunno what to do now
    } else {
      llvm::errs() << "FIXME: Unhandled constexpr case!\n";
    }
  // put int value into the int pool
  } else if (llvm::isa<llvm::IntegerType>(st.getOperand(0)->getType()) &&
      llvm::isa<llvm::PointerType>(st.getOperand(1)->getType())) {
    // auto dest = omap.getObject(st.getOperand(1));
    auto dest = omap.getValue(st.getOperand(1));
    if (dest == ObjectMap::NullValue) {
      // If this is not an object, store to the value
      dest = omap.getValue(st.getOperand(1));
      llvm::dbgs() << "No object for store dest: " << dest << " : " <<
        ValPrint(dest) << "\n";
    }
    cg.add(ConstraintType::Store,
        st_id,
        ObjectMap::IntValue,
        dest);
  // Poop... structs
  } else if (llvm::isa<llvm::StructType>(st.getOperand(0)->getType())) {
    llvm::errs() << "FIXME: Ignoring struct store\n";
    /*
    cg.add(ConstraintType::Store, st_id,
        omap.getValue(st.getOperand(1)),
        ObjectMap::AgregateNode);
        */
  } else {
    // Didn't add it to the graph?
    llvm::dbgs() << "FIXME: Not adding store object to graph: "
        << st_id << "\n";
    return;
  }

  // We have to create a new objID to uniquely identify this store...
  addCFGStore(cfg, next_id, st_id);
}

static void idGEPInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  auto &gep = llvm::cast<const llvm::GetElementPtrInst>(inst);

  auto src = getGEPOffs(omap, gep);
  auto src_id = src.first;
  auto src_offs = src.second;

  cg.add(ConstraintType::Copy,
      getValueUpdate(cg, omap, &gep),
      src_id,
      src_offs);
}

static void idI2PInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  // ddevec - FIXME: Could trace through I2P here, by keeping a listing
  //    of i2ps...
  // sfs does this, Andersens doesn't.  I don't think its a sound approach, as
  // something external may modify any int reference passed to it (where we're
  // unaware of what's in it) and screw up our tracking
  // Instead I'm just going to go w/ the Andersen's, approach, give it an
  // int value
  cg.add(ConstraintType::Copy,
      getValueUpdate(cg, omap, &inst),
      ObjectMap::IntValue);
}

static void idBitcastInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  auto &bcast = llvm::cast<const llvm::BitCastInst>(inst);

  assert(llvm::isa<llvm::PointerType>(inst.getType()));

  auto id = getValueUpdate(cg, omap, &bcast);

  assert(llvm::isa<llvm::PointerType>(bcast.getOperand(0)->getType()));
  auto op = omap.getValue(bcast.getOperand(0));

  cg.add(ConstraintType::Copy, id, op);
}

static void idPhiInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  auto &phi = *llvm::cast<const llvm::PHINode>(&inst);

  assert(llvm::isa<llvm::PointerType>(phi.getType()));

  // hheheheheh PHI-d
  auto phid = getValueUpdate(cg, omap, &phi);

  for (size_t i = 0, e = phi.getNumIncomingValues(); i != e; ++i) {
    cg.add(ConstraintType::Copy, phid,
        omap.getValue(phi.getIncomingValue(i)));
  }
}

static void idSelectInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  auto &select = llvm::cast<const llvm::SelectInst>(inst);

  // this inst --> select: op(0) ? op(1) : op(2)

  if (llvm::isa<llvm::PointerType>(select.getType())) {
    auto sid = getValueUpdate(cg, omap, &select);

    cg.add(ConstraintType::Copy, sid,
        omap.getValue(select.getOperand(1)));
    cg.add(ConstraintType::Copy, sid,
        omap.getValue(select.getOperand(2)));

  } else if (llvm::isa<llvm::StructType>(select.getType())) {
    llvm::errs() << "Warning, unsupported select on struct!\n";
  }
}

static void idVAArgInst(ConstraintGraph &, ObjectMap &,
    const llvm::Instruction &) {
  llvm_unreachable("Vaarg not handled yet");
}

static void idExtractInst(ConstraintGraph &, ObjectMap &,
    const llvm::Instruction &) {
  llvm_unreachable("ExtractValue not handled yet");
}
//}}}

// Instruction parsing helpers {{{
static void processBlock(ConstraintGraph &cg, CFG &cfg,
    std::set<const llvm::BasicBlock *> &seen, ObjectMap &omap,
    const llvm::BasicBlock &BB, CFG::CFGid parent_id) {
  // Make sure we don't follow the same block twice
  assert(seen.count(&BB) == 0);
  seen.insert(&BB);

  // Extract the basic block info about this block for our CFG (required for
  //    computing SSA on address-taken variables)
  // This is for the basic block, not a value, so it's "anon"
  CFG::CFGid next_id = cfg.nextNode();
  // Add an edge from our parent, if we have one
  if (parent_id.valid()) {
    cfg.addEdge(parent_id, next_id);
  // Or if we don't have a parent denote that we should get edges from calls
  } else {
    dout << "Adding CFGFunctionStart for: " << omap.getObject(BB.getParent()) <<
      "\n";
    dout << "Function is : " << BB.getParent()->getName() << "\n";

    // If this is main, we add an edge from glbl_init to it
    if (BB.getParent()->getName() == "main") {
      cfg.addEdge(CFG::CFGInit, next_id);
    }

    cfg.addFunctionStart(omap.getFunction(BB.getParent()), next_id);
  }


  bool block_has_call = false;

  // Now, analyze each instruction, extract constraints
  for (auto &inst : BB) {
    bool is_ptr = llvm::isa<llvm::PointerType>(inst.getType());

    switch (inst.getOpcode()) {
      case llvm::Instruction::Ret:
        {
          assert(!is_ptr);

          // We add a "return node" for this block if there is a call within it
          if (block_has_call) {
            // Get a new "anon" cfg node for the ret node
            CFG::CFGid ret_id = cfg.nextNode();
            cfg.addEdge(next_id, ret_id);
            next_id = ret_id;
          // Otherwise, we consider the entry node as the return node
          }

          cfg.addFunctionReturn(omap.getFunction(BB.getParent()), next_id);

          idRetInst(cg, omap, inst);
        }
        break;
      case llvm::Instruction::Invoke:
      case llvm::Instruction::Call:
        block_has_call |= idCallInst(cg, cfg, omap, inst, &next_id);
        break;
      case llvm::Instruction::Alloca:
        assert(is_ptr);
        idAllocaInst(cg, omap, inst);
        break;
      case llvm::Instruction::Load:
        idLoadInst(cg, cfg, omap, inst, next_id);
        break;
      case llvm::Instruction::Store:
        assert(!is_ptr);
        idStoreInst(cg, cfg, omap, inst, &next_id);
        break;
      case llvm::Instruction::GetElementPtr:
        assert(is_ptr);
        idGEPInst(cg, omap, inst);
        break;
      case llvm::Instruction::IntToPtr:
        assert(is_ptr);
        idI2PInst(cg, omap, inst);
        break;
      case llvm::Instruction::BitCast:
        if (is_ptr) {
          idBitcastInst(cg, omap, inst);
        }
        break;
      case llvm::Instruction::PHI:
        if (is_ptr) {
          idPhiInst(cg, omap, inst);
        }
        break;
      case llvm::Instruction::Select:
          idSelectInst(cg, omap, inst);
        break;
      case llvm::Instruction::VAArg:
        if (is_ptr) {
          idVAArgInst(cg, omap, inst);
        }
        break;
      case llvm::Instruction::ExtractValue:
        if (is_ptr) {
          idExtractInst(cg, omap, inst);
        }
        break;
      default:
        assert(!is_ptr && "Unknown instruction has a pointer return type!");
    }
  }

  // Process all of our successor blocks (In DFS order)
  std::for_each(succ_begin(&BB), succ_end(&BB),
      [&cg, &cfg, &seen, &omap, next_id] (const llvm::BasicBlock *succBB) {
    if (seen.count(succBB) == 0) {
      processBlock(cg, cfg, seen, omap, *succBB, next_id);
    }
  });
}

void scanFcn(ConstraintGraph &cg, CFG &cfg, ObjectMap &omap,
    const llvm::Function &fcn) {
  // SFS adds instructions to graph, we've already added them?
  //   So we don't need to worry about it
  // Add instructions to graph
  /*
  std::for_each(inst_begin(fcn), inst_end(fcn),
      [&graph, &omap] (const Instruction &inst) {
    if (isa<PointerType>(inst.getType())) {
      cfg.addNode(&inst);
    }
  });
  */

  // Now create constraints in depth first order:
  std::set<const llvm::BasicBlock *> seen;
  processBlock(cg, cfg, seen, omap, fcn.getEntryBlock(), CFG::CFGid::invalid());
}
//}}}

}  // End private namespace
//}}}

bool SpecSFS::identifyObjects(ObjectMap &omap, const llvm::Module &M) {
  //{{{
  // Okay, we need to identify all possible objects within the module, then
  //   insert them into our object map

  // Identify all used strucutre types...
  {
    std::vector<llvm::StructType *> struct_types;
    M.findUsedStructTypes(struct_types);
    std::for_each(std::begin(struct_types), std::end(struct_types),
        [&omap] (llvm::StructType *st) {
      omap.addStructInfo(st);
    });
  }

  // Id all globals
  std::for_each(M.global_begin(), M.global_end(),
      [&omap](const llvm::Value &glbl) {
    // Need to do special stuffs for structures
    omap.addValue(&glbl);
    omap.addObject(&glbl);
  });

  // Functions are memory objects
  std::for_each(std::begin(M), std::end(M),
      [&omap](const llvm::Function &fcn) {
    omap.addObject(&fcn);
  });

  // Now add nodes for the functions, and all the operations within
  for (auto &fcn : M) {
    omap.addValueFunction(&fcn);

    // If this is a function which returns a pointer, we'll need a node for it
    if (llvm::isa<llvm::PointerType>(fcn.getFunctionType()->getReturnType())) {
      omap.addReturn(&fcn);
    }

    // If this is a vararg function... I've got problems!
    if (fcn.getFunctionType()->isVarArg()) {
      omap.addVarArg(&fcn);
    }

    // Args are also values...
    // Structures here? Yuck!
    std::for_each(fcn.arg_begin(), fcn.arg_end(),
        [&omap](const llvm::Argument &arg) {
      if (llvm::isa<llvm::StructType>(arg.getType())) {
        llvm::dbgs() << "FIXME: Possibly missed ptsto in arg struct???\n";
      }

      if (llvm::isa<llvm::PointerType>(arg.getType())) {
        omap.addValue(&arg);
      }
    });

    // Each BB in each function gets an ObjID as an object
    std::for_each(std::begin(fcn), std::end(fcn),
        [&omap](const llvm::BasicBlock &bb) {
      omap.addObject(&bb);
    });

    // For each instruction:
    std::for_each(inst_begin(fcn), inst_end(fcn),
        [&omap](const llvm::Instruction &inst) {
      // Add pointer values
      if (llvm::isa<llvm::PointerType>(inst.getType())) {
        omap.addValue(&inst);
      }

      // Add alloc objects
      if (auto AI = llvm::dyn_cast<llvm::AllocaInst>(&inst)) {
        // FIXME: Add object fields for the struct!
        omap.addObject(AI);
      }

      // Also add values for loads/stores, even if they return int types
      // -- I need the values for unique identifiers later
      if (auto ld = llvm::dyn_cast<llvm::LoadInst>(&inst)) {
        if (!llvm::isa<llvm::PointerType>(ld->getType())) {
          omap.addValue(ld);
        }
      }

      if (auto st = llvm::dyn_cast<llvm::StoreInst>(&inst)) {
        omap.addValue(st);
      }

      // How do I deal w/ structures here? -- something related to a bitcast?
      if (isMalloc(&inst)) {
        omap.addObject(&inst);
      }
    });
  }

  return false;
  //}}}
}

bool SpecSFS::createConstraints(ConstraintGraph &cg, CFG &cfg, ObjectMap &omap,
    const llvm::Module &M) {
  //{{{

  // Special Constraints {{{
  // First, we set up some constraints for our special constraints:
  // Universal value
  cg.add(ConstraintType::AddressOf, ObjectMap::UniversalValue,
      ObjectMap::UniversalValue);

  // FIXME: The SFS component does not know the predecessors of UniversalValue,
  //   as Andersens does not provide them...  So I (unsoundly) removed it for
  //   now?
  /*
  auto ui_store_id = omap.createPhonyID();
  cg.add(ConstraintType::Store, ui_store_id, ObjectMap::UniversalValue,
      ObjectMap::UniversalValue);
  */

  // Null value pts to null object
  cg.add(ConstraintType::AddressOf,
      ObjectMap::NullValue, ObjectMap::NullObjectValue);
  //}}}

  // Global Variables {{{
  // Okay, first create nodes for all global variables:
  std::for_each(M.global_begin(), M.global_end(),
      [&cg, &cfg, &omap](const llvm::GlobalVariable &glbl) {
    // Associate the global address with a node:
    // graph.associateNode(obj_id, &glbl);
    auto val_id = omap.getValue(&glbl);
    auto obj_id = omap.getObject(&glbl);

    // Create the constraint for the actual global
     cg.add(ConstraintType::AddressOf,
      getValueUpdate(cg, omap, &glbl),
      obj_id);

    // If its a global w/ an initalizer
    if (glbl.hasDefinitiveInitializer()) {
      addGlobalInitializerConstraints(cg, cfg, omap, val_id,
        glbl.getInitializer());

      // If the global is a pointer constraint, it needs a const ptr
      //   (as it has an initializer)
      if (llvm::isa<llvm::PointerType>(glbl.getType())) {
        addConstraintForConstPtr(cg, omap, glbl);
      }

    // Doesn't have initializer
    } else {
      cg.add(ConstraintType::Copy, omap.getObject(&glbl),
          ObjectMap::UniversalValue);
      cg.add(ConstraintType::Copy, omap.getValue(&glbl),
          ObjectMap::UniversalValue);
    }
  });
  //}}}

  // Functions {{{
  // Now that we've dealt with globals, move on to functions
  for (auto &fcn : M) {
    auto obj_id = omap.getObject(&fcn);
    // graph.associateNode(obj_id, &fcn);

    cg.add(ConstraintType::AddressOf,
        getValueUpdate(cg, omap, &fcn),
        obj_id);

    // Functions are constant pointers
    addConstraintForConstPtr(cg, omap, fcn);
  }

  // Now we deal with the actual internals of functions
  for (auto &fcn : M) {
    // If we return a pointer
    if (llvm::isa<llvm::PointerType>(fcn.getFunctionType()->getReturnType())) {
      // Create a node for this fcn's return
      // cg.associateNode(omap.getReturn(&fcn), omap.getObject(&fcn));
    }
    // Set up our vararg node
    if (fcn.getFunctionType()->isVarArg()) {
      // cg.associateNode(omap.getVarArg(&fcn), omap.getObject(&fcn));
    }

    // Update the value for each arg
    std::for_each(fcn.arg_begin(), fcn.arg_end(),
        [&cg, &omap](const llvm::Argument &arg) {
      if (llvm::isa<llvm::PointerType>(arg.getType())) {
        getValueUpdate(cg, omap, &arg);
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
      // Don't add unused function pieces for main or llvm.dbg.declare, they are
      //     special, and don't need to be tracked
      if (fcn.getName() != "main" && fcn.getName() != "llvm.dbg.declare") {
        std::vector<ConstraintGraph::ConsID> con_ids;
        std::for_each(fcn.arg_begin(), fcn.arg_end(),
            [&cg, &cfg, &omap, &con_ids](const llvm::Argument &arg) {
          auto arg_id = omap.getValue(&arg);
          auto id = omap.makeTempValue();

          auto con_id = cg.add(ConstraintType::AddressOf, arg_id, id);
          assert(con_id != ConstraintGraph::ConsID::invalid());
          con_ids.emplace_back(con_id);
        });
        cfg.addUnusedFunction(omap.getFunction(&fcn), std::move(con_ids));
      }
    }

    // If this function has a body
    if (!fcn.isDeclaration()) {
      scanFcn(cg, cfg, omap, fcn);
    // There is no body...
    } else {
      // FIXME:
      // This used to create constraints for function arguments, but for
      //   external calls... This caused issue with not being able to get the
      //   UniversalValue set from Andersens... so I'm once again unsoundly
      //   removing it
      /*
      if (llvm::isa<llvm::PointerType>(
            fcn.getFunctionType()->getReturnType())) {
        cg.add(ConstraintType::Copy, omap.getReturn(&fcn),
            ObjectMap::UniversalValue);
      }

      // Add a universal constraint for each pointer arg
      std::for_each(fcn.arg_begin(), fcn.arg_end(),
          [&cg, &omap, &fcn](const llvm::Argument &arg) {
        if (llvm::isa<llvm::PointerType>(arg.getType())) {
          // Must deal with pointers passed into extrernal fcns
          // We add a phony store object?, so we can uniquely refer
          //   to this later
          auto st_id = omap.createPhonyID();
          llvm::dbgs() << "Creating universal value arg pass to id: " << st_id
              << "\n";
          llvm::dbgs() << "fcn is: " << fcn.getName() << "\n";
          llvm::dbgs() << "arg is: " << arg << "\n";
          cg.add(ConstraintType::Store, st_id,
            ObjectMap::UniversalValue, omap.getValue(&arg));

          // must deal w/ memory object passed into external fcns
          cg.add(ConstraintType::Copy, omap.getValue(&arg),
            ObjectMap::UniversalValue);
        }
      });

      if (fcn.getFunctionType()->isVarArg()) {
        auto st_id = omap.createPhonyID();
        llvm::dbgs() << "Creating universal value vararg pass to id: " << st_id
            << "\n";
        cg.add(ConstraintType::Store, st_id,
            ObjectMap::UniversalValue, omap.getVarArg(&fcn));
      }
      */
    }
  }
  //}}}

  return false;
  //}}}
}


bool SpecSFS::addIndirectCalls(ConstraintGraph &cg, CFG &cfg,
    const Andersens &aux, ObjectMap &omap) {
  //{{{
  identifyAUXFcnCallRetInfo(cfg, omap, aux);

  if_debug(
    dout << "initial unused functions are: ";
    std::for_each(cfg.unused_function_begin(), cfg.unused_function_end(),
        [&cg, &cfg, &omap] (CFG::const_unused_function_iterator::reference pr) {
      const llvm::Function *fcn =
          llvm::cast<llvm::Function>(omap.valueAtID(pr.first));
      dout << " " << fcn->getName();
    });
    dout << "\n");

  // We iterate each indirect call in the DUG
  // to add the indirect info to the constraint map:
  std::for_each(cfg.indirect_cbegin(), cfg.indirect_cend(),
      [&cg, &cfg, &aux, &omap]
      (const std::pair<ConstraintGraph::ObjID, CFG::CFGid> &pair) {
    const llvm::CallInst *ci =
      llvm::cast<llvm::CallInst>(omap.valueAtID(pair.first));
    llvm::CallSite CS(const_cast<llvm::CallInst *>(ci));
    auto fptr = CS.getCalledValue();

    // Get the functon call/ret info for this function:
    auto &pr = cfg.getCallRetInfo(omap.getValue(fptr));
    CFG::CFGid aux_call_id = pr.first;
    CFG::CFGid aux_ret_id = pr.second;

    // Add an edge from this call to the fcn
    CFG::CFGid call_id = pair.second;
    CFG::CFGid ret_id = cfg.getCallSuccessor(call_id);

    // Now add edges
    cfg.addEdge(call_id, aux_call_id);
    cfg.addEdge(aux_ret_id, ret_id);

    bool is_ext = false;
    const std::vector<ConstraintGraph::ObjID> &fcnTargets =
      cfg.getIndirFcns(pair.first);

    // Also, add constraints if needed
    std::for_each(std::begin(fcnTargets), std::end(fcnTargets),
          [&cg, &cfg, &omap, &CS, &is_ext]
          (const ConstraintGraph::ObjID fcn_id) {
      const llvm::Function *fcn = omap.getFunction(fcn_id);

      is_ext |= addConstraintsForCall(cg, cfg, omap, CS,
        const_cast<llvm::Function *>(fcn), nullptr);

      cfg.removeUnusedFunction(cg, fcn_id);
    });

    if (is_ext) {
      // Add edge through this point due to inserted constraint?
      cfg.addEdge(call_id, ret_id);
    }
  });

  // Also, add call nodes for the direct calls.  Note, we couldn't do this
  // earlier, as we hadn't filled out the start/end nodes for all calls yet
  std::for_each(cfg.direct_cbegin(), cfg.direct_cend(),
      [&cg, &cfg, &omap]
      (const std::pair<CFG::CFGid, std::vector<ConstraintGraph::ObjID>> &pair) {
    CFG::CFGid call_id = pair.first;
    CFG::CFGid ret_id = cfg.getCallSuccessor(call_id);

    std::for_each(pair.second.cbegin(), pair.second.cend(),
        [&cg, &cfg, &omap, &call_id, &ret_id]
        (const ConstraintGraph::ObjID &ins_id){
      dout << "Got value: " << *omap.valueAtID(ins_id) << "\n";

      ConstraintGraph::ObjID fcn_id = ins_id;
      CFG::CFGid fcn_call_id =
        cfg.getFunctionStart(fcn_id);
      CFG::CFGid fcn_ret_id = cfg.getFunctionReturn(fcn_id);

      cfg.addEdge(call_id, fcn_call_id);
      cfg.addEdge(fcn_ret_id, ret_id);

      cfg.removeUnusedFunction(cg, fcn_id);
    });
  });

  // if_debug(
  llvm::dbgs() << "Post insert unused functions are: ";
  std::for_each(cfg.unused_function_begin(), cfg.unused_function_end(),
      [&cfg, &omap] (CFG::const_unused_function_iterator::reference pr) {
    const llvm::Function *fcn =
        llvm::cast<llvm::Function>(omap.valueAtID(pr.first));
    llvm::dbgs() << " " << fcn->getName();
  });
  llvm::dbgs() << "\n";
  // )

  std::for_each(cfg.unused_function_begin(), cfg.unused_function_end(),
      [&cg, &cfg, &omap]
      (const std::pair<ObjectMap::ObjID, std::vector<ConstraintGraph::ConsID>>
           &pr) {
    const llvm::Function *fcn =
      llvm::cast<const llvm::Function>(omap.valueAtID(pr.first));
    addConstraintsForNonInternalLinkage(cg, omap, *fcn);
    for (auto id : pr.second) {
      cg.removeConstraint(id);
    }
  });

  return false;
  //}}}
}

