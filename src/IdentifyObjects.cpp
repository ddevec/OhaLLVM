/*
 * Copyright (C) 2015 David Devecsery
 *
 * NOTE: Components stolen from Andersens.cpp
 */
// #define SPECSFS_DEBUG

#include <cassert>
#include <cstdint>

#include <algorithm>
#include <functional>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "include/Debug.h"

#include "include/AllocInfo.h"
#include "include/Andersens.h"
#include "include/ConstraintGraph.h"
#include "include/DUG.h"
#include "include/ObjectMap.h"
#include "include/SpecSFS.h"
#include "include/lib/IndirFcnTarget.h"

#include "llvm/Pass.h"
#include "llvm/Constants.h"
#include "llvm/Function.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Module.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/raw_ostream.h"


// Private namespace for file-local info {{{
namespace {

// Using AUX with CFG helpers {{{
// ID to keep track of anders return values
struct aux_id { };
typedef ID<aux_id, int32_t, -1> AuxID;

static void identifyAUXFcnCallRetInfo(CFG &cfg,
    ObjectMap &omap, const Andersens &aux,
    const IndirFunctionInfo *dyn_info) {
  // If we don't have dynamic info:
  if (dyn_info == nullptr || !dyn_info->hasInfo()) {
    // The mapping of andersen's values to functions
    std::map<AuxID, ObjectMap::ObjID> anders_to_fcn;

    auto &aux_val_nodes = aux.getObjectMap();
    std::for_each(std::begin(aux_val_nodes), std::end(aux_val_nodes),
        [&anders_to_fcn, &aux, &omap]
        (const std::pair<const llvm::Value *, uint32_t> &pr) {
      if (auto pfcn = llvm::dyn_cast<llvm::Function>(pr.first)) {
        auto fcn_id = omap.getFunction(pfcn);
        auto aux_val_id = pr.second;

        anders_to_fcn.emplace(AuxID(aux_val_id), fcn_id);
      }
    });

    if_debug(
      dout("Got ids for functions:");
      for (auto pr : anders_to_fcn) {
        dout(" {" << ValPrint(pr.second) << ", " << pr.first << "}");
      }
      dout("\n"));

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

      if_debug(
        dout("have ptsto:");
        for (auto aid : ptsto) {
          dout(" " << aid);
        }
        dout("\n"));

      CFG::CFGid call_id = cfg.nextNode();
      CFG::CFGid ret_id = cfg.nextNode();
      dout("call cfg_id: " << call_id << "\n");
      dout("ret cfg_id: " << ret_id << "\n");

      for (auto anders_int_id : ptsto) {
        // FIXME: Andersen's reports the function as pointing to the universal
        //   set... or all unknown functions... I'm ignoring this for now, but
        //   will fix if needed
        if (anders_int_id == 0) {
          llvm::dbgs() << "FIXME: Function points to universal value..."
            " Ignoring the universal value ptr\n";
          continue;
        }

        AuxID anders_id(anders_int_id);

        auto fcn_id_it = anders_to_fcn.find(anders_id);
        if (fcn_id_it == std::end(anders_to_fcn)) {
          /*
          llvm::dbgs() << "FIXME: Anders points to a function I don't"
            " recognize???\n";
          */
          continue;
        }
        ObjectMap::ObjID fcn_id = fcn_id_it->second;

        cfg.addIndirFcn(pair.first, fcn_id);

        // Add edge from call->fcn start node
        dout("Getting cfgfunctionstart for: " << fcn_id << "\n");
        dout("Function is: " <<
          llvm::cast<const llvm::Function>(omap.valueAtID(fcn_id))->getName() <<
          "\n");
        // NOTE: Should add assert that the if should only be skipped in
        //   instances of DCE
        if (cfg.hasFunctionStart(fcn_id)) {
          auto fcn_start_id = cfg.getFunctionStart(fcn_id);
          cfg.addPred(fcn_start_id, call_id);

          // Some functions (like "error" or "abort" don't return)
          if (cfg.hasFunctionReturn(fcn_id)) {
            // Add edge from fcn ret node->ret
            auto fcn_ret_id = cfg.getFunctionReturn(fcn_id);
            cfg.addPred(ret_id, fcn_ret_id);
          }
        }
      }

      cfg.addCallRetInfo(omap.getValue(fptr), call_id, ret_id);
    });
  // If we do have dynamic info, just ignore the andersens info, and use ours
  } else {
    std::for_each(cfg.indirect_cbegin(), cfg.indirect_cend(),
        // We take different arguments, depending on if we're debugging...
        [&cfg, &omap, &dyn_info]
        (const std::pair<ConstraintGraph::ObjID, CFG::CFGid> &pair) {
      const llvm::CallInst *ci =
        llvm::cast<llvm::CallInst>(omap.valueAtID(pair.first));

      CFG::CFGid call_id = cfg.nextNode();
      CFG::CFGid ret_id = cfg.nextNode();

      llvm::dbgs() << "Getting ci: " << *ci << "\n";
      auto fcn_targets = dyn_info->getTargets(ci);

      for (auto fcn : fcn_targets) {
        auto fcn_id = omap.getFunction(llvm::cast<llvm::Function>(fcn));
        cfg.addIndirFcn(pair.first, fcn_id);

        auto fcn_start_id = cfg.getFunctionStart(fcn_id);
        cfg.addPred(fcn_start_id, call_id);

        if (cfg.hasFunctionReturn(fcn_id)) {
          // Add edge from fcn ret node->ret
          auto fcn_ret_id = cfg.getFunctionReturn(fcn_id);
          cfg.addPred(ret_id, fcn_ret_id);
        }
      }

      llvm::CallSite CS(const_cast<llvm::CallInst *>(ci));
      auto fptr = CS.getCalledValue();

      cfg.addCallRetInfo(omap.getValue(fptr), call_id, ret_id);
    });
  }
}


//}}}

// Functions/Variables helping me track internal values {{{
/*
ObjectMap::ObjID getValueReturn(ObjectMap &omap, const llvm::Value *v) {
  return ObjectMap::getOffsID(omap.getValue(v), CallReturnPos);
}
*/

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
  dout("ADDING USE to cfg\n");
  graph.addUse(load_id, dest);

  node.debug_uses();
}

void addCFGStore(CFG &graph, CFG::CFGid *store_id,
    ConstraintGraph::ObjID dest) {
  // Well, stuff here
  dout("addStore called with store_id: " << *store_id << "\n");
  auto node = &graph.getNode(*store_id);

  // If this is a m-node (np-node), then it has a store, and we need to make a
  // new node
  if (node->m()) {
    CFG::CFGid next_id = graph.nextNode();
    dout("store cfg_id: " << next_id << "\n");

    graph.addPred(next_id, *store_id);

    // Advance the id
    *store_id = next_id;

    dout("Have np-node, added new id: " << *store_id << "\n");
    node = &graph.getNode(*store_id);
  }
  dout("Setting M for store_id: " << *store_id << "\n");
  node->setM();
  // Need to also set R for store nodes.... bleh
  node->setR();

  dout("Adding def for: " << *store_id << "\n");
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
  dout("callsite cfg_id: " << next_id << "\n");
  *pcall_id = next_id;

  if (fcn) {
    // We don't add edges now because we haven't identified the entry and return
    //   CFGid's for all functions yet
    // We also use a getObject(F) because functions are all associated with
    // objects, only some are associated with values
    dout("Adding direct call to: " << fcn->getName() << " id: "
        << omap.getObject(fcn) << "\n");
    cfg.addCallsite(call_id, omap.getFunction(fcn), next_id);
  } else {
    // We also don't add edges between the call_id and the callsite for indirect
    //    calls because we don't know the destination until we run our AUX
    //    analysis.
    // All call instructions are associated with values, so we use getValue here
    llvm::CallSite CS(ci);
    if (llvm::isa<llvm::InlineAsm>(CS.getCalledValue())) {
      llvm::dbgs() << "WARNING: ignoring inline asm: " << *ci << "\n";
      cfg.addPred(next_id, call_id);
    } else {
      dout("Adding INDIRECT call to: " << *ci << "\n");
      ConstraintGraph::ObjID obj_id = omap.getValue(ci);
      if (obj_id == ObjectMap::NullValue) {
        omap.addValue(ci);
        obj_id = omap.getValue(ci);
      }
      dout("ci has id: " << obj_id << "\n");
      assert(obj_id != ObjectMap::NullValue);
      cfg.addIndirectCall(call_id, obj_id, next_id);
    }
  }
}
//}}}

static bool isMalloc(const llvm::Value *V) {
  return Andersens::isMallocCall(V);
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
      // FIXME: are fopen and fdopen really non-ptsto contraint creators?
      //   I would imagine they are really malloc functions...
      F->getName() == "fopen" || F->getName() == "fdopen" ||
      F->getName() == "fflush" || F->getName() == "feof" ||
      F->getName() == "fileno" || F->getName() == "clearerr" ||
      F->getName() == "rewind" || F->getName() == "ftell" ||
      F->getName() == "ferror" || F->getName() == "fgetc" ||
      F->getName() == "fgetc" || F->getName() == "_IO_getc" ||
      F->getName() == "fwrite" || F->getName() == "fread" ||
      F->getName() == "fgets" || F->getName() == "ungetc" ||
      F->getName() == "fputc_unlocked" || F->getName() == "fputc" ||
      F->getName() == "fputs" || F->getName() == "fputs_unlocked" ||
      F->getName() == "putc" || F->getName() == "fclose" ||
      F->getName() == "ftell" || F->getName() == "rewind" ||
      F->getName() == "_IO_putc" || F->getName() == "fseek" ||
      F->getName() == "fgetpos" || F->getName() == "fsetpos" ||
      F->getName() == "printf" || F->getName() == "fprintf" ||
      F->getName() == "sprintf" || F->getName() == "vprintf" ||
      F->getName() == "vfprintf" || F->getName() == "vsprintf" ||
      F->getName() == "scanf" || F->getName() == "fscanf" ||
      F->getName() == "sscanf" || F->getName() == "__assert_fail" ||
      F->getName() == "modf" || F->getName() == "exit" ||
      F->getName() == "_exit" || F->getName() == "strlen" ||
      F->getName() == "close" || F->getName() == "abort" ||
      F->getName() == "atexit" || F->getName() == "error" ||
      F->getName() == "umask" || F->getName() == "free" ||
      F->getName() == "setfscreatecon" ||
      F->getName() == "__ctype_get_mb_cur_max" ||
      F->getName() == "iswprint" || F->getName() == "mbsinit" ||
      // Although this copies the strings, it doesn't move pointers
      F->getName() == "mbrtowc" ||
      F->getName() == "fchdir" || F->getName() == "fseeko" ||
      F->getName() == "ferror_unlocked" ||
      F->getName() == "fork" || F->getName() == "waitpid" ||
      F->getName() == "raise" || F->getName() == "__fpending" ||
      F->getName() == "ferror" || F->getName() == "fchown" ||
      F->getName() == "fchmod" || F->getName() == "lchown" ||
      F->getName() == "chown" || F->getName() == "lchown" ||
      F->getName() == "getc_unlocked" || F->getName() == "snprintf" ||
      F->getName() == "__freading" || F->getName() == "lseek" ||
      F->getName() == "fcntl" || F->getName() == "feeko" ||
      F->getName() == "abs" || F->getName() == "toupper" ||
      F->getName() == "__iso_c99sscanf" || F->getName() == "iswupper" ||
      F->getName() == "tolower" || F->getName() == "towupper" ||
      F->getName() == "towlower" || F->getName() == "strncasecmp" ||
      F->getName() == "floor" || F->getName() == "ceil" ||
      F->getName() == "fabs" || F->getName() == "acos" ||
      F->getName() == "asin" || F->getName() == "atan" ||
      F->getName() == "atan2" || F->getName() == "cos" ||
      F->getName() == "cosh" || F->getName() == "exp" ||
      F->getName() == "fmod" || F->getName() == "strcasecmp" ||
      F->getName() == "log" || F->getName() == "log10" ||
      F->getName() == "sin" || F->getName() == "sinh" ||
      F->getName() == "tan" || F->getName() == "tanh" ||
      F->getName() == "readlink" || F->getName() == "qsort" ||
      F->getName() == "sqrt" || F->getName() == "strftime" ||
      F->getName() == "getuid" || F->getName() == "getgid" ||
      F->getName() == "gettimeofday" || F->getName() == "settimeofday" ||
      F->getName() == "getopt_long" || F->getName() == "getopt") {
    return true;
  }

  // Ignore memset, it modifies the array, but not the ptsto
  if (F->getName().find("llvm.memset") ||
      F->getName().find("llvm.pow")) {
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
      auto first_arg = omap.getValue(CS.getArgument(0));
      auto second_arg = omap.getValue(CS.getArgument(1));
      // Creates a new node in the graph, and a temp holder in omap

      // Setup constraints
      assert(llvm::isa<llvm::PointerType>(CS.getArgument(0)->getType()));
      auto dest = CS.getArgument(0);
      // Get the type of the dest, stripping bitcasts if needed
      auto type = getTypeOfVal(dest);
      // Strip away the outer pointer type
      assert(llvm::isa<llvm::PointerType>(type));
      type = type->getContainedType(0);

      // If this is a struct, we need to insert all the loads and stores for all
      // of the fields...
      if (auto st = llvm::dyn_cast<llvm::StructType>(type)) {
        // Okay, for each field of the structure...
        auto &si = omap.getStructInfo(st);

        // Setup the base of our CFG node, we need all stores to proceed in
        //   parallel...
        auto base_id = next_id;
        auto merge_id = cfg.nextNode();

        // Now iterate each field, and add a copy for each field
        int32_t i = 0;
        std::for_each(si.sizes_begin(), si.sizes_end(),
            [&cfg, &cg, &i, &omap, &first_arg, &second_arg, &base_id,
              &merge_id, &CS] (int32_t) {
          auto node_id = cfg.nextNode();
          auto load_dest = omap.createPhonyID();
          // The gep dests have equivalent ptsto as the argumens
          auto load_gep_dest = omap.createPhonyID(CS.getArgument(1));
          auto store_gep_dest = omap.createPhonyID(CS.getArgument(0));
          auto store_id = omap.createPhonyID();

          // Okay, now create the constraints
          // The load_dest is the destination address of the load:
          cg.add(ConstraintType::Copy, load_gep_dest, second_arg, i);
          cg.add(ConstraintType::Load, load_dest, load_gep_dest, load_dest);

          cg.add(ConstraintType::Copy, store_gep_dest, first_arg, i);

          cg.add(ConstraintType::Store, store_id, load_dest,
            store_gep_dest);

          cfg.addPred(node_id, *base_id);
          cfg.addPred(merge_id, node_id);

          // Create a load at this id
          dout("Adding load: " << load_dest << " and store: " <<
            store_id << "\n");
          addCFGLoad(cfg, node_id, load_dest);
          addCFGStore(cfg, &node_id, store_id);

          i++;
        });

        // Advance the merge_id to next_id
        *next_id = merge_id;

      // If this isn't a struct, handle it normally
      } else {
        auto load_id = omap.createPhonyID();
        auto store_id = omap.createPhonyID();

        cg.add(ConstraintType::Load, load_id, second_arg, load_id);
        cg.add(ConstraintType::Store, store_id, load_id, first_arg);

        // Setup CFG
        // First setup the load
        addCFGLoad(cfg, *next_id, load_id);
        // Then setup the store
        addCFGStore(cfg, next_id, store_id);
      }

      return true;
    }
  }

  // Result = Arg0
  if (F->getName() == "realloc" || F->getName() == "strchr" ||
      F->getName() == "strrchr" || F->getName() == "strstr" ||
      F->getName() == "strtok"  || F->getName() == "stpcpy" ||
      F->getName() == "getcwd"  || F->getName() == "strcat" ||
      F->getName() == "strcpy"  || F->getName() == "strncat"  ||
      F->getName() == "strpbrk"  || F->getName() == "localtime"  ||
      // FIXME: I don't fully understand the man page, so I'm not 100% sure
      //   bindtextdomain goes here
      F->getName() == "textdomain"  ||
      F->getName() == "bindtextdomain") {
    const llvm::FunctionType *FTy = F->getFunctionType();
    if (FTy->getNumParams() > 0 &&
        llvm::isa<llvm::PointerType>(FTy->getParamType(0))) {
      cg.add(ConstraintType::Copy,
          omap.getValue(CS.getInstruction()),
          omap.getValue(CS.getArgument(0)));
      return true;
    }
  }

  // Locale functions
  if (F->getName() == "getlocale" ||
      F->getName() == "setlocale" ||
      F->getName() == "nl_langinfo") {
    cg.add(ConstraintType::AddressOf,
        omap.getValue(CS.getInstruction()),
        ObjectMap::LocaleObject);
    return true;
  }

  // Errno
  if (F->getName() == "__errno_location") {
    cg.add(ConstraintType::AddressOf,
        omap.getValue(CS.getInstruction()),
        ObjectMap::ErrnoObject);
    return true;
  }

  // getenv -- This is currently linked to argv...
  if (F->getName() == "getenv") {
    cg.add(ConstraintType::AddressOf,
      omap.getValue(CS.getInstruction()),
      ObjectMap::ArgvObjectValue);
    return true;
  }

  // CType Functions
  if (F->getName() == "__ctype_b_loc") {
    cg.add(ConstraintType::AddressOf,
        omap.getValue(CS.getInstruction()),
        ObjectMap::CTypeObject);
    return true;
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

  if (F->getName() == "gettext") {
    const llvm::FunctionType *FTy = F->getFunctionType();
    if (FTy->getNumParams() > 0 &&
        llvm::isa<llvm::PointerType>(FTy->getParamType(0))) {
      cg.add(ConstraintType::Copy,
          omap.getValue(CS.getInstruction()),
          omap.getValue(CS.getArgument(0)));
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
    if (llvm::IntrinsicInst *II = llvm::dyn_cast<llvm::IntrinsicInst>(I)) {
      llvm::Intrinsic::ID IID = II->getIntrinsicID();
      if (IID == llvm::Intrinsic::vastart) {
        // llvm::Function *ParentF = I->getParent()->getParent();
        assert(I->getParent()->getParent()->getFunctionType()->isVarArg()
            && "va_start in non-vararg function!");
        llvm::dbgs() << "FIXME: ???VARAG???\n";
        /*
        llvm::Value *Arg = II->getArgOperand(0);
        auto TempArg = omap.createPhonyID();
        cg.add(ConstraintType::AddressOf, TempArg,
            omap.getVarArg(ParentF));
        cg.add(ConstraintType::Store, omap.getValue(Arg),
            TempArg);
        addCFGStore(cfg, next_id, omap.getValue(Arg));
        */
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

  llvm::dbgs() << "!!! Unknown external call: " << F->getName() << "\n";
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
      dout("Adding global init for: " << ValPrint(dest) << "\n");
      cg.add(ConstraintType::GlobalInit, glbl_id, omap.getConstValue(C), dest);
      /*
      cg.add(ConstraintType::GlobalInit, glbl_id,
          omap.getConstValue(C), dest);
      */
      cfg.addGlobalInit(glbl_id);

      offset = 1;
    }

  // Initialized to null value
  } else if (C->isNullValue()) {
    dout("Glbl init on: " << ValPrint(dest) << "\n");
    if (llvm::isa<llvm::StructType>(C->getType())) {
      llvm::dbgs() << "FIXME: Ignoring zero init on struct type for now...\n";
      offset = 1;
    } else {
      // auto glbl_id = omap.createPhonyID();
      dout("Adding NULL global init for: " << ValPrint(dest) << "\n");
      llvm::dbgs() << "FIXME: Ignoring zero init on non-struct to be consistent"
        " with andersens";
      /*
      cg.add(ConstraintType::GlobalInit, glbl_id, ObjectMap::NullValue, dest);
      cfg.addGlobalInit(glbl_id);
      */

      offset = 1;
    }
  // Set to some other defined value
  } else if (!llvm::isa<llvm::UndefValue>(C)) {
    // It must be an array, or struct
    assert(llvm::isa<llvm::ConstantArray>(C) ||
        llvm::isa<llvm::ConstantStruct>(C) ||
        llvm::isa<llvm::ConstantDataSequential>(C));

    dout("Adding STRUCT global init for: " << ValPrint(dest) << "\n");
    // For each field of the initializer, add a constraint for the field
    // This is done differently for structs than for array
    if (auto cs = llvm::dyn_cast<llvm::ConstantStruct>(C)) {
      llvm::dbgs() << "FIXME: Missing ptsto set for ConstantStruct"
        " Initializer\n";
      /* BROKEN
      std::for_each(cs->op_begin(), cs->op_end(),
          [&offset, &cg, &cfg, &cs, &omap, &dest]
          (const llvm::Use &field) {
        auto field_cons = llvm::cast<const llvm::Constant>(field);
        offset += addGlobalInitializerConstraints(cg, cfg, omap,
          omap.getOffsID(dest, offset), field_cons);
      });
      */
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
      auto node_id = omap.createPhonyID();
      auto arg_id = omap.getValue(&arg);
      cg.add(ConstraintType::Copy, node_id, arg_id,
        ObjectMap::UniversalValue);
      // The arg now aliases the universal value
      // omap.addObjAlias(ObjectMap::UniversalValue, arg_id);
    }
  });
}


static void addConstraintsForIndirectCall(ConstraintGraph &, ObjectMap &,
    llvm::CallSite &CS) {
  auto &called_val = *CS.getCalledValue();

  if (llvm::isa<llvm::InlineAsm>(&called_val)) {
    llvm::errs() << "WARNING: Ignoring inline asm!\n";
    return;
  }

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
      auto ret_val = omap.getReturn(&called_val);
      cg.add(ConstraintType::Copy, val, ret_val);
    // The callsite returns a pointer, but the function returns a
    // non-pointer value, treat it as a non-pointer cast to a pointer
    } else {
      // The call now aliases the universal value
      // omap.addObjAlias(ObjectMap::UniversalValue, val);
      cg.add(ConstraintType::Copy, val,
          ObjectMap::UniversalValue);
    }
  // The callsite returns a non-pointer, but the function returns a
  // pointer value, treat it as a pointer cast to a non-pointer
  } else if (F &&
      llvm::isa<llvm::PointerType>(F->getFunctionType()->getReturnType())) {
    // The call now aliases the universal value
    auto ret_id = omap.getReturn(F);
    // omap.addObjAlias(ObjectMap::UniversalValue, ret_id);
    cg.add(ConstraintType::Copy,
        ret_id, ObjectMap::UniversalValue);
  }

  auto ArgI = CS.arg_begin();
  auto ArgE = CS.arg_end();

  bool external = F->isDeclaration();

  auto FargI = F->arg_begin();
  auto FargE = F->arg_end();

  // For each arg
  for (; FargI != FargE && ArgI != ArgE; ++FargI, ++ArgI) {
    if (external && llvm::isa<llvm::PointerType>((*ArgI)->getType())) {
      dout("Adding arg to universal value :(\n");
      auto node_id = omap.createPhonyID();
      auto arg_id = omap.getValue(*ArgI);

      /*
      cg.add(ConstraintType::Copy, node_id, arg_id,
          ObjectMap::UniversalValue);
      */
      cg.add(ConstraintType::Copy, node_id, ObjectMap::UniversalValue,
          arg_id);
      // The arg now aliases the universal value
      // omap.addObjAlias(ObjectMap::UniversalValue, arg_id);
    }

    // If we expect a pointer type
    if (llvm::isa<llvm::PointerType>(FargI->getType())) {
      // And we get one!
      if (llvm::isa<llvm::PointerType>((*ArgI)->getType())) {
        dout("Adding arg copy!\n");
        auto node_id = omap.createPhonyID();
        auto dest_id = omap.getValue(FargI);
        auto src_id = omap.getValue(*ArgI);
        dout("Copy src: " << ValPrint(src_id) << " -> " << ValPrint(dest_id)
          << "\n");
        cg.add(ConstraintType::Copy, node_id, src_id, dest_id);
      // But if its not a pointer type...
      } else {
        // Map it to everything (i2p)
        dout("Adding i2p universal value :(\n");
        auto node_id = omap.createPhonyID();
        auto dest_id = omap.getValue(FargI);
        cg.add(ConstraintType::Copy, node_id, ObjectMap::UniversalValue,
            dest_id);
        // The arg now aliases the universal value
        // omap.addObjAlias(ObjectMap::UniversalValue, arg_id);
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
  // Try to recover the function from a bitcast (taken from sfs code)
  // If this function was just cast to a function pointer from the prior
  // instruction, this will determine so statically, and treat it as a direct
  // call
  if (!F) {
    llvm::Value *callee = CS.getCalledValue();

    auto ce = llvm::dyn_cast<llvm::ConstantExpr>(callee);

    if (ce) {
      if (ce->getOpcode() == llvm::Instruction::BitCast) {
        F = llvm::dyn_cast<llvm::Function>(ce->getOperand(0));
      }
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

static void addGlobalConstraintForType(ConstraintType ctype,
    ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Type *type, ObjectMap::ObjID dest,
    ObjectMap::ObjID src_obj, bool strong) {

  // All globals are (implicitly) pointers, I'm evaluating based off of the
  //   contained type
  type = type->getContainedType(0);

  // Strip wrapping arrays
  while (auto at = llvm::dyn_cast<llvm::ArrayType>(type)) {
    // Arrays invalidate strength
    strong = false;
    type = at->getContainedType(0);
  }


  if (auto st = llvm::dyn_cast<llvm::StructType>(type)) {
    auto &si = omap.getStructInfo(st);

    for (size_t i = 0; i < si.numSizes(); i++) {
      // Add an addr of to this offset
      dout("Adding Global AddressOf for struct.  Dest: " << dest
          << ", src " << src_obj << " + " << i << "\n");

      // For global object, force the src, dest offset to + i
      auto cons_id = cg.add(ctype,
          ObjectMap::getOffsID(dest, i),
          ObjectMap::getOffsID(src_obj, i));
      auto &cons = cg.getConstraint(cons_id);
      // Update strength as appropriate
      cons.setStrong(strong && si.fieldStrong(i));
    }
  } else {
    dout("Adding Global AddressOf for NON-struct.  Dest: " << dest
        << ", src " << src_obj << "\n");
    // No offs defaults to 0 in offs column, which is what we want for a
    //   non-struct object
    auto cons_id = cg.add(ctype, dest, src_obj);
    auto &cons = cg.getConstraint(cons_id);
    cons.setStrong(strong);
  }
}

static void addConstraintForType(ConstraintType ctype,
    ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Type *type, ObjectMap::ObjID dest,
    ObjectMap::ObjID src_obj, bool strong) {

  dout("Passed in inferred_type: " << type << "\n");

  // Strip wrapping arrays
  while (auto at = llvm::dyn_cast<llvm::ArrayType>(type)) {
    // Arrays invalidate strength
    strong = false;
    type = at->getContainedType(0);
  }

  if (auto st = llvm::dyn_cast<llvm::StructType>(type)) {
    auto &si = omap.getStructInfo(st);

    for (size_t i = 0; i < si.numSizes(); i++) {
      // Add an addr of to this offset
      dout("Adding AddressOf for struct.  Dest: " << dest << ", src "
        << src_obj << " + " << i << "\n");
      auto cons_id = cg.add(ctype, dest, src_obj, i);
      auto &cons = cg.getConstraint(cons_id);
      // Update strength as appropriate
      cons.setStrong(strong && si.fieldStrong(i));
    }
  } else {
    // No offs defaults to 0 in offs column, which is what we want for a
    //   non-struct object
    auto cons_id = cg.add(ctype, dest, src_obj);
    auto &cons = cg.getConstraint(cons_id);
    cons.setStrong(strong);
  }
}

static bool idCallInst(ConstraintGraph &cg, CFG &cfg, ObjectMap &omap,
    const llvm::Instruction &inst, CFG::CFGid *bb_id) {
  // Meh, Callsites don't take consts... bleh
  llvm::CallSite CS(const_cast<llvm::Instruction *>(&inst));

  if (isMalloc(&inst)) {
    dout("Have malloc call: " << inst << "\n");
    // If its a malloc, we don't add constriants for the call, we instead
    //   pretend the call is actually a addressof operation
    //
    // Unfortunately, malloc doesn't tell us what size strucutre is
    //   being allocated, we infer this information from its uses
    auto inferred_type = findLargestType(omap, inst);

    auto dest_id = omap.getValue(&inst);
    auto src_obj_id = omap.getObject(&inst);

    dout("Malloc addAddressForType(" << dest_id << ", " << src_obj_id
        << ")\n");
    addConstraintForType(ConstraintType::AddressOf, cg, omap,
        inferred_type, dest_id, src_obj_id, false);

    return false;
  }

  return addConstraintsForCall(cg, cfg, omap, CS, CS.getCalledFunction(),
      bb_id);
}

static void idAllocaInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  auto &alloc = *llvm::cast<const llvm::AllocaInst>(&inst);

  // If the thing we're allocating is a structure... then we need to handle
  //   addressof for all sub-fields!
  auto type = alloc.getAllocatedType();

  auto dest_id = omap.getValue(&alloc);
  auto src_obj_id = omap.getObject(&alloc);

  addConstraintForType(ConstraintType::AddressOf, cg, omap,
      type, dest_id, src_obj_id, true);
}

static void idLoadInst(ConstraintGraph &cg, CFG &cfg, ObjectMap &omap,
    const llvm::Instruction &inst, CFG::CFGid next_id) {
  auto &ld = *llvm::cast<const llvm::LoadInst>(&inst);

  if (llvm::isa<llvm::PointerType>(ld.getType())) {
    auto ld_id = getValueUpdate(cg, omap, &ld);

    if_debug(auto cons_id =) cg.add(ConstraintType::Load, ld_id,
        omap.getValue(ld.getOperand(0)),
        ld_id);

    dout("Adding load (" << ld_id << ") " << inst << " to cons: " <<
      cons_id << "\n");

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

  dout("store is: " << ValPrint(st_id) << "\n");
  dout("arg(0) is: " << *st.getOperand(0) << "\n");
  dout("arg(1) is: " << *st.getOperand(1) << "\n");

  if (llvm::isa<llvm::PointerType>(st.getOperand(0)->getType())) {
    // Store from ptr
    // auto dest = omap.getObject(st.getOperand(1));
    auto dest = omap.getValue(st.getOperand(1));
    dout("Got ptr dest of: " << dest << " : " << ValPrint(dest) <<
      "\n");
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
        dout("No object for store dest: " << dest << " : " <<
          ValPrint(dest) << "\n");
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
      dout("No object for store dest: " << dest << " : " <<
        ValPrint(dest) << "\n");
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

  auto gep_id = omap.getValue(&gep);
  auto src_offs = getGEPOffs(omap, gep);
  auto src_id = omap.getValue(gep.getOperand(0));

  dout("id gep_id: " << ValPrint(gep_id) << "\n");
  dout("  src_offs: " << src_offs << "\n");
  dout("  src_id: " << src_id << "\n");

  cg.add(ConstraintType::Copy,
      gep_id,
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

  auto dest_id = omap.getValue(&bcast);
  auto src_id = omap.getValue(bcast.getOperand(0));

  assert(llvm::isa<llvm::PointerType>(bcast.getOperand(0)->getType()));

  /*
  addConstraintForType(ConstraintType::Copy, cg, omap,
      bcast.getType()->getContainedType(0), dest_id, src_id, false);
      */
  cg.add(ConstraintType::Copy, dest_id, src_id);
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

static void idExtractInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  auto &extract_inst = llvm::cast<llvm::ExtractValueInst>(inst);
  if (llvm::isa<llvm::PointerType>(extract_inst.getType())) {
    cg.add(ConstraintType::Copy,
        omap.getValue(&extract_inst),
        ObjectMap::AggregateValue);
  } else if (llvm::isa<llvm::IntegerType>(extract_inst.getType())) {
    cg.add(ConstraintType::Copy,
        ObjectMap::IntValue,
        ObjectMap::AggregateValue);
  }
}

static void idInsertInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  auto &insert_inst = llvm::cast<llvm::InsertValueInst>(inst);
  auto src_val = insert_inst.getOperand(1);

  if (llvm::isa<llvm::PointerType>(src_val->getType())) {
    cg.add(ConstraintType::Copy,
        ObjectMap::AggregateValue,
        omap.getValue(src_val));
  } else if (llvm::isa<llvm::IntegerType>(src_val->getType())) {
    cg.add(ConstraintType::Copy,
        ObjectMap::AggregateValue,
        ObjectMap::IntValue);
  }
}
//}}}

// Instruction parsing helpers {{{
static void processBlock(const UnusedFunctions &unused_fcns,
    ConstraintGraph &cg, CFG &cfg,
    std::map<const llvm::BasicBlock *, CFG::CFGid> &seen,
    ObjectMap &omap, const llvm::BasicBlock &BB, CFG::CFGid parent_id) {
  // If this block is never used, don't process it! -- This includes adding
  //   edges from/to parents
  if (!unused_fcns.isUsed(&BB)) {
    return;
  }

  // Make sure we don't follow the same block twice
  auto seen_it = seen.find(&BB);

  if (seen_it != std::end(seen)) {
    // Add an edge from my parent to me
    cfg.addPred(seen_it->second, parent_id);
    return;
  }




  // Extract the basic block info about this block for our CFG (required for
  //    computing SSA on address-taken variables)
  // This is for the basic block, not a value, so it's "anon"
  CFG::CFGid next_id = cfg.nextNode(&BB);
  seen.emplace(&BB, next_id);
  // Add an edge from our parent, if we have one
  if (parent_id.valid()) {
    cfg.addPred(next_id, parent_id);
  // Or if we don't have a parent denote that we should get edges from calls
  } else {
    dout("Adding CFGFunctionStart for: " << omap.getObject(BB.getParent()) <<
      "\n");
    dout("Function is : " << BB.getParent()->getName() << "\n");

    // If this is main, we add an edge from glbl_init to it
    if (BB.getParent()->getName() == "main") {
      // cfg.addEdge(CFG::CFGArgvBegin, CFG::ArgvEnd);
      cfg.addPred(next_id, CFG::CFGArgvEnd);
      cfg.addPred(next_id, CFG::CFGInit);
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
            cfg.addPred(ret_id, next_id);
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
      case llvm::Instruction::InsertValue:
        idInsertInst(cg, omap, inst);
        break;
      default:
        assert(!is_ptr && "Unknown instruction has a pointer return type!");
    }
  }

  // Process all of our successor blocks (In DFS order)
  std::for_each(succ_begin(&BB), succ_end(&BB),
      [&cg, &cfg, &seen, &omap, next_id, &unused_fcns]
      (const llvm::BasicBlock *succBB) {
    processBlock(unused_fcns, cg, cfg, seen, omap, *succBB, next_id);
  });
}

void scanFcn(const UnusedFunctions &unused_fcns, ConstraintGraph &cg, CFG &cfg,
    ObjectMap &omap, const llvm::Function &fcn) {
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
  std::map<const llvm::BasicBlock *, CFG::CFGid> seen;
  processBlock(unused_fcns, cg, cfg, seen, omap,
      fcn.getEntryBlock(), CFG::CFGid::invalid());
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
      dout("Have structtype: " << st << "\n");
      omap.addStructInfo(st);
    });
  }

  // Id all globals
  std::for_each(M.global_begin(), M.global_end(),
      [&omap](const llvm::Value &glbl) {
    // addValues (note valueS) takes into account structure fields.  We do this
    // for values on global variables because they can be statically accessed by
    // constant expressions.  ObjectS are also treated this way, and are treated
    // for staic/heap allocations
    assert(llvm::isa<llvm::PointerType>(glbl.getType()));
    auto type = glbl.getType()->getContainedType(0);
    omap.addValues(type, &glbl);
    omap.addObjects(type, &glbl);
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
        [&omap, &fcn](const llvm::Argument &arg) {
      if (llvm::isa<llvm::StructType>(arg.getType())) {
        llvm::dbgs() << "FIXME: Possibly missed ptsto in arg struct???\n";
      }

      if (llvm::isa<llvm::PointerType>(arg.getType())) {
        omap.addValue(&arg);
        if (fcn.getName() == "main") {
          omap.addObject(&arg);
        }
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
        // Do we reserve values for the pointer inst here?
        omap.addValue(&inst);
      }

      // Add alloc objects
      if (auto AI = llvm::dyn_cast<llvm::AllocaInst>(&inst)) {
        // add objectS in a similar manner to add valueS in glbls
        auto type = AI->getAllocatedType();

        omap.addObjects(type, AI);
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

      if (isMalloc(&inst)) {
        // Once again, add objectS
        auto inferred_type = findLargestType(omap, inst);
        if_debug(
          dout("Finding type for malloc: " << inst << "\n");
          if (llvm::isa<llvm::StructType>(inferred_type)) {
            dout("Found struct type\n");
          } else {
            dout("Found non-struct type\n");
          });
        omap.addObjects(inferred_type, &inst);
      }
    });
  }

  return false;
  //}}}
}

bool SpecSFS::createConstraints(ConstraintGraph &cg, CFG &cfg, ObjectMap &omap,
    const llvm::Module &M, const UnusedFunctions &unused_fcns) {
  //{{{

  // Special Constraints {{{
  // First, we set up some constraints for our special constraints:
  // Universal value
  cg.add(ConstraintType::AddressOf, ObjectMap::UniversalValue,
      ObjectMap::UniversalValue);

  // Constraints for argv
  // The argv value always points to the argv object
  cg.add(ConstraintType::AddressOf, ObjectMap::ArgvValue,
      ObjectMap::ArgvObjectValue);

  // Constraints for ctype values
  cg.add(ConstraintType::AddressOf, ObjectMap::CTypeObject,
      ObjectMap::CTypeObject);


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
    auto type = glbl.getType();

    // Okay, so I need to do this for each global...
    auto val_id = omap.getValue(&glbl);
    auto obj_id = omap.getObject(&glbl);

    dout("Adding glbl constraint for: " << glbl << "\n");

    addGlobalConstraintForType(ConstraintType::AddressOf, cg, omap,
      type, val_id, obj_id, true);

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
      if (glbl.hasInitializer() &&
          llvm::isa<llvm::ConstantAggregateZero>(glbl.getInitializer())) {
        dout("Global Zero Initializer: " << glbl.getName() << "\n");
        llvm::dbgs() << "FIXME: Ignoring zero initializer: Andersen's assumes"
          << " its a univeral value, and that breaks struct stuff, so I'm "
          " (unsoundly) ignoring\n";
        /*
        cg.add(ConstraintType::Copy, omap.getValue(&glbl),
            ObjectMap::NullValue);
        */
      } else {
        llvm::dbgs() << "Warning, skipping global init for unknown global "
          "initializer, to be consistent with andersens...\n";
        /*
        dout("NO GLOBAL INITIALIZER: " << glbl.getName() << "\n");
        cg.add(ConstraintType::Copy, omap.getObject(&glbl),
            ObjectMap::UniversalValue);
        cg.add(ConstraintType::Copy, omap.getValue(&glbl),
            ObjectMap::UniversalValue);
        */
      }
    }
  });
  //}}}

  // Functions {{{
  // Now that we've dealt with globals, move on to functions
  for (auto &fcn : M) {
    // NOTE: In the absense of profile info isUsed reports conservatively
    if (unused_fcns.isUsed(fcn)) {
      auto obj_id = omap.getObject(&fcn);
      // graph.associateNode(obj_id, &fcn);

      cg.add(ConstraintType::AddressOf,
          getValueUpdate(cg, omap, &fcn),
          obj_id);

      // Functions are constant pointers
      addConstraintForConstPtr(cg, omap, fcn);
    }
  }

  // Now we deal with the actual internals of functions
  for (auto &fcn : M) {
    // NOTE: In the absense of profile info isUsed reports conservatively
    if (unused_fcns.isUsed(fcn)) {
      // If this function may be used externally -- aka I can't track the uses
      //   of it
      if (!fcn.hasLocalLinkage() || analyzeUsesOfFunction(fcn)) {
        // If it appears that the function is unused, I'm going to add some fake
        // constraints for the arguments, to stop HU from combining them
        // together with other arguments that aren't filled until after HU
        // We add in a fake address of to make the node unusable.
        //
        // Don't add unused function pieces for main or llvm.dbg.declare,
        //    they are special, and don't need to be tracked
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
      if (!fcn.isDeclaration() && !Andersens::isMallocCall(&fcn)) {
        // Any arguments for main have their own objects...
        if (fcn.getName() == "main") {
          std::for_each(fcn.arg_begin(), fcn.arg_end(),
              [&cg, &omap, &cfg](const llvm::Argument &arg) {
            if (llvm::isa<llvm::PointerType>(arg.getType())) {
              // NOTE: We don't have to add value for type because structures
              //   cannot be passed into main... I think
              // NOTE: We also need to add a new phony object which
              //   argv[i]/envp[i] pts to
              auto obj_id = omap.getObject(&arg);
              auto val_id = omap.getValue(&arg);
              cg.add(ConstraintType::AddressOf, val_id, obj_id);

              // We store the data at argv into our argv** ptr
              auto st_id = omap.createPhonyID();
              cg.add(ConstraintType::Store, st_id,
                ObjectMap::ArgvValue, val_id);

              auto node_id = cfg.nextNode();

              cfg.addPred(node_id, CFG::CFGArgvBegin);

              addCFGStore(cfg, &node_id, st_id);

              cfg.addPred(CFG::CFGArgvEnd, node_id);
            }
          });
        }

        scanFcn(unused_fcns, cg, cfg, omap, fcn);
      // There is no body...
      } else {
        // FIXME:
        // This used to create constraints for function arguments, but for
        //   external calls... This caused issue with not being able to get the
        //   UniversalValue set from Andersens... so I'm once again unsoundly
        //   removing it
        if (llvm::isa<llvm::PointerType>(
              fcn.getFunctionType()->getReturnType())) {
          auto ret_id = omap.getReturn(&fcn);
          cg.add(ConstraintType::Copy, ret_id,
              ObjectMap::UniversalValue);
        }

        // Add a universal constraint for each pointer arg
        std::for_each(fcn.arg_begin(), fcn.arg_end(),
            [&cg, &omap, &fcn](const llvm::Argument &arg) {
          if (llvm::isa<llvm::PointerType>(arg.getType())) {
            // Must deal with pointers passed into extrernal fcns
            // We add a phony store object?, so we can uniquely refer
            //   to this later

            dout("fcn is: " << fcn.getName() << "\n");
            dout("arg is: " << arg << "\n");

            auto arg_id = omap.getValue(&arg);
            // must deal w/ memory object passed into external fcns
            cg.add(ConstraintType::Copy, arg_id,
              ObjectMap::UniversalValue);
          }
        });

        if (fcn.getFunctionType()->isVarArg()) {
          if_debug(
            auto st_id = omap.createPhonyID();
            dout("Creating universal value vararg pass to id: " <<
                st_id << "\n"));
          cg.add(ConstraintType::Copy, omap.getVarArg(&fcn),
              ObjectMap::UniversalValue);
        }
      }
    }
  }
  //}}}

  return false;
  //}}}
}


bool SpecSFS::addIndirectCalls(ConstraintGraph &cg, CFG &cfg,
    const Andersens &aux, const IndirFunctionInfo *dyn_indir_info,
    ObjectMap &omap) {
  //{{{
  identifyAUXFcnCallRetInfo(cfg, omap, aux, dyn_indir_info);

  if_debug(
    dout("initial unused functions are: ");
    std::for_each(cfg.unused_function_begin(), cfg.unused_function_end(),
        [&cg, &cfg, &omap] (CFG::const_unused_function_iterator::reference pr) {
      const llvm::Function *fcn =
          llvm::cast<llvm::Function>(omap.valueAtID(pr.first));
      dout(" " << fcn->getName());
    });
    dout("\n"));

  // We iterate each indirect call in the DUG
  // to add the indirect info to the constraint map:
  std::for_each(cfg.indirect_cbegin(), cfg.indirect_cend(),
      [this, &cg, &cfg, &aux, &omap]
      (const std::pair<ConstraintGraph::ObjID, CFG::CFGid> &pair) {
    const llvm::CallInst *ci =
      llvm::cast<llvm::CallInst>(omap.valueAtID(pair.first));
    llvm::CallSite CS(const_cast<llvm::CallInst *>(ci));
    auto fptr = CS.getCalledValue();

    // Add an edge from this call to the fcn
    CFG::CFGid call_id = pair.second;
    CFG::CFGid ret_id = cfg.getCallSuccessor(call_id);

    // Get the functon call/ret info for this function:
    auto &cr_vec = cfg.getCallRetInfo(omap.getValue(fptr));
    for (auto pr : cr_vec) {
      CFG::CFGid aux_call_id = pr.first;
      CFG::CFGid aux_ret_id = pr.second;

      // Now add edges
      cfg.addPred(aux_call_id, call_id);
      cfg.addPred(ret_id, aux_ret_id);
    }

    bool is_ext = false;
    // Its possible I cannot Identify the indir function from the list andersens
    //   gave me.  I ignore it then, and that /should/ be safe?
    // I'm also only following indirect functions for functions I can precisely
    //   identify, otherwise things get too nasty
    if (cfg.haveIndirFcn(pair.first)) {
      const std::vector<ConstraintGraph::ObjID> &fcnTargets =
        cfg.getIndirFcns(pair.first);
      // Also, add constraints if needed
      std::for_each(std::begin(fcnTargets), std::end(fcnTargets),
            [this, &aux, &cg, &cfg, &omap, &CS, &ci, &is_ext]
            (const ConstraintGraph::ObjID fcn_id) {
        const llvm::Function *fcn = omap.getFunction(fcn_id);
        /*
        llvm::dbgs() << "Checking fcnTarget for: " << *ci <<
            " : " << fcn->getName() << "\n";
        */

        // If this is an allocation we need to note that in our structures...
        if (AllocInfo::fcnIsMalloc(fcn) &&
            llvm::isa<llvm::PointerType>(ci->getType())) {
          llvm::dbgs() << "Have indirect malloc call\n";
          // If its a malloc, we don't add constriants for the call, we
          //   instead pretend the call is actually a addressof operation
          //
          // Unfortunately, malloc doesn't tell us what size strucutre is
          //   being allocated, we infer this information from its uses
          auto &inst = *ci;
          auto inferred_type = findLargestType(omap, inst);

          auto dest_id = omap.getValue(&inst);
          // Add objects for this call...
          // llvm::dbgs() << "adding indirect objects: " << inst << "\n";

          std::vector<ObjectMap::ObjID> alias_ptsto;
          auto &aux_ptsto = aux.getPointsTo(ci);
          // Convert aux_ptsto to our ptsto
          for (int32_t i : aux_ptsto) {
            alias_ptsto.push_back(aux_to_obj_[i]);
          }

          omap.addObjectsAlias(inferred_type, &inst, alias_ptsto);
          auto src_obj_id = omap.getObject(&inst);
          /*
          llvm::dbgs() << "  got source object: " << src_obj_id << "\n";

          llvm::dbgs() << "  Malloc addAddressForType(" << dest_id << ", " <<
              src_obj_id << ")\n";
              */
          addConstraintForType(ConstraintType::AddressOf, cg, omap,
              inferred_type, dest_id, src_obj_id, false);

          is_ext = true;
        // If its not an allocation, add normal constraints
        } else {
          // llvm::dbgs() << "  Non-malloc call!\n";
          is_ext |= addConstraintsForCall(cg, cfg, omap, CS,
            const_cast<llvm::Function *>(fcn), nullptr);
        }

        cfg.removeUnusedFunction(cg, fcn_id);
      });
    // If we can't figure out the target, add a universal constraint
    } else {
      is_ext = true;
      std::for_each(CS.arg_begin(), CS.arg_end(),
          [&cfg, &cg, &omap] (const llvm::Use &arg) {
        auto val = arg.get();
        if (llvm::isa<llvm::PointerType>(val->getType())) {
          auto node_id = omap.createPhonyID();
          auto arg_id = omap.getValue(val);
          cg.add(ConstraintType::Copy, node_id, arg_id,
            ObjectMap::UniversalValue);
        }
      });

      // Also return the universal value from the function
      if (llvm::isa<llvm::PointerType>(CS.getType())) {
        auto node_id = omap.createPhonyID();
        auto arg_id = omap.getValue(CS.getInstruction());
        cg.add(ConstraintType::Copy, node_id, arg_id,
            ObjectMap::UniversalValue);
      }
    }

    if (is_ext) {
      // Add edge through this point due to inserted constraint?
      cfg.addPred(ret_id, call_id);
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
        (const ConstraintGraph::ObjID &ins_id) {
      dout("Got value: " << ValPrint(ins_id) << "\n");

      ConstraintGraph::ObjID fcn_id = ins_id;

      // If this function has a body
      // FIXME: This requires 2 searches of the map... could make 1
      if (cfg.hasFunctionStart(fcn_id)) {
        CFG::CFGid fcn_call_id =
          cfg.getFunctionStart(fcn_id);
        cfg.addPred(fcn_call_id, call_id);

        // Not all functions have returns... (noreturn functions)... yeah
        if (cfg.hasFunctionReturn(fcn_id)) {
          CFG::CFGid fcn_ret_id = cfg.getFunctionReturn(fcn_id);

          cfg.addPred(ret_id, fcn_ret_id);
        }
      } else {
        cfg.addPred(ret_id, call_id);
      }


      cfg.removeUnusedFunction(cg, fcn_id);
    });
  });

  if_debug(
      dout("Post insert unused functions are: ");
      std::for_each(cfg.unused_function_begin(), cfg.unused_function_end(),
          [&cfg, &omap] (CFG::const_unused_function_iterator::reference pr) {
        const llvm::Function *fcn =
            llvm::cast<llvm::Function>(omap.valueAtID(pr.first));
        dout(" " << fcn->getName());
      });
      dout("\n"));

  std::for_each(cfg.unused_function_begin(), cfg.unused_function_end(),
      [&cg, &cfg, &omap]
      (const std::pair<ObjectMap::ObjID, std::vector<ConstraintGraph::ConsID>> &pr) {  // NOLINT
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

