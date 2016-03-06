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
#include <stack>
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

// FIXME: Shouldn't be here...
std::stack<void *> __g_st;

// Using AUX with CFG helpers {{{
ObjectMap::ObjID getConstValue(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Constant *c) {
  if (llvm::isa<const llvm::ConstantPointerNull>(c) ||
      llvm::isa<const llvm::UndefValue>(c)) {
    return ObjectMap::NullValue;
  } else if (auto gv = dyn_cast<llvm::GlobalValue>(c)) {
    return omap.getValue(gv);
  } else if (auto ce = dyn_cast<llvm::ConstantExpr>(c)) {
    switch (ce->getOpcode()) {
      case llvm::Instruction::GetElementPtr:
        {
          // Need to calc offset here...
          // But this encounters obj vs value issues...

          auto offs = LLVMHelper::getGEPOffs(omap, *ce);
          auto obj_id = getConstValue(cg, omap, ce->getOperand(0));

          // Now we need to get a gep to convert this value to the gep'd offset:
          auto gep_id = omap.getConstRep(c);
          cg.add(ConstraintType::Copy,
              gep_id,
              obj_id,
              offs);

          return gep_id;
        }
      case llvm::Instruction::IntToPtr:
        // assert(0);
        // llvm::dbgs() << "getConstValue returns IntValue\n";
        return ObjectMap::IntValue;
      case llvm::Instruction::PtrToInt:
        llvm::dbgs() << __LINE__ << ": getConstValue returns IntValue\n";
        assert(0);
        return ObjectMap::IntValue;
      case llvm::Instruction::BitCast:
        {
          auto base_id = getConstValue(cg, omap, ce->getOperand(0));
          // Now, if we cast from a struct to a non-struct, we need to merge
          //   nodes...

          /* FIXME: THis is unsound????
          auto base_type = ce->getOperand(0)->getType();
          assert(llvm::isa<llvm::PointerType>(base_type));
          auto base_nptr_type = base_type->getContainedType(0);

          // if the base type is a struct ptr, and the dest type is not the same
          //   type merge all the points-tos together
          auto st = dyn_cast<llvm::StructType>(base_nptr_type);
          if (st != nullptr && base_type != ce->getType()) {
            auto ret_id = omap.createPhonyID(c);

            // First, get the structure type
            auto &si = omap.getStructInfo(st);

            // llvm::dbgs() << "Adding grouping constraints for struct cast: "
            //     << *c << "\n";

            // Then, for each field in the struct type
            for (size_t i = 0; i < si.numSizes(); i++) {
              // Copy that field's ptsto set into the new resultant pointer
              cg.add(ConstraintType::Copy, ret_id, base_id, i);
            }

            // Now, return the structure type
            return ret_id;
          }
          */

          return base_id;
        }
      default:
        llvm::errs() << "Const Expr not yet handled: " << *ce << "\n";
        llvm_unreachable(0);
    }
  } else if (llvm::isa<llvm::ConstantInt>(c)) {
    // llvm::dbgs() << __LINE__ << ": getConstValue returns IntValue\n";
    // assert(0);
    return ObjectMap::IntValue;
  } else {
    llvm::errs() << "Const Expr not yet handled: " << *c << "\n";
    llvm_unreachable("Unknown constant expr ptr");
  }
}

ObjectMap::ObjID getValue(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Value *val) {
  if (auto c = dyn_cast<const llvm::Constant>(val)) {
    if (!llvm::isa<llvm::GlobalValue>(c)) {
      return getConstValue(cg, omap, c);
    }
  }

  auto id = omap.getValueRep(val);

  // graph.associateNode(id, id);

  return id;
}

// Returns true if unknown, false if known
bool traceInt(const llvm::Value *val, std::set<const llvm::Value *> &src,
    std::map<const llvm::Value *, bool> &seen) {
  auto it = seen.find(val);

  if (it != std::end(seen)) {
    return it->second;
  }

  seen[val] = false;

  // llvm::dbgs() << "  Tracing: " << *val << "\n";

  int32_t opcode = 0;

  std::vector<const llvm::Value *> ops;

  if (llvm::isa<llvm::Argument>(val) || llvm::isa<llvm::ConstantInt>(val)) {
    seen[val] = true;
    return true;
  } else if (auto ce = dyn_cast<llvm::ConstantExpr>(val)) {
    opcode = ce->getOpcode();
    for (size_t i = 0; i < ce->getNumOperands(); i++) {
      ops.push_back(ce->getOperand(i));
    }
  } else if (auto ins = dyn_cast<llvm::Instruction>(val)) {
    opcode = ins->getOpcode();
    for (size_t i = 0; i < ins->getNumOperands(); i++) {
      ops.push_back(ins->getOperand(i));
    }
  } else {
    llvm_unreachable("Unknown Integeral type");
  }

  bool ret;

  switch (opcode) {
    case llvm::Instruction::Invoke:
    case llvm::Instruction::FPToUI:
    case llvm::Instruction::FPToSI:
    case llvm::Instruction::ICmp:
    case llvm::Instruction::FCmp:
    case llvm::Instruction::Call:
    case llvm::Instruction::VAArg:
    case llvm::Instruction::ExtractElement:
    case llvm::Instruction::ExtractValue:
      ret = true;
      break;

    case llvm::Instruction::PtrToInt:
      src.insert(ops[0]);
      ret = false;
      break;

    // For loads, do what we can...
    case llvm::Instruction::Load:
      {
        // If its a load from a global
        if (auto gv = dyn_cast<llvm::GlobalVariable>(ops[0])) {
          auto gi = gv->getInitializer();

          ret = traceInt(gi, src, seen);
        } else {
          auto li = cast<llvm::LoadInst>(val);

          auto addr = ops[0];
          const llvm::Value *source = nullptr;

          auto bb = li->getParent();
          for (auto &ins : *bb) {
            if (auto si = dyn_cast<llvm::StoreInst>(&ins)) {
              if (si->getPointerOperand() == addr) {
                source = si->getOperand(0);
              }
            } else if (auto ld = dyn_cast<llvm::LoadInst>(&ins)) {
              if (ld == li) {
                break;
              }
            }
          }

          if (source != nullptr) {
            ret = traceInt(source, src, seen);
          } else {
            ret = true;
          }
        }
        break;
      }
    // 1 input arith operations, trace the addr
    case llvm::Instruction::Shl:
    case llvm::Instruction::LShr:
    case llvm::Instruction::AShr:
    case llvm::Instruction::Trunc:
    case llvm::Instruction::ZExt:
    case llvm::Instruction::SExt:
    case llvm::Instruction::BitCast:
      {
        auto op_type = ops[0]->getType();

        if (llvm::isa<llvm::IntegerType>(op_type)) {
          ret = traceInt(ops[0], src, seen);
        } else {
          assert(opcode == llvm::Instruction::BitCast);
          ret = true;
        }

        break;
      }
    // Binary arithmetic
    case llvm::Instruction::Add:
    case llvm::Instruction::Sub:
    case llvm::Instruction::Mul:
    case llvm::Instruction::UDiv:
    case llvm::Instruction::SDiv:
    case llvm::Instruction::URem:
    case llvm::Instruction::SRem:
    case llvm::Instruction::And:
    case llvm::Instruction::Or:
    case llvm::Instruction::Xor:
      ret = traceInt(ops[0], src, seen) &&
                 traceInt(ops[1], src, seen);
      break;

    case llvm::Instruction::PHI:
      ret = false;
      for (auto op : ops) {
        auto op_type = op->getType();
        if (llvm::isa<llvm::IntegerType>(op_type)) {
          ret |= traceInt(op, src, seen);
        } else if (llvm::isa<llvm::PointerType>(op_type)) {
          src.insert(op);
        } else {
          ret = true;
        }
      }
      break;

    // Select...
    case llvm::Instruction::Select:
      ret = traceInt(ops[0], src, seen) &&
                 traceInt(ops[1], src, seen);
      break;

    default:
      ret = true;
      llvm_unreachable("Unsupported trace_int operand");
  }

  seen[val] = ret;
  return ret;
}

ObjectMap::ObjID getGlobalInitializer(ConstraintGraph &, CFG &,
    ObjectMap &, const llvm::GlobalValue &glbl) {
  ObjectMap::ObjID ret = ObjectMap::UniversalValue;

  auto name = glbl.getName();

  if (name == "stdout") {
    ret = ObjectMap::StdIOValue;
  } else if (name == "stderr") {
    ret = ObjectMap::StdIOValue;
  } else if (name == "stdin") {
    ret = ObjectMap::StdIOValue;
  } else if (name == "environ") {
    ret = ObjectMap::ArgvValue;
  }

  return ret;
}

void identifyAUXFcnCallRetInfo(CFG &cfg,
    ObjectMap &omap, SpecAnders &aux,
    const IndirFunctionInfo *dyn_info) {
  // If we don't have dynamic info, or we're explicitly not using it:
  if (!do_spec || dyn_info == nullptr || !dyn_info->hasInfo()) {
    // We iterate each indirect call in the CFG
    // to add the indirect info to the constraint map:
    std::for_each(cfg.indirect_cbegin(), cfg.indirect_cend(),
        // We take different arguments, depending on if we're debugging...
        [&cfg, &aux, &omap]
        (const std::pair<ConstraintGraph::ObjID, CFG::CFGid> &pair) {
      const llvm::CallInst *ci =
        cast<llvm::CallInst>(omap.valueAtID(pair.first));


      llvm::CallSite CS(const_cast<llvm::CallInst *>(ci));

      auto fptr = CS.getCalledValue();

      // This is the andersen's node for this element
      auto &ptsto = aux.getPointsTo(omap.getValue(fptr));

      if_debug(
        dout("have ptsto:");
        for (auto obj_idid : ptsto) {
          dout(" " << obj_id);
        }
        dout("\n"));

      for (ObjectMap::ObjID obj_id : ptsto) {
        // FIXME: Andersen's reports the function as pointing to the universal
        //   set... or all unknown functions... I'm ignoring this for now, but
        //   will fix if needed
        if (obj_id == ObjectMap::UniversalValue) {
          /*
          llvm::dbgs() << "FIXME: Function points to universal value..."
            " Ignoring the universal value ptr\n";
          */
          continue;
        }

        auto fcn = dyn_cast_or_null<llvm::Function>(omap.valueAtID(obj_id));

        // Ignore nullptrs to values, they don't point to callable functions
        if (fcn == nullptr) {
          continue;
        }

        ObjectMap::ObjID fcn_id =
          omap.getObject(fcn);

        cfg.addIndirFcn(pair.first, fcn_id);
      }
    });
  // If we do have dynamic info, just ignore the andersens info, and use ours
  } else {
    std::for_each(cfg.indirect_cbegin(), cfg.indirect_cend(),
        // We take different arguments, depending on if we're debugging...
        [&cfg, &omap, &dyn_info]
        (const std::pair<ConstraintGraph::ObjID, CFG::CFGid> &pair) {
      const llvm::CallInst *cci =
        cast<llvm::CallInst>(omap.valueAtID(pair.first));

      auto ci = const_cast<llvm::CallInst *>(cci);

      llvm::CallSite CS(const_cast<llvm::CallInst *>(ci));
      auto fptr = CS.getCalledValue();

      // llvm::dbgs() << "Getting info for target: " << *ci << "\n";
      auto fcn_targets = dyn_info->getTargets(ci);

      // Manage speculative assumptions:
      {
        PtstoSet pts_ids;
        for (auto fcn : fcn_targets) {
          pts_ids.set(omap.getObject(fcn));
        }

        /*
        llvm::dbgs() << "call: " << *ci << "\n";
        llvm::dbgs() << "  Has indir fcns:";
        for (auto fcn : fcn_targets) {
          llvm::dbgs() << " " << fcn->getName();
        }
        llvm::dbgs() << "\n";
        */

        // ci.getOperand(0) -> the value being called
        // llvm::dbgs() << "Have fptr: " << *fptr << "\n";
        std::unique_ptr<Assumption> ptsto_aspn(new PtstoAssumption(
              cast<llvm::Value>(fptr), pts_ids));

        // addSpeculativeAssumption(std::move(ptsto_aspn));
      }

      for (auto fcn : fcn_targets) {
        auto fcn_id = omap.getObject(cast<llvm::Function>(fcn));

        cfg.addIndirFcn(pair.first, fcn_id);
      }
    });
  }
}

// Functions/Variables helping me track internal values {{{
/*
ObjectMap::ObjID getValueReturn(ObjectMap &omap, const llvm::Value *v) {
  return ObjectMap::getOffsID(omap.getValue(v), CallReturnPos);
}
*/
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

void addCFGStore(CFG &graph, CFG::CFGid *store_cfg_id,
    ConstraintGraph::ObjID store_obj_id) {
  // Well, stuff here
  dout("addStore called with store_cfg_id: " << *store_cfg_id << "\n");
  auto node = &graph.getNode(*store_cfg_id);

  // If this is a m-node (np-node), then it has a store, and we need to make a
  // new node
  if (node->m()) {
    CFG::CFGid next_id = graph.nextNode();
    dout("store cfg_id: " << next_id << "\n");

    graph.addPred(next_id, *store_cfg_id);

    // Advance the id
    *store_cfg_id = next_id;

    dout("Have np-node, added new id: " << *store_cfg_id << "\n");
    node = &graph.getNode(*store_cfg_id);
  }
  dout("Setting M for store_cfg_id: " << *store_cfg_id << "\n");
  node->setM();
  // Need to also set R for store nodes.... bleh
  node->setR();

  dout("Adding def for: " << *store_cfg_id << "\n");
  graph.addDef(*store_cfg_id, store_obj_id);
}

void addGlobalInit(ConstraintGraph &cg, CFG &cfg, ObjectMap &omap,
    ObjectMap::ObjID src_id, ObjectMap::ObjID dest_id) {
  auto glbl_id = omap.createPhonyID();

  // Add the store to the constraint graph
  cg.add(ConstraintType::Store, glbl_id, src_id, dest_id);

  // Do CFG setup:
  // create new CFG node for this store
  // Attach it between GlblStoreInit and StartNode
  auto cfg_id = cfg.nextNode();
  if_debug_enabled(auto chk_cfg_id = cfg_id);

  // Connect cfg_id within the graph
  // The global store goes between globalinit and init
  cfg.addPred(cfg_id, CFG::CFGGlobalInit);
  cfg.addPred(CFG::CFGInit, cfg_id);

  addCFGStore(cfg, &cfg_id, glbl_id);

  // Assert cfg_node didn't change
  assert(cfg_id == chk_cfg_id);
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
    dout("Adding direct call to: " << fcn->getName() << " id: "
        << omap.getObject(fcn) << "\n");
    // cfg.addCallsite(call_id, omap.getFunction(fcn), next_id);
    cfg.addCallsite(call_id, omap.getObject(fcn), next_id);
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
      F->getName() == "llvm.memset" || F->getName() == "llvm.va_copy" ||
      F->getName() == "system" || F->getName() == "link" ||
      F->getName() == "setuid" || F->getName() == "setgid" ||
      F->getName() == "seteuid" || F->getName() == "setegid" ||
      F->getName() == "geteuid" || F->getName() == "getegid" ||
      F->getName() == "getpid" ||
      F->getName() == "setvbuf" || F->getName() == "setbuf" ||
      F->getName() == "ftruncate" ||
      F->getName() == "closedir" || F->getName() == "putenv" ||
      F->getName() == "kill" || F->getName() == "frexp" ||
      F->getName() == "__isnan" ||
      F->getName() == "strcmp" || F->getName() == "strncmp" ||
      F->getName() == "execl" || F->getName() == "execlp" ||
      F->getName() == "execle" || F->getName() == "execv" ||
      F->getName() == "execvp" || F->getName() == "chmod" ||
      F->getName() == "puts" || F->getName() == "write" ||
      F->getName() == "open" || F->getName() == "create" ||
      F->getName() == "open64" || F->getName() == "lstat64" ||
      F->getName() == "truncate" || F->getName() == "chdir" ||
      F->getName() == "mkdir" || F->getName() == "rmdir" ||
      F->getName() == "read" || F->getName() == "pipe" ||
      F->getName() == "wait" || F->getName() == "time" ||
      F->getName() == "stat" || F->getName() == "fstat" ||
      F->getName() == "lstat" || F->getName() == "strtod" ||
      F->getName() == "strtof" || F->getName() == "strtold" ||
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
      F->getName() == "setfscreatecon" || F->getName() == "strspn" ||
      F->getName() == "strcspn" ||
      F->getName() == "bsearch" || F->getName() == "clock" ||
      // End jump fixme
      F->getName() == "getpagesize" ||
      // FIXME: gcc stuffs?
      F->getName() == "obstack_free" || F->getName() == "_obstack_newchunk" ||
      F->getName() == "_obstack_begin" ||
      F->getName() == "_obstack_memory_used" ||
      // END GCC Stuffs
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
      F->getName() == "iconv" || F->getName() == "iconv_close" ||
      F->getName() == "access" || F->getName() == "dup" ||
      F->getName() == "strncpy" || F->getName() == "__isoc99_sscanf" ||
      F->getName() == "select" || F->getName() == "ctime" ||
      F->getName() == "fsync" || F->getName() == "utime" ||
      F->getName() == "mblen" || F->getName() == "perror" ||
      F->getName() == "lseek64" || F->getName() == "perror" ||
      F->getName() == "signal" || F->getName() == "stat64" ||
      F->getName() == "isatty" || F->getName() == "stat64" ||
      F->getName() == "vsnprintf" || F->getName() == "__isoc99_fscanf" ||
      F->getName() == "pclose" || F->getName() == "getrusage" ||
      F->getName() == "getrlimit" || F->getName() == "setrlimit" ||
      F->getName() == "cielf" || F->getName() == "floorf" ||
      F->getName() == "sleep" || F->getName() == "setupterm" ||
      F->getName() == "tigetnum" || F->getName() == "times" ||
      F->getName() == "sysconf" || F->getName() == "ceilf" ||
      F->getName() == "setlinebuf" || F->getName() == "putchar" ||
      F->getName() == "getopt_long" || F->getName() == "getopt") {
    return true;
  }

  // Okay, how do we handle jmp functions?
  // Uhhh, well... we... um, you-know
  // For anders we do nothing
  // For sfs, we need to add edges to the CFG
  // -- based on results from anders (where the jmps may come from or go)
  //    Similar to indirect functions:
  //
  // For each setjmp:
  //    Make a mapping of obj-ids to setjmps
  //    Also ensure that each setjmp is a boundry with a new cfgnode
  //
  // for each longjmp do a lookup in the setjmp map
  //   Add an edge from each longjmp to each setjmp
  // FIXME: well, this is actually ugly, wrt the cfg
  //
  // Broken down:
  // Responsibility here:
  //  setjmp:
  //    Alert the CFG of a setjmp, to be filled in later
  //    Break the node after the setjmp, as the entry for any incoming
  //      longjmps
  if (F->getName() == "_setjmp" ||
      F->getName() == "__sigsetjmp") {
    // Add new node to cfg (to be the dest of any longjmps about this node)
    auto succ_id = cfg.nextNode();
    cfg.addPred(succ_id, *next_id);
    *next_id = succ_id;

    // Add succ_id into the cfg longjump list
    cfg.addSetjmp(succ_id, CS.getArgument(0));
    return true;
  }

  //  longjmp:
  //    Alert the CFG of a longjmp here
  //    Break the node, remove any cfg edges going out of the prior node, to be
  //    replaced with longjmp destinations
  if ( F->getName() == "siglongjmp" ||
      F->getName() == "longjmp") {
    auto succ_id = cfg.nextNode();

    cfg.addLongjmp(*next_id, CS.getArgument(0));

    *next_id = succ_id;
    return true;
  }

  // Ignore memset, it modifies the array, but not the ptsto
  if (F->getName().find("llvm.memset") == 0 ||
      F->getName().find("llvm.bswap") == 0 ||
      F->getName().find("llvm.expect") == 0 ||
      F->getName().find("llvm.pow") == 0) {
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
      auto first_arg = getValue(cg, omap, CS.getArgument(0));
      auto second_arg = getValue(cg, omap, CS.getArgument(1));
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
      if (auto st = dyn_cast<llvm::StructType>(type)) {
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
      F->getName() == "textdomain"  || F->getName() == "mkdtemp"  ||
      F->getName() == "memchr"  ||
      F->getName() == "bindtextdomain") {
    const llvm::FunctionType *FTy = F->getFunctionType();
    if (FTy->getNumParams() > 0 &&
        llvm::isa<llvm::PointerType>(FTy->getParamType(0))) {
      cg.add(ConstraintType::Copy,
          omap.getValue(CS.getInstruction()),
          getValue(cg, omap, CS.getArgument(0)));
      return true;
    }
  }

  // Result = Arg3
  if (F->getName() == "gcvt") {
    cg.add(ConstraintType::Copy,
        omap.getValue(CS.getInstruction()),
        getValue(cg, omap, CS.getArgument(2)));
    return true;
  }
  // term info stuffs...
  if (F->getName() == "tigetstr" ||
      F->getName() == "tparm") {
    // Set the output to be terminfo static data
    cg.add(ConstraintType::AddressOf,
        omap.getValue(CS.getInstruction()),
        ObjectMap::TermInfoObject);
    return true;
  }

  // c stdlib returning fcns
  if (F->getName() == "strerror" ||
      F->getName() == "gmtime" ||
      F->getName() == "readdir") {
    // Set the output to be terminfo static data
    cg.add(ConstraintType::AddressOf,
        omap.getValue(CS.getInstruction()),
        ObjectMap::CLibObject);
    return true;
  }

  // strtoll maddness
  // stores arg0 in arg1
  if (F->getName() == "strtoll" ||
      F->getName() == "strtoul" ||
      F->getName() == "strtol") {
    auto st_id = omap.createPhonyID();
    cg.add(ConstraintType::Store, st_id,
        getValue(cg, omap, CS.getArgument(0)),
        getValue(cg, omap, CS.getArgument(1)));
    return true;
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

  // FIXME: Instead treat it as an alloc, unclear if this is best
  /*
  // getenv -- This is currently linked to argv...
  if (F->getName() == "getenv") {
    cg.add(ConstraintType::AddressOf,
      omap.getValue(CS.getInstruction()),
      ObjectMap::ArgvValueObject);
    return true;
  }
  */
  if (F->getName() == "opendir") {
    cg.add(ConstraintType::AddressOf,
      omap.getValue(CS.getInstruction()),
      ObjectMap::DirObject);
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
          getValue(cg, omap, CS.getArgument(1)));
      return true;
    }
  }

  if (F->getName() == "gettext") {
    const llvm::FunctionType *FTy = F->getFunctionType();
    if (FTy->getNumParams() > 0 &&
        llvm::isa<llvm::PointerType>(FTy->getParamType(0))) {
      cg.add(ConstraintType::Copy,
          omap.getValue(CS.getInstruction()),
          getValue(cg, omap, CS.getArgument(0)));
      return true;
    }
  }

  if (F->getName() == "freopen") {
    const llvm::FunctionType *FTy = F->getFunctionType();
    if (FTy->getNumParams() > 0 &&
        llvm::isa<llvm::PointerType>(FTy->getParamType(2))) {
      cg.add(ConstraintType::Copy,
          omap.getValue(CS.getInstruction()),
          getValue(cg, omap, CS.getArgument(2)));
      return true;
    }
  }

  // FIXME: There must be a better way to do this?
  if (F->getName() == "ioctl") {
    auto va = CS.getArgument(2);

    auto st_id = omap.createPhonyID();
    auto dest_val = getValue(cg, omap, va);
    cg.add(ConstraintType::Store, st_id,
        ObjectMap::IoctlValue,
        dest_val);
    addCFGStore(cfg, next_id, st_id);
    return true;
  }

  llvm::Instruction *I = CS.getInstruction();
  if (I) {
    if (llvm::IntrinsicInst *II = dyn_cast<llvm::IntrinsicInst>(I)) {
      llvm::Intrinsic::ID IID = II->getIntrinsicID();
      if (IID == llvm::Intrinsic::vastart) {
        // llvm::Function *ParentF = I->getParent()->getParent();
        assert(I->getParent()->getParent()->getFunctionType()->isVarArg()
            && "va_start in non-vararg function!");
        llvm::dbgs() << "FIXME: ???VARARG???\n";
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
      cg.add(ConstraintType::Store, getValue(cg, omap, ThrFunc),
          getValue(cg, omap, Arg), CallFirstArgPos);
      addCFGStore(cfg, next_id,
          omap.getOffsID(getValue(cg, omap, Arg), CallFirstArgPos));
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
          getValue(cg, omap, CS.getInstruction()->getOperand(1)));
      return true;
    }
  }

  // Don't worry about debug declare...
  if (F->getName() == "llvm.dbg.declare" ||
      F->getName() == "llvm.dbg.value") {
    return true;
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
  int32_t offset = 1;
  /*
  dbg << "In glbl init cons\n";
  dbg << "glbl init cons dest: (" << dest << ") " <<
    ValPrint(dest) << "\n";
  */
  // llvm::dbgs() << "Entry constant: " << *C << ", dest: " << dest << "\n";
  // Simple case, single initializer
  if (C->getType()->isSingleValueType()) {
    if (llvm::isa<llvm::PointerType>(C->getType())) {
      auto const_id = getConstValue(cg, omap, C);
      /*
      dbg << "Adding global init for: (" << dest << ") " <<
          ValPrint(dest) << " to (" << const_id << ") " << ValPrint(const_id)
          << "\n";
      */

      /*
      llvm::dbgs() << "Assigning constant: " << *C << "\n";
      llvm::dbgs() << "  To: " << dest << " from: " << const_id << "\n";
      */
      addGlobalInit(cg, cfg, omap, const_id, dest);
    }

  // Initialized to null value
  } else if (C->isNullValue()) {
      // NOTE: We ignore this, because null values don't point to anything...
    // dbg << "Glbl init on: (" << dest << ") " << ValPrint(dest) << "\n";
    if (llvm::isa<llvm::StructType>(C->getType())) {
      // FIXME: Offset = sizeof struct type?
      auto &si = omap.getStructInfo(cast<llvm::StructType>(C->getType()));
      offset = si.size();
    } else {
    }
  // Set to some other defined value
  } else if (!llvm::isa<llvm::UndefValue>(C)) {
    // It must be an array, or struct
    assert(llvm::isa<llvm::ConstantArray>(C) ||
        llvm::isa<llvm::ConstantStruct>(C) ||
        llvm::isa<llvm::ConstantDataSequential>(C));

    /*
    dbg << "Adding STRUCT global init for: (" << dest << ") " <<
      ValPrint(dest) << "\n";
    */
    // For each field of the initializer, add a constraint for the field
    // This is done differently for structs than for array
    if (auto cs = dyn_cast<llvm::ConstantStruct>(C)) {
      // llvm::dbgs() << "Splitting struct constant: " << *C << "\n";
      // Need to reset to 0, because we're adding fields
      offset = 0;
      std::for_each(cs->op_begin(), cs->op_end(),
          [&offset, &cg, &cfg, &cs, &omap, &dest]
          (const llvm::Use &field) {
        auto field_cons = cast<const llvm::Constant>(field);
        offset += addGlobalInitializerConstraints(cg, cfg, omap,
          omap.getOffsID(dest, offset), field_cons);
      });
    } else {
      if_debug_enabled(int32_t first_offs = -1);

      // llvm::dbgs() << "Arraying constant: " << *C << "\n";
      std::for_each(C->op_begin(), C->op_end(),
          [&offset, &cg, &cfg, &cs, &omap, &dest
          if_debug_enabled(, &first_offs)]
          (const llvm::Use &field) {
        auto field_cons = cast<const llvm::Constant>(field);
        offset = addGlobalInitializerConstraints(cg, cfg, omap,
          dest, field_cons);

        if_debug_enabled(
          if (first_offs < 0) {
            first_offs = offset;
          });

        // Each array field should have the same size
        /*
        llvm::dbgs() << "offset: " << offset << ", first_offs " << first_offs <<
            "\n";
        */
        // assert(offset == first_offs);
      });
    }
  } else {
    // Undef values get no ptsto
    auto type = C->getType();
    while (auto at = dyn_cast<llvm::ArrayType>(type)) {
      type = at->getContainedType(0);
    }

    if (auto st = dyn_cast<llvm::StructType>(type)) {
      auto &si = omap.getStructInfo(st);
      offset = si.size();
    } else {
      offset = 1;
    }
  }

  return offset;
}

[[ gnu::unused ]]
static void addConstraintForConstPtr(ConstraintGraph &cg,
    ObjectMap &omap, const llvm::GlobalValue &glbl) {
  bool inserted = false;
  for (auto I = glbl.use_begin(), E = glbl.use_end(); I != E; ++I) {
    auto use = *I;

    // If this use is a constant expr, we can add the constraint now
    if (auto *CE = dyn_cast<const llvm::ConstantExpr>(use)) {
      // If its a ptr to int, add an "intvalue"
      if (CE->getOpcode() == llvm::Instruction::PtrToInt) {
        if (!inserted) {
          /*
          llvm::dbgs() << __LINE__ <<
            ": addConstForConstPtr returns IntValue\n";
          */
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
    } else if (auto SI = dyn_cast<llvm::StoreInst>(*UI)) {
      if (&val == SI->getOperand(1)) {
        return false;

      // This pointer is being stored
      } else if (SI->getOperand(1)) {
        return true;
      }
    } else if (auto GEP = dyn_cast<llvm::GetElementPtrInst>(*UI)) {
      if (analyzeUsesOfFunction(*GEP)) {
        return true;
      }
    } else if (auto CI = dyn_cast<llvm::CallInst>(*UI)) {
      llvm::CallSite CS((llvm::CallInst *)CI);
      // Can't use std::for_each because of return
      for (size_t i = 0, e = CS.arg_size(); i < e; i++) {
        if (CS.getArgument(i) == &val) {
          return true;
        }
      }
    } else if (auto CE = dyn_cast<llvm::ConstantExpr>(*UI)) {
      if (CE->getOpcode() == llvm::Instruction::GetElementPtr ||
          CE->getOpcode() == llvm::Instruction::BitCast) {
        if (analyzeUsesOfFunction(*CE)) {
          return true;
        }
      } else {
        return true;
      }
    } else if (dyn_cast<llvm::ICmpInst>(*UI) != nullptr) {
      return true;
    } else {
      return true;
    }
  }

  return false;
}

/*
static void addConstraintsForNonInternalLinkage(ConstraintGraph &,
    ObjectMap &,
    const llvm::Function &) {
  // FIXME: Need to do this:
  // If we have a non-internal linkage, then we:
  //   Store the universal value in all of the input arguments
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
*/


static void addConstraintsForIndirectCall(ConstraintGraph &cg, ObjectMap &omap,
    llvm::CallSite &CS) {
  auto &called_val = *CS.getCalledValue();

  if (llvm::isa<llvm::InlineAsm>(&called_val)) {
    llvm::errs() << "WARNING: Ignoring inline asm!\n";
    return;
  }

  // We take care of adding the constriants to the cfg in addCFGCallsite, called
  //    from addConstraintsForCall() before this

  // We don't actually add the constraints, because SFS does not need them to
  //   create indirect edges (although Andersens does)
  // Instead we alert the constraint graph of the appropriate nodes, and allow
  //   it to fill in the information later.
  // Create a ret node:
  auto call_id = omap.getValueRep(CS.getInstruction());
  bool is_pointer =
    llvm::isa<llvm::PointerType>(CS.getInstruction()->getType());
  std::vector<ObjectMap::ObjID> args;
  std::for_each(CS.arg_begin(), CS.arg_end(),
      [&CS, &cg, &omap, &args] (const llvm::Use &arg) {
    // args.push_back(omap.createPhonyID(arg.get()));
    auto val_id = getValue(cg, omap, arg.get());
    /*
    if (val_id == ObjectMap::IntValue) {
      llvm::dbgs() << "Got int value for arg: " << arg.get() << " in call: " <<
          *CS.getInstruction() <<"\n";
    }
    */
    args.push_back(val_id);
  });
  auto callee_id = omap.getValue(&called_val);
  cg.addIndirectCall(call_id, is_pointer, callee_id, std::move(args));
}

static void addConstraintsForDirectCall(ConstraintGraph &cg, ObjectMap &omap,
    llvm::CallSite &CS, llvm::Function *F) {
  // llvm::dbgs() << "Add direct call: " << *CS.getInstruction() << "\n";
  // If this call returns a pointer
  assert(F != nullptr);
  if (llvm::isa<llvm::PointerType>(F->getFunctionType()->getReturnType())) {
    auto val = omap.getValueRep(CS.getInstruction());

    // If the function that's called also returns a pointer
    // Add a copy from the return value into this value
    /*
    llvm::dbgs() << "CS is: " << *CS.getInstruction() << "\n";
    llvm::dbgs() << "cv is: " << *CS.getCalledValue() << "\n";
    llvm::dbgs() << "Fcn is: " << *F << "\n";
    */
    auto ret_val = omap.getReturnRep(F);
    cg.add(ConstraintType::Copy, val, ret_val);

  // The callsite returns a non-pointer, but the function returns a
  // pointer value, treat it as a pointer cast to a non-pointer
  } else if (
      llvm::isa<llvm::PointerType>(F->getFunctionType()->getReturnType())) {
    // The call now aliases the universal value
    llvm::dbgs() << "FIXME: Direct call returns universal value: " <<
        CS.getInstruction() << "\n";
    auto ret_id = omap.getReturnRep(F);
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
      auto arg_id = getValue(cg, omap, *ArgI);

      /*
      cg.add(ConstraintType::Copy, node_id, arg_id,
          ObjectMap::UniversalValue);
      */

      llvm::dbgs() << "WARNING: adding universal store which doesn't "
       "jive w/ andersen's for fcn args: " << *CS.getCalledValue() << "\n";
      cg.add(ConstraintType::Store, node_id, ObjectMap::UniversalValue,
          arg_id);
    }

    // If we expect a pointer type
    if (llvm::isa<llvm::PointerType>(FargI->getType())) {
      // And we get one!
      if (llvm::isa<llvm::PointerType>((*ArgI)->getType())) {
        // llvm::dbgs() << "Adding arg copy!\n";
        // llvm::dbgs() << "Callinst: " << *CS.getInstruction() << "\n";
        auto node_id = omap.createPhonyID();
        auto dest_id = getValue(cg, omap, FargI);
        auto src_id = getValue(cg, omap, *ArgI);
        /*
        if (src_id == ObjectMap::UniversalValue ||
            src_id == ObjectMap::IntValue) {
          llvm::dbgs() << "  src is: " << ValPrint(src_id) << "for call: " <<
            *CS.getInstruction() << "\n";
        }
        */

        if (node_id.val() == 191679) {
          llvm::dbgs() << "Adding to arg: " << FargI->getParent()->getName() <<
            ": " << FargI->getName() << "\n";
          llvm::dbgs() << "dest: " << dest_id << "\n";
          llvm::dbgs() << "src_id is: " << src_id << ": " << *ArgI->get() <<
            "\n";
        }
        cg.add(ConstraintType::Copy, node_id, src_id, dest_id);
      // But if its not a pointer type...
      } else {
        // Map it to int stores (i2p)
        auto node_id = omap.createPhonyID();
        auto dest_id = getValue(cg, omap, FargI);

        /*
        llvm::dbgs() << "instr is: " << *CS.getInstruction() << "\n";
        llvm::dbgs() << "dest is: " << F->getName() << "\n";
        llvm::dbgs() << "ArgI is: " << (*ArgI)->getName() << "\n";
        llvm::dbgs() << "FargI is: " << FargI->getName() << "\n";
        */

        llvm::dbgs() << __LINE__ <<
          ": addConstForDirectCall returns IntValue\n";
        cg.add(ConstraintType::Copy, node_id, ObjectMap::IntValue,
            dest_id);
      }
    }
  }

  // Varargs magic :(
  if (F->getFunctionType()->isVarArg()) {
    for (; ArgI != ArgE; ++ArgI) {
      if (llvm::isa<llvm::PointerType>((*ArgI)->getType())) {
        cg.add(ConstraintType::Copy, omap.getVarArg(F),
            getValue(cg, omap, *ArgI));
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

    auto ce = dyn_cast<llvm::ConstantExpr>(callee);

    if (ce) {
      if (ce->getOpcode() == llvm::Instruction::BitCast) {
        F = dyn_cast<llvm::Function>(ce->getOperand(0));
      }
    }
  }

  // If this is direct && is external
  if (F && F->isDeclaration()) {
    // Add it as an external function
    // llvm::dbgs() << "External call\n";
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
    assert(next_id != nullptr && "Adding constraints for indirect call in "
        "indirect call resolution");
    addConstraintsForIndirectCall(cg, omap, CS);
  }

  return true;
}
//}}}

// Helpers for individual instruction constraints {{{
static void idRetInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  auto &ret = cast<const llvm::ReturnInst>(inst);

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

  auto returned_id = getValue(cg, omap, src);
  /*
  llvm::dbgs() << "Adding return for " << F->getName() << " to id: " <<
    omap.getReturn(F) << " from " << returned_id << "\n";
  */
  cg.add(ConstraintType::Copy,
      omap.getReturn(F), returned_id);
}

static void addGlobalConstraintForType(ConstraintType ctype,
    ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Type *type, ObjectMap::ObjID dest,
    ObjectMap::ObjID src_obj, bool strong) {

  // All globals are (implicitly) pointers, I'm evaluating based off of the
  //   contained type
  type = type->getContainedType(0);

  // Strip wrapping arrays
  while (auto at = dyn_cast<llvm::ArrayType>(type)) {
    // Arrays invalidate strength
    strong = false;
    type = at->getContainedType(0);
  }


  if (auto st = dyn_cast<llvm::StructType>(type)) {
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
  while (auto at = dyn_cast<llvm::ArrayType>(type)) {
    // Arrays invalidate strength
    strong = false;
    type = at->getContainedType(0);
  }

  if (auto st = dyn_cast<llvm::StructType>(type)) {
    auto &si = omap.getStructInfo(st);

    // Only create one addressof object, per alloc
    if (ctype == ConstraintType::AddressOf) {
      auto cons_id = cg.add(ctype, dest, src_obj, 0);
      auto &cons = cg.getConstraint(cons_id);
      // Update strength as appropriate
      cons.setStrong(strong && si.fieldStrong(0));
    } else {
      for (size_t i = 0; i < si.numSizes(); i++) {
        // Add an addr of to this offset
        dout("Adding AddressOf for struct.  Dest: " << dest << ", src "
          << src_obj << " + " << i << "\n");
        auto cons_id = cg.add(ctype, dest, src_obj, i);
        auto &cons = cg.getConstraint(cons_id);
        // Update strength as appropriate
        cons.setStrong(strong && si.fieldStrong(i));
      }
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
    /*
    llvm::dbgs() << "Have malloc call: " <<
      inst.getParent()->getParent()->getName() << ":" << inst << "\n";
    */
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

    /*
    if (auto st = dyn_cast<llvm::StructType>(inferred_type)) {
      auto &si = omap.getStructInfo(st);
      llvm::dbgs() << inst.getParent()->getParent()->getName() <<
        ": Have Struct type: " << st->getName() << " and size: "
        << si.size() << "\n";
      auto &max_si = omap.getMaxStructInfo();
      llvm::dbgs() << "For reference, max struct info is: " <<
        max_si.size() << " with struct: " <<
        max_si.type()->getName() << "\n";
    } else {
      llvm::dbgs() << inst.getParent()->getParent()->getName() <<
        ": Nonstruct malloc!\n";
    }
    */
    addConstraintForType(ConstraintType::AddressOf, cg, omap,
        inferred_type, dest_id, src_obj_id, false);

    return false;
  }

  return addConstraintsForCall(cg, cfg, omap, CS, CS.getCalledFunction(),
      bb_id);
}

static void idAllocaInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  auto &alloc = cast<const llvm::AllocaInst>(inst);

  // If the thing we're allocating is a structure... then we need to handle
  //   addressof for all sub-fields!
  auto type = alloc.getAllocatedType();

  auto dest_id = getValue(cg, omap, &alloc);
  auto src_obj_id = omap.getObject(&alloc);

  addConstraintForType(ConstraintType::AddressOf, cg, omap,
      type, dest_id, src_obj_id, true);
}

static void idLoadInst(ConstraintGraph &cg, CFG &cfg, ObjectMap &omap,
    const llvm::Instruction &inst, CFG::CFGid next_id) {
  auto &ld = cast<const llvm::LoadInst>(inst);

  auto dest_id = getValue(cg, omap, ld.getOperand(0));

  if (llvm::isa<llvm::PointerType>(ld.getType())) {
    auto ld_id = getValue(cg, omap, &ld);

    if_debug(auto cons_id =) cg.add(ConstraintType::Load, ld_id,
        dest_id,
        ld_id);

    dout("Adding load (" << ld_id << ") " << inst << " to cons: " <<
      cons_id << "\n");

    // Add this to the uses
    addCFGLoad(cfg, next_id, ld_id);
  } else if (auto ptr_t =
      dyn_cast<llvm::PointerType>(ld.getOperand(0)->getType())) {
    if (llvm::isa<llvm::PointerType>(ptr_t->getElementType()) &&
        llvm::isa<llvm::IntegerType>(ld.getType())) {
      // Ld is an int value... those may alias.  So we instead create a
      //   phony id
      auto ld_id = getValue(cg, omap, &ld);

      llvm::dbgs() << __LINE__ << ": Load int into pointer\n";
      cg.add(ConstraintType::Load, ld_id,
          dest_id,
          ObjectMap::IntValue);

      addCFGLoad(cfg, next_id, ld_id);
    }
  } else if (llvm::isa<llvm::StructType>(ld.getType())) {
    llvm::errs() << "FIXME: Unhandled struct load!\n";
  }
}

static void idStoreInst(ConstraintGraph &cg, CFG &cfg, ObjectMap &omap,
    const llvm::Instruction &inst, CFG::CFGid *next_id) {
  auto &st = cast<const llvm::StoreInst>(inst);

  auto st_id = omap.getValue(&st);

  dout("store is: " << ValPrint(st_id) << "\n");
  dout("arg(0) is: " << *st.getOperand(0) << "\n");
  dout("arg(1) is: " << *st.getOperand(1) << "\n");

  auto dest_type = dyn_cast<llvm::PointerType>(st.getOperand(1)->getType());

  if (llvm::isa<llvm::PointerType>(st.getOperand(0)->getType())) {
    // Store from ptr
    // auto dest = omap.getObject(st.getOperand(1));
    auto dest = getValue(cg, omap, st.getOperand(1));
    dout("Got ptr dest of: " << dest << " : " << ValPrint(dest) <<
      "\n");
    cg.add(ConstraintType::Store,
        st_id,
        getValue(cg, omap, st.getOperand(0)),
        dest);
  } else if (llvm::ConstantExpr *ce =
      dyn_cast<llvm::ConstantExpr>(st.getOperand(0))) {
    // If we just cast a ptr to an int then stored it.. we can keep info on it
    if (ce->getOpcode() == llvm::Instruction::PtrToInt) {
      // auto dest = omap.getObject(st.getOperand(1));
      auto dest = getValue(cg, omap, st.getOperand(1));
      if (dest == ObjectMap::NullValue) {
        // If this is not an object, store to the value
        dest = getValue(cg, omap, st.getOperand(1));
        llvm::dbgs() << "No object for store dest: " << dest << " : " <<
          ValPrint(dest) << "\n";
      }
      cg.add(ConstraintType::Store,
          st_id,
          getValue(cg, omap, st.getOperand(0)),
          dest);
    // Uhh, dunno what to do now
    } else {
      llvm::errs() << "FIXME: Unhandled constexpr case!\n";
    }
  // put int value into the int pool
  } else if (llvm::isa<llvm::IntegerType>(st.getOperand(0)->getType()) &&
      llvm::isa<llvm::PointerType>(st.getOperand(1)->getType())) {
    if (!llvm::isa<llvm::IntegerType>(dest_type->getContainedType(0))) {
      // auto dest = omap.getObject(st.getOperand(1));
      auto dest = getValue(cg, omap, st.getOperand(1));
      if (dest == ObjectMap::NullValue) {
        // If this is not an object, store to the value
        dest = getValue(cg, omap, st.getOperand(1));
        dout("No object for store dest: " << dest << " : " <<
          ValPrint(dest) << "\n");
      }

      llvm::dbgs() << __LINE__ << ": Store int into pointer: " <<
        st << "\n";
      cg.add(ConstraintType::Store,
          st_id,
          ObjectMap::IntValue,
          dest);
    } else {
      /*
      llvm::dbgs() << "Skipping Universal Cons for store to int *: " << st <<
        "\n";
      */
      // NOTE: We must return here, because we didn't acutlaly add a store!
      return;
    }
  // Poop... structs
  } else if (llvm::isa<llvm::StructType>(st.getOperand(0)->getType())) {
    llvm::errs() << "FIXME: Ignoring struct store\n";
    /*
    cg.add(ConstraintType::Store, st_id,
        omap.getValue(st.getOperand(1)),
        ObjectMap::AgregateNode);
        */
  } else {
    // Floats are stored, but not in graph...
    if (!st.getOperand(0)->getType()->isFloatTy() &&
        !st.getOperand(0)->getType()->isDoubleTy()) {
      // Didn't add it to the graph?
      llvm::errs() << "FIXME: Not adding store object to graph?: "
          << st << "\n";
    }
    return;
  }

  // We have to create a new objID to uniquely identify this store...
  addCFGStore(cfg, next_id, st_id);
}

static void idGEPInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  auto &gep = cast<const llvm::GetElementPtrInst>(inst);

  auto gep_id = omap.getValue(&gep);
  auto src_offs = LLVMHelper::getGEPOffs(omap, gep);
  auto src_id = getValue(cg, omap, gep.getOperand(0));

  dout("id gep_id: " << ValPrint(gep_id) << "\n");
  dout("  src_offs: " << src_offs << "\n");
  dout("  src_id: " << src_id << "\n");

  /*
  static size_t gep_count = 0;
  gep_count++;
  if (gep_count % 100000 == 0) {
    assert(0);
  }
  */

  cg.add(ConstraintType::Copy,
      gep_id,
      src_id,
      src_offs);
}

// FIXME: remove?
[[ gnu::unused ]]
static void idP2IInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  // ddevec - FIXME: Could trace through I2P here, by keeping a listing
  //    of i2ps...
  // sfs does this, Andersens doesn't.

  auto val = getValue(cg, omap, inst.getOperand(0));
  // cg.addP2ICast(&inst, val);

  // If this I instruction is only used by I2P instrs, don't make a constraint
  // for it...
  bool non_i2p = false;
  std::for_each(inst.use_begin(), inst.use_end(),
      [&non_i2p] (const llvm::User *use) {
    if (!llvm::isa<llvm::IntToPtrInst>(use)) {
      non_i2p = true;
      /*
      auto inst = cast<llvm::Instruction>(use);
      llvm::dbgs() << "have non-i2p use: " <<
        inst->getParent()->getParent()->getName() << ": " << *use << "\n";
      */
    }
  });

  if (non_i2p) {
    /*
    llvm::dbgs() << __LINE__ << ": p2i pointer into int for: " << inst << "\n";
    */
    llvm::dbgs() << __LINE__ << ": p2i pointer into int\n";
    cg.add(ConstraintType::Copy,
        ObjectMap::IntValue, val);
  }
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

  auto dest_val = omap.getValue(&inst);

  /*
  auto it = cg.findP2ICast(inst.getOperand(0));
  if (it != cg.p2icast_end()) {
    src_val = it->second;
  }
  */

  std::set<const llvm::Value *> src;
  std::map<const llvm::Value *, bool> seen;

  // llvm::dbgs() << "Start trace\n";
  bool has_i2p = traceInt(inst.getOperand(0), src, seen);
  // llvm::dbgs() << "Finish trace\n";
  seen.clear();

  for (auto val : src) {
    cg.add(ConstraintType::Copy,
        dest_val, getValue(cg, omap, val));
  }

  if (has_i2p) {
    // llvm::dbgs() << __LINE__ << ": i2p int into pointer " << inst << "\n";
    cg.add(ConstraintType::Copy,
        dest_val, ObjectMap::IntValue);
  }
}

static void idBitcastInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  auto &bcast = cast<const llvm::BitCastInst>(inst);

  assert(llvm::isa<llvm::PointerType>(inst.getType()));

  // llvm::dbgs() << "bitcast: " << bcast << "\n";
  auto dest_id = omap.getValue(&bcast);
  auto src_id = getValue(cg, omap, bcast.getOperand(0));

  assert(llvm::isa<llvm::PointerType>(bcast.getOperand(0)->getType()));

  /*
  addConstraintForType(ConstraintType::Copy, cg, omap,
      bcast.getType()->getContainedType(0), dest_id, src_id, false);
      */
  cg.add(ConstraintType::Copy, dest_id, src_id);
}

static void idPhiInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  auto &phi = *cast<const llvm::PHINode>(&inst);

  assert(llvm::isa<llvm::PointerType>(phi.getType()));

  // hheheheheh PHI-d
  auto phid = getValue(cg, omap, &phi);

  for (size_t i = 0, e = phi.getNumIncomingValues(); i != e; ++i) {
    cg.add(ConstraintType::Copy, phid,
        getValue(cg, omap, phi.getIncomingValue(i)));
  }
}

static void idSelectInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  auto &select = cast<const llvm::SelectInst>(inst);

  // this inst --> select: op(0) ? op(1) : op(2)

  if (llvm::isa<llvm::PointerType>(select.getType())) {
    auto sid = getValue(cg, omap, &select);

    cg.add(ConstraintType::Copy, sid,
        getValue(cg, omap, select.getOperand(1)));
    cg.add(ConstraintType::Copy, sid,
        getValue(cg, omap, select.getOperand(2)));

  } else if (llvm::isa<llvm::StructType>(select.getType())) {
    llvm::errs() << "FIXME: unsupported select on struct!\n";
  }
}

static void idVAArgInst(ConstraintGraph &, ObjectMap &,
    const llvm::Instruction &) {
  llvm_unreachable("Vaarg not handled yet");
}

static void idExtractInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  auto &extract_inst = cast<llvm::ExtractValueInst>(inst);
  if (llvm::isa<llvm::PointerType>(extract_inst.getType())) {
    cg.add(ConstraintType::Copy,
        omap.getValue(&extract_inst),
        ObjectMap::AggregateValue);
  } else if (llvm::isa<llvm::IntegerType>(extract_inst.getType())) {
    llvm::dbgs() << __LINE__ << ": EXTRACT INT?\n";
    cg.add(ConstraintType::Copy,
        ObjectMap::IntValue,
        ObjectMap::AggregateValue);
  }
}

static void idInsertInst(ConstraintGraph &cg, ObjectMap &omap,
    const llvm::Instruction &inst) {
  auto &insert_inst = cast<llvm::InsertValueInst>(inst);
  auto src_val = insert_inst.getOperand(1);

  if (llvm::isa<llvm::PointerType>(src_val->getType())) {
    cg.add(ConstraintType::Copy,
        ObjectMap::AggregateValue,
        getValue(cg, omap, src_val));
  } else if (llvm::isa<llvm::IntegerType>(src_val->getType())) {
    llvm::dbgs() << __LINE__ << ": INSERT INT?\n";
    cg.add(ConstraintType::Copy,
        ObjectMap::AggregateValue,
        ObjectMap::IntValue);
  }
}
//}}}

// Instruction parsing helpers {{{
void processBlock(const UnusedFunctions &unused_fcns,
    ConstraintGraph &cg, CFG &cfg,
    std::map<const llvm::BasicBlock *, CFG::CFGid> &seen,
    ObjectMap &omap, const llvm::BasicBlock &BB, CFG::CFGid parent_id,
    AssumptionSet &as) {
  // If this block is never used, don't process it! -- This includes adding
  //   edges from/to parents
  if (do_spec && !unused_fcns.isUsed(&BB)) {
    as.add(std::unique_ptr<Assumption>(
          new DeadCodeAssumption(const_cast<llvm::BasicBlock *>(&BB))));

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
      cfg.addPred(next_id, CFG::CFGArgvEnd);
      cfg.addPred(next_id, CFG::CFGInit);
    }

    cfg.addFunctionStart(omap.getObject(BB.getParent()), next_id);
    /*
    llvm::dbgs() << "Creating Function start (" <<
      BB.getParent()->getName() << "): " <<
      omap.getObject(BB.getParent()) << " -> " << next_id << "\n";
    */
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

          cfg.addFunctionReturn(omap.getObject(BB.getParent()), next_id);

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
      case llvm::Instruction::PtrToInt:
        assert(!is_ptr);
        // FIXME: Is this sound?...
        /*
        idP2IInst(cg, omap, inst);
        */
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
      [&cg, &cfg, &seen, &omap, next_id, &unused_fcns, &as]
      (const llvm::BasicBlock *succBB) {
    processBlock(unused_fcns, cg, cfg, seen, omap, *succBB, next_id, as);
  });
}

void scanFcn(const UnusedFunctions &unused_fcns, ConstraintGraph &cg,
    CFG &cfg, ObjectMap &omap, const llvm::Function &fcn, AssumptionSet &as) {
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
      fcn.getEntryBlock(), CFG::CFGid::invalid(), as);
}
//}}}

//}}}

bool ConstraintPass::identifyObjects(ObjectMap &omap, const llvm::Module &M) {
  //{{{
  // Okay, we need to identify all possible objects within the module, then
  //   insert them into our object map

  // Identify all used strucutre types...
  {
    std::vector<llvm::StructType *> struct_types;
    M.findUsedStructTypes(struct_types);
    std::for_each(std::begin(struct_types), std::end(struct_types),
        [&omap] (llvm::StructType *st) {
      dout("Have structtype: " << st->getName() << "\n");
      omap.addStructInfo(st);
    });
  }

  // Id all globals
  std::for_each(M.global_begin(), M.global_end(),
      [&omap](const llvm::Value &glbl) {
    assert(llvm::isa<llvm::PointerType>(glbl.getType()));
    auto type = glbl.getType()->getContainedType(0);

    // llvm::dbgs() << "adding global: " << glbl << " to omap!\n";

    omap.addValue(&glbl);
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
      if (auto AI = dyn_cast<llvm::AllocaInst>(&inst)) {
        // add objectS in a similar manner to add valueS in glbls
        auto type = AI->getAllocatedType();

        omap.addObjects(type, AI);
      }

      // Also add values for loads/stores, even if they return int types
      // -- I need the values for unique identifiers later
      if (auto ld = dyn_cast<llvm::LoadInst>(&inst)) {
        if (!llvm::isa<llvm::PointerType>(ld->getType())) {
          omap.addValue(ld);
        }
      }

      if (auto st = dyn_cast<llvm::StoreInst>(&inst)) {
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

bool ConstraintPass::createConstraints(ConstraintGraph &cg, CFG &cfg,
    ObjectMap &omap, const llvm::Module &M, const UnusedFunctions &unused_fcns,
    AssumptionSet &as) {
  //{{{

  // Special Constraints {{{
  // First, we set up some constraints for our special constraints:
  // Universal value
  cg.add(ConstraintType::AddressOf, ObjectMap::UniversalValue,
      ObjectMap::UniversalValue);

  // Constraints for argv
  // The argv value always points to the argv object
  // Do store here...
  {
    cg.add(ConstraintType::AddressOf,
      ObjectMap::ArgvValue, ObjectMap::ArgvValueObject);
    cg.add(ConstraintType::AddressOf,
        ObjectMap::ArgvObject, ObjectMap::ArgvObjectObject);

    auto st_id = omap.createPhonyID();
    cg.add(ConstraintType::Store, st_id,
      ObjectMap::ArgvObject, ObjectMap::ArgvValue);

    auto node_id = cfg.nextNode();

    cfg.addPred(node_id, CFG::CFGArgvBegin);

    addCFGStore(cfg, &node_id, st_id);

    cfg.addPred(CFG::CFGArgvEnd, node_id);
  }

  // Constraints for stdio
  {
    // Create a fileio struct:
    auto obj = omap.createPhonyObjectIDs(M.getTypeByName("struct._IO_FILE"));

    cg.add(ConstraintType::AddressOf,
        ObjectMap::StdIOValue, obj);
  }

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

    dout("Adding glbl constraint for: " << glbl <<
     "(thats val: " << val_id << ", obj: " << obj_id << ")\n");

    addGlobalConstraintForType(ConstraintType::AddressOf, cg, omap,
      type, val_id, obj_id, true);

    // If its a global w/ an initalizer
    // NOTE: We assume we have everything linked together, so the initializer
    // wont be over-written by a library... this may be false in some cases,
    // those should use "definitive initializer"...
    // if (glbl.hasDefinitiveInitializer())
    if (glbl.hasInitializer() &&
        llvm::isa<llvm::ConstantPointerNull>(glbl.getInitializer())) {
      dout("Global Zero Initializer: " << glbl.getName() << "\n");
      // We don't add any ptsto constraints for null value here, because null
      //   value points to nothing...
    } else if (glbl.hasInitializer()) {
      dout("Adding glbl initializer for: " << glbl << "\n");
      // llvm::dbgs() << "Adding glbl initializer for: " << glbl << "\n";
      addGlobalInitializerConstraints(cg, cfg, omap, val_id,
        glbl.getInitializer());
    // Doesn't have initializer
    } else {
      if (glbl.hasInitializer()) {
        llvm::dbgs() << "FIXME: IGNORED GLOBAL INITIALIZER: " <<
          glbl.getName() << "\n";
        // Ugh, how do I handle this guy?
        // Well, we get the constant value out of it
      } else {
        auto glbl_val = getGlobalInitializer(cg, cfg, omap, glbl);

        if (glbl_val == ObjectMap::UniversalValue) {
          llvm::dbgs() << "FIXME: Global Init -- universal value -- global: " <<
            glbl.getName() << "\n";
        }
        /*
        cg.add(ConstraintType::Copy, omap.getValue(&glbl),
            glbl_val);
        */

        // Also store the value into this
        addGlobalInit(cg, cfg, omap, glbl_val,
            omap.getValue(&glbl));
      }
    }
  });
  //}}}

  // Functions {{{
  // Now that we've dealt with globals, move on to functions
  for (auto &fcn : M) {
    // Will analyse function if it do_spec is false, or isUsed is also true
    if (!do_spec || unused_fcns.isUsed(fcn)) {
      auto obj_id = omap.getObject(&fcn);
      // graph.associateNode(obj_id, &fcn);

      cg.add(ConstraintType::AddressOf,
          getValue(cg, omap, &fcn), obj_id);

      // Functions are constant pointers
      // addConstraintForConstPtr(cg, omap, fcn);
    }
  }

  // Now we deal with the actual internals of functions
  for (auto &fcn : M) {
    // NOTE: In the absence of profile info isUsed reports conservatively
    if (!do_spec || unused_fcns.isUsed(fcn)) {
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
            if (llvm::isa<llvm::PointerType>(arg.getType())) {
              auto arg_id = omap.getValue(&arg);
              assert(arg_id != ObjectMap::NullValue);
              assert(arg_id != ObjectMap::NullObjectValue);
              auto id = omap.createPhonyID();

              auto con_id = cg.add(ConstraintType::AddressOf, arg_id, id);
              assert(con_id != ConstraintGraph::ConsID::invalid());
              con_ids.emplace_back(con_id);
            }
          });
        }
      }

      // If this function has a body
      if (!fcn.isDeclaration() && !Andersens::isMallocCall(&fcn)) {
        // Any arguments for main have their own objects...
        if (fcn.getName() == "main") {
          std::for_each(fcn.arg_begin(), fcn.arg_end(),
              [&cg, &omap, &cfg, &as]
              (const llvm::Argument &arg) {
            if (llvm::isa<llvm::PointerType>(arg.getType())) {
              // NOTE: We don't have to add value for type because structures
              //   cannot be passed into main... I think
              // NOTE: We also need to add a new phony object which
              //   argv[i]/envp[i] pts to
              auto val_id = omap.getValue(&arg);
              cg.add(ConstraintType::AddressOf, val_id,
                ObjectMap::ArgvValueObject);
              /*  old argv behavior
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
              */
            }
          });
        }

        scanFcn(unused_fcns, cg, cfg, omap, fcn, as);
      // There is no body... We handle this via external calls?
      } else {
        /*
        if (llvm::isa<llvm::PointerType>(
              fcn.getFunctionType()->getReturnType())) {
          llvm::dbgs() << "FIXME: adding Universal value ret for: " <<
            fcn.getName() << "\n";
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
            llvm::dbgs() << "FIXME: adding Universal value arg for: " <<
              fcn.getName() << ": " << arg << "\n";

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
          llvm::dbgs() << "FIXME: adding Universal value vararg for: " <<
            fcn.getName() << "\n";
          cg.add(ConstraintType::Copy, omap.getVarArg(&fcn),
              ObjectMap::UniversalValue);
        }
      */
      }
    } else if (do_spec && !unused_fcns.isUsed(fcn)) {
      // Add a visit assumption to our assumptions for the entry block of this
      //   function
      auto &bb = fcn.getEntryBlock();

      as.add(std::unique_ptr<Assumption>(
            new DeadCodeAssumption(const_cast<llvm::BasicBlock *>(&bb))));
    }
  }

  // Now that we've identified all of our funcitons, lets fill out any remaining
  // CFG return edges
  for (auto it = cfg.direct_begin(), en = cfg.direct_end();
      it != en; ++it) {
    auto &pr = *it;
    auto entry_id = pr.first;
    auto &fcn_targets = pr.second;

    // For each direct callsite, get the callsite incoming and outgoing edge
    auto callsite_ent = entry_id;
    auto callsite_ret = cfg.getCallSuccessor(entry_id);

    for (auto &target_id : fcn_targets) {
      // Get the target (function) incoming and outgoing edge
      auto target_ent = cfg.getFunctionStart(target_id);
      // callsite_ent -> target_ent
      cfg.addPred(target_ent, callsite_ent);


      if (cfg.hasFunctionReturn(target_id)) {
        auto target_ret = cfg.getFunctionReturn(target_id);

        // target_ret -> callsite_ret
        cfg.addPred(callsite_ret, target_ret);
      }
    }
  }
  //}}}

  return false;
  //}}}
}

// Jumps {{{
void handleJmps(CFG &cfg, SpecAnders &aux, ObjectMap &omap) {
  std::multimap<ObjectMap::ObjID, CFG::CFGid> obj_to_dest;

  // First create a mapping of objid to dest cfgid
  for (auto &pr : cfg.getSetjmps()) {
    auto &ptsto = aux.getPointsTo(omap.getValue(pr.second));
    for (auto obj_id : ptsto) {
      obj_to_dest.emplace(obj_id, pr.first);
    }
  }


  // Now, for each jmp
  for (auto &pr : cfg.getLongjmps()) {
    // Find the objids of that jmpenv
    auto &ptsto = aux.getPointsTo(omap.getValue(pr.second));

    // Now, find all the possible dests
    std::vector<CFG::CFGid> dests;
    for (auto obj_id : ptsto) {
      auto pr = obj_to_dest.equal_range(obj_id);
      for (; pr.first != pr.second; ++pr.first) {
        dests.push_back(pr.first->second);
      }
    }

    std::sort(std::begin(dests), std::end(dests));
    auto it = std::unique(std::begin(dests), std::end(dests));
    dests.erase(it, std::end(dests));

    // Now, for each destination, add a cfg edge
    for (auto &dest_id : dests) {
      // Add an edge from the longjmp (src) to the setjmp (destination)
      cfg.addPred(dest_id, pr.first);
    }
  }
}
//}}}

// NOTE: Also handles sigjmp and longjmps
bool addIndirectCalls(ConstraintGraph &cg, CFG &cfg,
    SpecAnders &aux, const IndirFunctionInfo *dyn_indir_info,
    ObjectMap &omap) {
  //{{{
  identifyAUXFcnCallRetInfo(cfg, omap, aux, dyn_indir_info);

  handleJmps(cfg, aux, omap);

  if_debug(
    dout("initial unused functions are: ");
    std::for_each(cfg.unused_function_begin(), cfg.unused_function_end(),
        [&cg, &cfg, &omap] (CFG::const_unused_function_iterator::reference pr) {
      const llvm::Function *fcn =
          cast<llvm::Function>(omap.valueAtID(pr.first));
      dout(" " << fcn->getName());
    });
    dout("\n"));

  // We iterate each indirect call in the DUG
  // to add the indirect info to the constraint map:
  std::for_each(cfg.indirect_cbegin(), cfg.indirect_cend(),
      [&cg, &cfg, &aux, &omap]
      (const std::pair<ConstraintGraph::ObjID, CFG::CFGid> &pair) {
    const llvm::CallInst *ci =
      cast<llvm::CallInst>(omap.valueAtID(pair.first));
    llvm::CallSite CS(const_cast<llvm::CallInst *>(ci));

    /*
    llvm::dbgs() << "Have call: " << pair.first << " " <<
        FullValPrint(pair.first) << "\n";
    */

    // Add an edge from this call to the fcn
    CFG::CFGid call_id = pair.second;
    CFG::CFGid ret_id = cfg.getCallSuccessor(call_id);

    bool is_ext = false;
    // I'm also only following indirect functions for functions I can precisely
    //   identify, otherwise things get too nasty
    if (cfg.haveIndirFcn(pair.first)) {
      const std::vector<ConstraintGraph::ObjID> &fcnTargets =
        cfg.getIndirFcns(pair.first);

      // llvm::dbgs() << "  has " << fcnTargets.size() << " targets\n";
      // Also, add constraints if needed
      for (ConstraintGraph::ObjID fcn_id : fcnTargets) {
        /*
        llvm::dbgs() << "fcn_id is: " << fcn_id << " val: " <<
            ValPrint(fcn_id, omap) << "\n";
        */
        // const llvm::Function *fcn = omap.getFunction(fcn_id);

        const llvm::Function *fcn =
            dyn_cast_or_null<llvm::Function>(omap.valueAtID(fcn_id));
        /*
        llvm::dbgs() << "Checking fcnTarget for: " << *ci <<
            " : " << fcn->getName() << "\n";
        */
        if (fcn == nullptr) {
          continue;
        }

        /*
        llvm::dbgs() << "obj_id is: " << omap.getObject(omap.valueAtID(fcn_id))
          << " val: " << ValPrint(fcn_id, omap) << "\n";
        llvm::dbgs() << "val_id is: " << omap.getValue(omap.valueAtID(fcn_id))
          << " val: " << ValPrint(fcn_id, omap) << "\n";
        */

        // Add the CFG edges
        // FIXME: Should add assert that the if should only be skipped in
        //   instances of DCE
        if (cfg.hasFunctionStart(fcn_id)) {
          // llvm::dbgs() << "Adding cfg edge!\n";
          auto fcn_start_id = cfg.getFunctionStart(fcn_id);
          cfg.addPred(fcn_start_id, call_id);

          // Some functions (like "error" or "abort" don't return)
          if (cfg.hasFunctionReturn(fcn_id)) {
            // Add edge from fcn ret node->ret
            auto fcn_ret_id = cfg.getFunctionReturn(fcn_id);
            cfg.addPred(ret_id, fcn_ret_id);
          }
        }

        // Add any new constraints
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

          omap.addObjects(inferred_type, &inst);
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
      }
    // If we can't figure out the target, add a universal constraint
    } else {
      // FIXME: Evaluate the soundness of this...
      /*
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
      */
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

    for (auto ins_id : pair.second) {
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
    }
  });

  /*
  if_debug(
      dout("Post insert unused functions are: ");
      std::for_each(cfg.unused_function_begin(), cfg.unused_function_end(),
          [&cfg, &omap] (CFG::const_unused_function_iterator::reference pr) {
        const llvm::Function *fcn =
            cast<llvm::Function>(omap.valueAtID(pr.first));
        dout(" " << fcn->getName());
      });
      dout("\n"));

  std::for_each(cfg.unused_function_begin(), cfg.unused_function_end(),
      [&cg, &cfg, &omap]
      (const std::pair<ObjectMap::ObjID, std::vector<ConstraintGraph::ConsID>> &pr) {  // NOLINT
    const llvm::Function *fcn =
      cast<const llvm::Function>(omap.valueAtID(pr.first));
    addConstraintsForNonInternalLinkage(cg, omap, *fcn);
    for (auto id : pr.second) {
      cg.removeConstraint(id);
    }
  });
  */

  return false;
  //}}}
}

