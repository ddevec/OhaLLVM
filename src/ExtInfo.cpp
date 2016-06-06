/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/ExtInfo.h"


#include <cassert>

#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Instructions.h"
#include "llvm/Module.h"

#include "include/ObjectMap.h"
#include "include/ConstraintGraph.h"
#include "include/ControlFlowGraph.h"

typedef decltype(llvm::Instruction::Mul) Opcode;
typedef ExtInfo::AllocInfo AllocInfo;
typedef ExtInfo::StaticAllocInfo StaticAllocInfo;

char ctype_name[] = "ctype";
char filestruct_name[] = "struct._IO_FILE";
char datetimestruct_name[] = "struct.tm";

char locale_name[] = "locale";
char env_name[] = "env";
char errno_name[] = "errno";
char clib_name[] = "clib";
char dir_name[] = "dir";
char terminfo_name[] = "terminfo";
char datetime_name[] = "datetime_static";
char textdomain_name[] = "textdomain_static";
char gettext_name[] = "gettext_static";

// External helper functions from IdentifyObjects
extern void addCFGStore(CFG &graph, CFG::CFGid *store_cfg_id,
    ConstraintGraph::ObjID store_obj_id);
extern void addCFGLoad(CFG &graph, CFG::CFGid load_id,
    ConstraintGraph::ObjID dest);


// Constraint Helpers {{{
struct NoopCons {
  bool operator()(llvm::ImmutableCallSite &, ObjectMap &,
      ConstraintGraph &, CFG &, CFG::CFGid *) const {
    return true;
  }
};

struct AllocCons {
  bool operator()(llvm::ImmutableCallSite &cs, ObjectMap &omap,
      ConstraintGraph &cg, CFG &, CFG::CFGid *) const {
    auto inst = cs.getInstruction();

    auto dest_id = omap.getValue(inst);

    auto src_obj_id = omap.getObject(inst);

    cg.add(ConstraintType::AddressOf, dest_id, src_obj_id);

    return true;
  }
};

// Non-structure -- for example, strdup, where strs are not structs
struct AllocNSCons {
  bool operator()(llvm::ImmutableCallSite &cs, ObjectMap &omap,
      ConstraintGraph &cg, CFG &, CFG::CFGid *) const {
    auto inst = cs.getInstruction();
    auto dest = omap.getValue(inst);
    auto src = omap.getObject(inst);
    // No type info, can just do simple cg add...
    cg.add(ConstraintType::AddressOf, dest, src);

    return true;
  }
};

template <const char *type_name>
struct AllocTypeCons {
  bool operator()(llvm::ImmutableCallSite &cs, ObjectMap &omap,
      ConstraintGraph &cg, CFG &, CFG::CFGid *) const {
    auto inst = cs.getInstruction();
    auto dest = omap.getValue(inst);
    auto src = omap.getObject(inst);

    // Add constraints for the alloc type...
    cg.add(ConstraintType::AddressOf, dest, src);

    return true;
  }
};

template <size_t arg_num>
struct ReturnCons {
  bool operator()(llvm::ImmutableCallSite &cs, ObjectMap &omap,
      ConstraintGraph &cg, CFG &, CFG::CFGid *) const {
    // The function returns arg(arg_num)
    auto ci = cs.getInstruction();
    auto arg0 = cs.getArgument(arg_num);

    auto ci_id = omap.getValue(ci);
    auto arg0_id = omap.getValueC(arg0);

    // Copy the arg into CI
    cg.add(ConstraintType::Copy, ci_id, arg0_id);

    return true;
  }
};

template <const char *name, const char *type_name>
struct ReturnNamedStructCons {
  bool operator()(llvm::ImmutableCallSite &cs, ObjectMap &omap,
      ConstraintGraph &cg, CFG &, CFG::CFGid *) const {
    // The function returns arg(arg_num)
    auto ci = cs.getInstruction();

    auto ci_id = omap.getValue(ci);
    // ins -> bb -> fcn -> module
    auto named_obj_id = omap.getNamedObject(name);

    // Copy the arg into CI
    cg.add(ConstraintType::AddressOf, ci_id, named_obj_id);

    return true;
  }
};

template <const char *name>
struct ReturnNamedNSCons {
  bool operator()(llvm::ImmutableCallSite &cs, ObjectMap &omap,
      ConstraintGraph &cg, CFG &, CFG::CFGid *) const {
    // The function returns arg(arg_num)
    auto ci = cs.getInstruction();

    auto ci_id = omap.getValue(ci);
    // ins -> bb -> fcn -> module
    auto named_obj_id = omap.getNamedObject(name);

    // Copy the arg into CI
    cg.add(ConstraintType::AddressOf, ci_id, named_obj_id);

    return true;
  }
};

template <size_t src, size_t dest>
struct StoreCons {
  bool operator()(llvm::ImmutableCallSite &cs, ObjectMap &omap,
      ConstraintGraph &cg, CFG &cfg, CFG::CFGid *next_id) const {
    // The function returns arg(arg_num)
    auto st_id = omap.createPhonyID();

    cg.add(ConstraintType::Store, st_id,
        omap.getValueC(cs.getArgument(src)),
        omap.getValueC(cs.getArgument(dest)));
    addCFGStore(cfg, next_id, st_id);

    return true;
  }
};

template <size_t arg_num>
struct ReturnArgOrMallocCons {
  bool operator()(llvm::ImmutableCallSite &cs, ObjectMap &omap,
      ConstraintGraph &cg, CFG &, CFG::CFGid *) const {
    // The function returns arg(arg_num) or allocates a new set of data
    // First, handle the allocation
    // Add objects to the graph
    auto inst = cs.getInstruction();
    auto ci_obj = omap.getObject(inst);
    auto ci_id = omap.getValue(inst);
    cg.add(ConstraintType::AddressOf,
        ci_id, ci_obj);

    auto arg = cs.getArgument(arg_num);
    auto arg_id = omap.getValueC(arg);
    // Now, handle the arg copy
    cg.add(ConstraintType::Copy,
        ci_id, arg_id);

    return true;
  }
};

template <size_t arg_num, const char *name>
struct ReturnArgOrStaticCons {
  bool operator()(llvm::ImmutableCallSite &cs, ObjectMap &omap,
      ConstraintGraph &cg, CFG &, CFG::CFGid *) const {
    // The function returns arg(arg_num) or allocates a new set of data
    // First, handle the static return case
    // Add objects to the graph
    auto inst = cs.getInstruction();
    llvm::dbgs() << "get named: " << name << "\n";
    auto ci_obj = omap.getNamedObject(name);
    auto ci_id = omap.getValue(inst);
    cg.add(ConstraintType::AddressOf,
        ci_id, ci_obj);

    // Now, handle the arg copy
    auto arg = cs.getArgument(arg_num);
    auto arg_id = omap.getValueC(arg);
    cg.add(ConstraintType::Copy,
        ci_id, arg_id);

    return true;
  }
};

struct MemcpyCons {
  bool operator()(llvm::ImmutableCallSite &cs, ObjectMap &omap,
      ConstraintGraph &cg, CFG &cfg, CFG::CFGid *next_id) const {
    auto dest = cs.getArgument(0);
    auto src = cs.getArgument(1);

    auto first_arg = omap.getValueC(dest);
    auto second_arg = omap.getValueC(src);

    auto type = getTypeOfVal(dest);

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
            &merge_id, &cs] (int32_t) {
        auto node_id = cfg.nextNode();
        auto load_dest = omap.createPhonyID();
        // The gep dests have equivalent ptsto as the argumens
        auto load_gep_dest = omap.createPhonyID(cs.getArgument(1));
        auto store_gep_dest = omap.createPhonyID(cs.getArgument(0));
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
};


struct PthreadCreateCons {
  bool operator()(llvm::ImmutableCallSite &cs, ObjectMap &omap,
      ConstraintGraph &cg, CFG &cfg, CFG::CFGid *next_id) const {
    // Need to add an indirect call... and some funky cfg edges

    // pthread_create
    // First, add
    auto callee = cs.getArgument(2);
    auto arg = omap.getValueC(cs.getArgument(3));

    // Just add a call to callee
    // FIXME(ddevec) -- If callee is not a function, this is harder
    auto fcn = cast<llvm::Function>(callee);

    // FIXME(ddevec) -- Return value can somehow be passed... ugh
    // First, make a cfg edge into this function
    auto cur_id = *next_id;
    auto n_id = cfg.nextNode();
    *next_id = n_id;

    cfg.addCallsite(cur_id, omap.getObject(fcn), n_id);

    // CFG flows through this callsite, as well as to the called function(s)
    cfg.addPred(n_id, cur_id);

    // Now, copy arg into the function's argument:
    auto fcn_arg = omap.getValue(&(*fcn->arg_begin()));
    auto node_id = omap.createPhonyID();
    cg.add(ConstraintType::Copy, node_id, arg, fcn_arg);

    return true;
  }
};
//}}}

// AllocSize Helpers {{{
struct NoAllocData {
  std::vector<AllocInfo> operator()(llvm::Module &, llvm::CallSite &,
        ObjectMap &, llvm::Instruction **) const {
    return std::vector<AllocInfo>();
  }
};

template <size_t arg_num>
struct AllocSize {
  std::vector<AllocInfo> operator()(llvm::Module &,
      llvm::CallSite &cs,
      ObjectMap &,
      llvm::Instruction **) const {
    std::vector<AllocInfo> ret;

    auto val = cs.getArgument(arg_num);

    ret.emplace_back(cs.getInstruction(), val, ObjectMap::ObjID::invalid());

    return ret;
  }
};

template <const char *type_name>
struct AllocStruct {
  std::vector<AllocInfo> operator()(llvm::Module &m,
      llvm::CallSite &cs,
      ObjectMap &,
      llvm::Instruction **) const {
    std::vector<AllocInfo> ret;

    auto type = m.getTypeByName(type_name);
    auto type_size_ce = LLVMHelper::calcTypeOffset(m, type, nullptr);

    ret.emplace_back(cs.getInstruction(), type_size_ce,
        ObjectMap::ObjID::invalid());

    return ret;
  }
};

template <size_t arg_num0, size_t arg_num1, Opcode op>
struct AllocSizeOp {
  std::vector<AllocInfo> operator()(llvm::Module &,
      llvm::CallSite &cs,
      ObjectMap &,
      llvm::Instruction **) const {
    std::vector<AllocInfo> ret;

    auto ci = cs.getInstruction();

    auto arg0 = cs.getArgument(arg_num0);
    auto arg1 = cs.getArgument(arg_num1);

    auto mul = llvm::BinaryOperator::Create(
        llvm::Instruction::Mul, arg0, arg1, "", ci);

    ret.emplace_back(ci, mul, ObjectMap::ObjID::invalid());

    return ret;
  }
};

template <const char *name, const char *type_name>
struct AllocNamedStruct {
  // We know the size -- can gep from type_name
  std::vector<AllocInfo> operator()(llvm::Module &m,
      llvm::CallSite &cs,
      ObjectMap &omap,
      llvm::Instruction **) const {
    std::vector<AllocInfo> ret;

    auto type = m.getTypeByName(type_name);
    auto type_size_ce = LLVMHelper::calcTypeOffset(m, type, nullptr);

    // We have the size of the type, its returned in the return value
    auto ci = cs.getInstruction();

    auto static_id = omap.getNamedObject(name);

    ret.emplace_back(ci, type_size_ce, static_id);

    return ret;
  }
};

template <const char *type_name, size_t size>
struct AllocNamedSize {
  // We know the size -- can gep from type_name
  std::vector<AllocInfo> operator()(llvm::Module &m,
      llvm::CallSite &cs,
      ObjectMap &omap,
      llvm::Instruction **) const {
    std::vector<AllocInfo> ret;
    auto i64_type = llvm::IntegerType::get(m.getContext(), 64);

    // We have the size of the type, its returned in the return value
    auto ci = cs.getInstruction();

    auto static_id = omap.getNamedObject(type_name);

    auto size_ce = llvm::ConstantInt::get(i64_type, size);

    ret.emplace_back(ci, size_ce, static_id);

    return ret;
  }
};

static llvm::Instruction *add_checked_strlen(
    llvm::Module &m,
    llvm::Value *str_val,
    llvm::Instruction **insert_after) {
  auto i8_ptr_type = llvm::PointerType::get(
      llvm::IntegerType::get(m.getContext(), 8), 0);
  auto i64_type = llvm::IntegerType::get(m.getContext(), 64);

  // If the argument is nullptr then we return alloc, otherwise do nothing
  // Add a check for nullptr, and a BB in that case:
  auto strlen_fcn = m.getFunction("strlen");
  // I may have to create an external linkage for this in some instances...
  //   ugh
  assert(strlen_fcn != nullptr);

  // This means we add a check for nullptr
  // Then if not nullptr we do math
  // We phi together after math
  // Finally, we return the info needed for the alloc function

  // If ci is nullptr, don't do the following, otherwise, do it
  // First, split the BB after the CI
  auto pins = *insert_after;
  auto bb_prev = pins->getParent();
  auto bb_it = llvm::BasicBlock::iterator(pins);
  // advance after insertafter
  bb_it = std::next(bb_it);

  // Split
  auto bb_succ = bb_prev->splitBasicBlock(bb_it);
  // Then delete the terminator in pred BB
  auto old_term = bb_prev->getTerminator();
  old_term->eraseFromParent();

  // Add a icmp
  auto icmp = new llvm::ICmpInst(*bb_prev, llvm::CmpInst::Predicate::ICMP_EQ,
      str_val, llvm::ConstantPointerNull::get(i8_ptr_type));

  auto bb_strlen = llvm::BasicBlock::Create(m.getContext(), "",
      bb_prev->getParent(), bb_succ);

  // Do strlen maths here
  // Phi together result from strlen is succ bb

  // Add branch to pred BB, do strlen iff ci not null
  // Add a iff not null branch
  llvm::BranchInst::Create(bb_succ, bb_strlen, icmp, bb_prev);

  // Make our argument vector containing arg
  std::vector<llvm::Value *> args = { str_val };

  auto strlen_ret = llvm::CallInst::Create(strlen_fcn, args, "", bb_strlen);

  // Add 1 for nullptr terminated strings
  auto inc = llvm::BinaryOperator::Create(
      llvm::Instruction::Add,
      strlen_ret, llvm::ConstantInt::get(i64_type, 1),
      "", bb_strlen);

  // Create terminator
  llvm::BranchInst::Create(bb_succ, bb_strlen);

  // Now, add a phi to bb_succ
  auto phi = llvm::PHINode::Create(i64_type, 2, "", std::begin(*bb_succ));
  phi->addIncoming(inc, bb_strlen);
  phi->addIncoming(llvm::ConstantInt::get(i64_type, 0), bb_prev);

  *insert_after = phi;

  return phi;
}

template <const char *name>
struct AllocNamedString {
  // We know the size -- can gep from type_name
  std::vector<AllocInfo> operator()(llvm::Module &m,
      llvm::CallSite &cs,
      ObjectMap &omap,
      llvm::Instruction **insert_after) const {
    std::vector<AllocInfo> ret;

    auto ci = cs.getInstruction();
    // First, get the argument
    auto str_id = omap.getNamedObject(name);

    auto len = add_checked_strlen(m, ci, insert_after);

    ret.emplace_back(ci, len, str_id);

    return ret;
  }
};

struct StringAlloc {
  std::vector<AllocInfo> operator()(llvm::Module &m,
      llvm::CallSite &cs,
      ObjectMap &,
      llvm::Instruction **insert_after) const {
    std::vector<AllocInfo> ret;

    auto strlen_fcn = m.getFunction("strlen");
    // I may have to create an external linkage for this in some instances...
    //   ugh
    assert(strlen_fcn != nullptr);

    // We have the size of the type, its returned in the return value
    auto ci = cs.getInstruction();

    auto len = add_checked_strlen(m, ci, insert_after);

    ret.emplace_back(ci, len, ObjectMap::ObjID::invalid());

    return ret;
  }
};

struct CTypeAlloc {
  std::vector<AllocInfo> operator()(llvm::Module &m,
      llvm::CallSite &cs,
      ObjectMap &omap,
      llvm::Instruction **insert_after) const {
    auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
    auto i64_type = llvm::IntegerType::get(m.getContext(), 64);
    std::vector<AllocInfo> ret;

    // We have the size of the type, its returned in the return value
    auto ci = cs.getInstruction();

    // subtract 128 from ci (gep for -128)
    std::vector<llvm::Value *> indicies;
    indicies.push_back(llvm::ConstantInt::get(i32_type, -128));

    auto gep = llvm::GetElementPtrInst::Create(ci, indicies);

    // Insert the gep after "insert_after"
    gep->insertAfter(*insert_after);

    // The ctype array size is:
    //    384 * sizeof(int16_t)
    // ...because that's what the spec says
    auto len = llvm::ConstantInt::get(i64_type, 384*sizeof(int16_t));

    *insert_after = gep;

    ret.emplace_back(gep, len, omap.getNamedObject("ctype"));

    return ret;
  }
};

template <size_t arg_num>
struct ReturnArgOrMallocStrAlloc {
  // This function either returns one of the arguments or mallocs... so it can
  //    be abbreviated to alloc if arg not null.  In which case, we'll return a
  //    zero if the arg is null, and non-zero if it is not
  std::vector<AllocInfo> operator()(llvm::Module &m,
      llvm::CallSite &cs,
      ObjectMap &,
      llvm::Instruction **) const {
    auto i64_type = llvm::IntegerType::get(m.getContext(), 64);
    std::vector<AllocInfo> ret;

    auto ci = cs.getInstruction();
    // First, get the argument
    auto arg = cs.getArgument(arg_num);

    auto i8_ptr_type = llvm::PointerType::get(
        llvm::IntegerType::get(m.getContext(), 8), 0);

    // If the argument is nullptr then we return alloc, otherwise do nothing
    // Add a check for nullptr, and a BB in that case:
    auto strlen_fcn = m.getFunction("strlen");
    // I may have to create an external linkage for this in some instances...
    //   ugh
    assert(strlen_fcn != nullptr);


    // This means we add a check for nullptr
    // Then if not nullptr we do math
    // We phi together after math
    // Finally, we return the info needed for the alloc function

    // If ci is nullptr, don't do the following, otherwise, do it
    // First, split the BB after the CI
    auto bb_prev = ci->getParent();
    auto bb_it = llvm::BasicBlock::iterator(ci);
    // rewind to before CI
    bb_it = std::prev(bb_it);

    // Split
    auto bb_succ = bb_prev->splitBasicBlock(bb_it);
    // Then delete the terminator in pred BB
    auto old_term = bb_prev->getTerminator();
    old_term->eraseFromParent();

    // Add a icmp
    auto icmp = new llvm::ICmpInst(*bb_prev, llvm::CmpInst::Predicate::ICMP_EQ,
        ci, llvm::ConstantPointerNull::get(i8_ptr_type));

    auto bb_strlen = llvm::BasicBlock::Create(m.getContext(), "",
        bb_prev->getParent(), bb_succ);

    // Do strlen maths here
    // Phi together result from strlen is succ bb

    // Add branch to pred BB, do strlen iff ci not null
    // Add a iff not null branch
    llvm::BranchInst::Create(bb_succ, bb_strlen, icmp, bb_prev);

    // Make our argument vector containing ci
    std::vector<llvm::Value *> args = { ci };

    auto strlen_ret = llvm::CallInst::Create(strlen_fcn, ci, "", bb_strlen);

    // Add 1 for nullptr terminated strings
    auto inc = llvm::BinaryOperator::Create(
        llvm::Instruction::Add,
        strlen_ret, llvm::ConstantInt::get(i64_type, 1),
        "", bb_strlen);

    // Create terminator
    llvm::BranchInst::Create(bb_succ, bb_strlen);

    // Now, add a phi to bb_succ
    auto phi = llvm::PHINode::Create(i64_type, 2, "", std::begin(*bb_succ));
    phi->addIncoming(inc, bb_strlen);
    phi->addIncoming(arg, bb_prev);

    ret.emplace_back(ci, phi, ObjectMap::ObjID::invalid());

    return ret;
  }
};

template <size_t arg_num, const char *name>
struct ReturnArgOrStaticAlloc {
  // This function either returns one of the arguments or a pointer to static
  //    memory...
  //    An allocation happens if the return value != arg[arg_num]
  //    In that case, alloc_size = strlen(arg)+1, and the static value is gotten
  //       by "name"
  std::vector<AllocInfo> operator()(llvm::Module &m,
      llvm::CallSite &cs,
      ObjectMap &,
      llvm::Instruction **insert_after) const {
    auto i64_type = llvm::IntegerType::get(m.getContext(), 64);
    std::vector<AllocInfo> ret;

    auto ci = cs.getInstruction();

    // First, get the argument
    auto arg = cs.getArgument(arg_num);

    /*
    auto i8_ptr_type = llvm::PointerType::get(
        llvm::IntegerType::get(m.getContext(), 8), 0);
    */

    // If the argument is nullptr then we return alloc, otherwise do nothing
    // Add a check for nullptr, and a BB in that case:
    auto strlen_fcn = m.getFunction("strlen");
    // I may have to create an external linkage for this in some instances...
    //   ugh
    assert(strlen_fcn != nullptr);


    // This means we add a check for nullptr
    // Then if not nullptr we do math
    // We phi together after math
    // Finally, we return the info needed for the alloc function

    // If ci is nullptr, don't do the following, otherwise, do it
    // First, split the BB after the CI
    auto bb_prev = ci->getParent();
    auto bb_it = llvm::BasicBlock::iterator(ci);
    // rewind to before CI
    bb_it = std::next(bb_it);

    // Split
    auto bb_succ = bb_prev->splitBasicBlock(bb_it);
    // Then delete the terminator in pred BB
    auto old_term = bb_prev->getTerminator();
    old_term->eraseFromParent();

    // Add a pointer comp -- branch to strlen on neq
    auto icmp = new llvm::ICmpInst(*bb_prev, llvm::CmpInst::Predicate::ICMP_NE,
        ci, arg);

    auto bb_strlen = llvm::BasicBlock::Create(m.getContext(), "",
        bb_prev->getParent(), bb_succ);

    // Do strlen maths here
    // Phi together result from strlen is succ bb

    // Add branch to pred BB, do strlen iff ci not null
    // Add a iff not null branch
    llvm::BranchInst::Create(bb_succ, bb_strlen, icmp, bb_prev);

    // Make our argument vector containing ci
    std::vector<llvm::Value *> args = { ci };

    auto strlen_ret = llvm::CallInst::Create(strlen_fcn, ci, "", bb_strlen);

    // Add 1 for nullptr terminated strings
    auto inc = llvm::BinaryOperator::Create(
        llvm::Instruction::Add,
        strlen_ret, llvm::ConstantInt::get(i64_type, 1),
        "", bb_strlen);

    // Create terminator
    llvm::BranchInst::Create(bb_succ, bb_strlen);

    // Now, add a phi to bb_succ
    auto phi = llvm::PHINode::Create(i64_type, 2, "", std::begin(*bb_succ));
    phi->addIncoming(inc, bb_strlen);
    phi->addIncoming(llvm::ConstantInt::get(i64_type, 0), bb_prev);

    *insert_after = phi;
    ret.emplace_back(ci, phi, ObjectMap::ObjID::invalid());

    return ret;
  }
};
//}}}

// FreeVal Helpers {{{
struct NoFreeData {
  std::vector<llvm::Value *>
  operator()(llvm::Module &, llvm::CallSite &,
      ObjectMap &,
      llvm::Instruction **) const {
    return std::vector<llvm::Value *>();
  }
};

template <size_t op_num>
struct FreeOp {
  std::vector<llvm::Value *>
  operator()(llvm::Module &, llvm::CallSite &cs,
      ObjectMap &,
      llvm::Instruction **) const {
    return { cs.getArgument(op_num) };
  }
};
//}}}

// AllocInfo helpers {{{
struct AllocInfoNone {
  StaticAllocInfo operator()(llvm::ImmutableCallSite &,
      ObjectMap &) const {
    return StaticAllocInfo(AllocStatus::None, nullptr);
  }
};

struct AllocInfoWeak {
  StaticAllocInfo operator()(llvm::ImmutableCallSite &cs,
      ObjectMap &omap) const {
    auto ci = cs.getInstruction();
    auto inferred_type = findLargestType(omap, *ci);
    return StaticAllocInfo(AllocStatus::Weak, inferred_type);
  }
};

struct AllocInfoWeakNS {
  StaticAllocInfo operator()(llvm::ImmutableCallSite &cs,
      ObjectMap &) const {
    auto m = cs.getInstruction()->getParent()->getParent()->getParent();
    auto i8_ptr_type = llvm::PointerType::get(
        llvm::IntegerType::get(m->getContext(), 8), 0);
    return StaticAllocInfo(AllocStatus::Weak, i8_ptr_type);
  }
};

template <const char *type_name>
struct AllocInfoWeakType {
  StaticAllocInfo operator()(llvm::ImmutableCallSite &cs,
      ObjectMap &) const {
    auto m = cs.getInstruction()->getParent()->getParent()->getParent();
    return StaticAllocInfo(AllocStatus::Weak, m->getTypeByName(type_name));
  }
};
//}}}

// canAlloc helpers {{{
struct CanAlloc {
  bool operator()() const {
    return true;
  }
};

struct CannotAlloc {
  bool operator()() const {
    return false;
  }
};
//}}}


// UnknownExtInfo {{{
bool UnknownExtInfo::insertCallCons(llvm::ImmutableCallSite &cs,
    ObjectMap &omap, ConstraintGraph &cg, CFG &cfg, CFG::CFGid *next_id) const {
  // Add a load from an unknwon object
  // The return value is the UniveralValue
  // Each (non-int) pointer argument passed in has the UniversalValue stored
  //    to it
  // If the return value is a pointer:
  auto inst = cs.getInstruction();
  llvm::dbgs() << "WARNING: Instrumentint unknown function: " <<
    cs.getCalledFunction()->getName() << "\n";
  if (llvm::isa<llvm::PointerType>(inst->getType())) {
    // Store universal value into it
    auto ret_id = omap.getValue(inst);
    // Load into ret_id from universal value
    cg.add(ConstraintType::Load, ret_id, ret_id, ObjectMap::UniversalValue);
    addCFGLoad(cfg, *next_id, ret_id);
  }

  // For each argument:
  for (auto it = cs.arg_begin(), en = cs.arg_end();
      it != en; ++it) {
    auto &use = *it;
    auto arg_id = omap.getValueC(use.get());

    auto ld_id = omap.createPhonyID();

    cg.add(ConstraintType::Load, ld_id, arg_id, ObjectMap::UniversalValue);
    addCFGLoad(cfg, *next_id, arg_id);
  }

  return false;
}

std::vector<AllocInfo> UnknownExtInfo::getAllocData(
    llvm::Module &m, llvm::CallSite &ci,
    ObjectMap &omap,
    llvm::Instruction **insert_after) const {
  llvm::dbgs() << "WARNING: Unknown alloc data: " <<
    ci.getCalledFunction()->getName() << "\n";
  // Do nothing
  return NoAllocData()(m, ci, omap, insert_after);
}

std::vector<llvm::Value *> UnknownExtInfo::getFreeData(
    llvm::Module &m, llvm::CallSite &ci,
    ObjectMap &omap, llvm::Instruction **insert_after) const {
  llvm::dbgs() << "WARNING: Unknown free data: " <<
    ci.getCalledFunction()->getName() << "\n";
  // Do nothing
  return NoFreeData()(m, ci, omap, insert_after);
}

StaticAllocInfo UnknownExtInfo::getAllocInfo(llvm::ImmutableCallSite &cs,
    ObjectMap &omap) const {
  auto ci = cs.getInstruction();

  if (llvm::isa<llvm::PointerType>(ci->getType())) {
    // Assume this may be an allocation function, find the largest type
    auto inferred_type = findLargestType(omap, *cs.getInstruction());

    return StaticAllocInfo(AllocStatus::Weak, inferred_type);
  } else {
    // We cannot allocate anything for a non-ptr
    return StaticAllocInfo(AllocStatus::None, nullptr);
  }
}
//}}}

// CRTP {{{
template <typename alloc_cons,
          typename alloc_size,
          typename free_pointer,
          typename alloc_info,
          typename can_alloc>
struct ExtInfoCRTP : public ExtInfo {
  bool insertCallCons(llvm::ImmutableCallSite &ci, ObjectMap &omap,
      ConstraintGraph &cg, CFG &cfg, CFG::CFGid *next_id) const override {
    return alloc_cons()(ci, omap, cg, cfg, next_id);
  }

  std::vector<AllocInfo>
  getAllocData(llvm::Module &m, llvm::CallSite &ci,
      ObjectMap &omap,
      llvm::Instruction **insert_after) const override {
    return alloc_size()(m, ci, omap, insert_after);
  }

  std::vector<llvm::Value *> getFreeData(llvm::Module &m,
      llvm::CallSite &ci,
      ObjectMap &omap,
      llvm::Instruction **insert_after) const override {
    return free_pointer()(m, ci, omap, insert_after);
  }

  StaticAllocInfo getAllocInfo(llvm::ImmutableCallSite &cs,
      ObjectMap &omap) const override {
    return alloc_info()(cs, omap);
  }

  bool canAlloc() const override {
    return can_alloc()();
  }
};
//}}}

// Common ExtInfos {{{
// Noop
class ExtNoop :
  public ExtInfoCRTP<NoopCons, NoAllocData, NoFreeData, AllocInfoNone,
      CannotAlloc> { };

// Allocations
// Ex malloc()
template<size_t ArgNum>
class Alloc :
  public ExtInfoCRTP<AllocCons, AllocSize<ArgNum>, NoFreeData,
      AllocInfoWeak, CanAlloc> { };

// FIXME: decltype because I'm being lazy
template<size_t ArgNum0, size_t ArgNum1, Opcode op>
class AllocOp :
  public ExtInfoCRTP<AllocCons, AllocSizeOp<ArgNum0, ArgNum1, op>, NoFreeData,
        AllocInfoWeak, CanAlloc> { };

// Ex realloc()
class Realloc1Free0 :
  public ExtInfoCRTP<ReturnCons<0>, AllocSize<1>, FreeOp<0>,
        AllocInfoWeak, CanAlloc> { };

// Ex. strchar
template <size_t arg_num>
class ReturnArg :
  public ExtInfoCRTP<ReturnCons<arg_num>, NoAllocData, NoFreeData,
      AllocInfoNone, CannotAlloc> { };

template <const char *name, const char *type_name>
class ReturnNamedStruct :
  public ExtInfoCRTP<ReturnNamedStructCons<name, type_name>,
            AllocNamedStruct<name, type_name>, NoFreeData,
            AllocInfoNone, CannotAlloc> { };

template <const char *name>
class ReturnNamedString :
  public ExtInfoCRTP<ReturnNamedNSCons<name>,
            AllocNamedString<name>, NoFreeData,
            AllocInfoNone, CannotAlloc> { };

template <const char *name, size_t size>
class ReturnNamedSize :
  public ExtInfoCRTP<ReturnNamedNSCons<name>,
            AllocNamedSize<name, size>, NoFreeData,
            AllocInfoNone, CannotAlloc> { };

// For things like strtoul which stores arg0 into arg1
template <size_t src, size_t dest>
class StoreArgs :
  public ExtInfoCRTP<StoreCons<src, dest>, NoAllocData, NoFreeData,
            AllocInfoNone, CannotAlloc> { };

template <size_t arg_num>
class ReturnArgOrMalloc :
  public ExtInfoCRTP<ReturnArgOrMallocCons<arg_num>,
          ReturnArgOrMallocStrAlloc<arg_num>, NoFreeData,
          AllocInfoWeak, CannotAlloc> { };

template <size_t arg_num>
class ReturnArgOrMallocNS :
  public ExtInfoCRTP<ReturnArgOrMallocCons<arg_num>,
          ReturnArgOrMallocStrAlloc<arg_num>, NoFreeData,
          AllocInfoWeakNS, CanAlloc> { };

template <size_t arg_num, const char *name>
class ReturnArgOrStatic :
  public ExtInfoCRTP<ReturnArgOrStaticCons<arg_num, name>,
          ReturnArgOrStaticAlloc<arg_num, name>, NoFreeData,
          AllocInfoNone, CannotAlloc> { };

// Ex free()
template<size_t ArgNum0>
class Free :
  public ExtInfoCRTP<NoopCons, NoAllocData, FreeOp<ArgNum0>,
          AllocInfoNone, CannotAlloc> { };

// Files
class FileOpen :
  public ExtInfoCRTP<AllocTypeCons<filestruct_name>,
          AllocStruct<filestruct_name>, NoFreeData,
          AllocInfoWeakType<filestruct_name>,
          CanAlloc> { };

class FileClose :
  public ExtInfoCRTP<NoopCons, NoAllocData, FreeOp<0>,
          AllocInfoNone, CannotAlloc> { };

// Directories
class DirOpen :
  public ExtInfoCRTP<ReturnNamedNSCons<dir_name>,
          // FIXME(ddevec) -- sizeof(DIR) ? ? ?
          AllocNamedSize<dir_name, 8>, NoFreeData,
          AllocInfoWeak, CanAlloc> { };

class DirClose :
  public ExtInfoCRTP<NoopCons, NoAllocData, FreeOp<0>,
          AllocInfoNone, CannotAlloc> { };

// Memcpy
class ExtMemcpy :
  public ExtInfoCRTP<MemcpyCons, NoAllocData, NoFreeData,
          AllocInfoNone, CannotAlloc> { };

// Special cases
class StrdupInfo :
  public ExtInfoCRTP<AllocNSCons, StringAlloc, NoFreeData,
          AllocInfoWeakNS, CanAlloc> { };

class ExtPthreadCreate :
  public ExtInfoCRTP<PthreadCreateCons, NoAllocData, NoFreeData,
          AllocInfoNone, CannotAlloc> { };

class ExtCTypeBLoc :
  public ExtInfoCRTP<ReturnNamedNSCons<ctype_name>,
      CTypeAlloc, NoFreeData, AllocInfoNone, CannotAlloc> { };
//}}}

// More annoying structs...

// Initialize the internal info_ (unordered_map) here
void ExtLibInfo::init(llvm::Module &m, ObjectMap &omap) {  //  NOLINT
  //{{{
  // Setting up named static data {{{
  // Named data includes:
  //    ctype(1)
  //    datetime_static(struct.tm)
  //    textdomain_static(1)
  //    terminfo(1)
  //    clib(1)
  //    locale(1)
  //    errno(1)
  //    env(1)
  omap.addNamedObject(nullptr, "ctype");
  omap.addNamedObject(m.getTypeByName("struct.tm"), "datetime_static");
  omap.addNamedObject(nullptr, "textdomain_static");
  omap.addNamedObject(nullptr, "gettext_static");
  omap.addNamedObject(nullptr, "terminfo");
  omap.addNamedObject(nullptr, "clib");
  omap.addNamedObject(nullptr, "locale");
  omap.addNamedObject(nullptr, "errno");
  omap.addNamedObject(nullptr, "env");
  omap.addNamedObject(nullptr, "dir");

  // Does the named data need constraints?
  // Largely no...
  //}}}

  // Functions monitored {{{
  // Allocations {{{
  // Malloc/calloc/friends...
  info_.emplace(std::piecewise_construct,
      std::make_tuple("malloc"),
      std::make_tuple(new Alloc<0>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("valloc"),
      std::make_tuple(new Alloc<0>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("calloc"),
      std::make_tuple(new AllocOp<0, 1, llvm::Instruction::Mul>()));

  // Reallocs
  info_.emplace(std::piecewise_construct,
      std::make_tuple("realloc"),
      std::make_tuple(new Realloc1Free0()));

  // Frees
  info_.emplace(std::piecewise_construct,
      std::make_tuple("free"),
      std::make_tuple(new Free<0>()));

  // Perl calls...
  info_.emplace(std::piecewise_construct,
      std::make_tuple("Perl_safesysmalloc"),
      std::make_tuple(new Alloc<0>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("Perl_safesysrealloc"),
      std::make_tuple(new Realloc1Free0()));
  //}}}

  // Strdup... ...
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strdup"),
      std::make_tuple(new StrdupInfo()));

  // File/dir {{{
  // File Open
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fopen"),
      std::make_tuple(new FileOpen()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("tmpfile"),
      std::make_tuple(new FileOpen()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fopen64"),
      std::make_tuple(new FileOpen()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("popen"),
      std::make_tuple(new FileOpen()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fdopen"),
      std::make_tuple(new FileOpen()));

  // File Close
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fclose"),
      std::make_tuple(new FileClose()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("pclose"),
      std::make_tuple(new FileClose()));

  // Dir Operations
  info_.emplace(std::piecewise_construct,
      std::make_tuple("opendir"),
      std::make_tuple(new DirOpen()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("closedir"),
      std::make_tuple(new DirClose()));
  //}}}

  // String functions {{{
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strchr"),
      std::make_tuple(new ReturnArg<0>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strrchr"),
      std::make_tuple(new ReturnArg<0>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strtok"),
      std::make_tuple(new ReturnArg<0>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("stpcpy"),
      std::make_tuple(new ReturnArg<0>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strcat"),
      std::make_tuple(new ReturnArg<0>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strncat"),
      std::make_tuple(new ReturnArg<0>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strcpy"),
      std::make_tuple(new ReturnArg<0>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strncpy"),
      std::make_tuple(new ReturnArg<0>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strpbrk"),
      std::make_tuple(new ReturnArg<0>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getcwd"),
      std::make_tuple(new ReturnArg<0>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getwd"),
      std::make_tuple(new ReturnArg<0>()));
  //}}}

  // Other functions that return arg0
  info_.emplace(std::piecewise_construct,
      std::make_tuple("mkdtemp"),
      std::make_tuple(new ReturnArg<0>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("memchr"),
      std::make_tuple(new ReturnArg<0>()));

  // This mostly returns arg0... we're going with it...
  info_.emplace(std::piecewise_construct,
      std::make_tuple("bindtextdomain"),
      std::make_tuple(new ReturnArg<0>()));

  // Returns arg2... cuz
  info_.emplace(std::piecewise_construct,
      std::make_tuple("gcvt"),
      std::make_tuple(new ReturnArg<2>()));

  // Returns pointer into libc static -- overwritten by datetime calls...
  info_.emplace(std::piecewise_construct,
      std::make_tuple("localtime"),
      std::make_tuple(new ReturnNamedStruct<datetime_name,
        datetimestruct_name>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("gmtime"),
      std::make_tuple(new ReturnNamedStruct<datetime_name,
        datetimestruct_name>()));
  // Returns pointer into library data -- overwritten by next textdomain call...
  info_.emplace(std::piecewise_construct,
      std::make_tuple("textdomain"),
      std::make_tuple(new ReturnNamedString<textdomain_name>()));

  // Stores Arg0 in Arg1
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strtol"),
      std::make_tuple(new StoreArgs<0, 1>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strtoul"),
      std::make_tuple(new StoreArgs<0, 1>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strtoll"),
      std::make_tuple(new StoreArgs<0, 1>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strtoull"),
      std::make_tuple(new StoreArgs<0, 1>()));

  // Ugh Relpath
  info_.emplace(std::piecewise_construct,
      std::make_tuple("realpath"),
      std::make_tuple(new ReturnArgOrMallocNS<1>()));

  // Gettext
  info_.emplace(std::piecewise_construct,
      std::make_tuple("gettext"),
      std::make_tuple(new ReturnArgOrStatic<0, gettext_name>()));

  // freopen -- returns arg2
  info_.emplace(std::piecewise_construct,
      std::make_tuple("freopen"),
      std::make_tuple(new ReturnArg<2>()));

  // FIXME(ddevec) -- hack -- Ugh, ioctl -- Ignore for now?
  llvm::dbgs() << "FIXME: Treating ioctl as noop...\n";
  info_.emplace(std::piecewise_construct,
      std::make_tuple("ioctl"),
      std::make_tuple(new ExtNoop()));

  // Pthread create... ugh
  info_.emplace(std::piecewise_construct,
      std::make_tuple("pthread_create"),
      std::make_tuple(new ExtPthreadCreate()));

  // External library statically allocated data {{{
  /*
  info_.emplace("pthread_getspecific", LoadNamed<"pthread_specific">);
  info_.emplace("pthread_setspecific", StoreNamed<"pthread_specific">);
  */
  info_.emplace(std::piecewise_construct,
      std::make_tuple("tigetstr"),
      std::make_tuple(new ReturnNamedString<terminfo_name>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("tparm"),
      std::make_tuple(new ReturnNamedString<terminfo_name>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strerror"),
      std::make_tuple(new ReturnNamedString<clib_name>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("gai_strerror"),
      std::make_tuple(new ReturnNamedString<clib_name>()));

  /*
  info_.emplace("readdir", new ExtReadDir());
  info_.emplace("opendir", new ExtOpenDir());
  */
  // Ctype...
  info_.emplace(std::piecewise_construct,
      std::make_tuple("__ctype_b_loc"),
      std::make_tuple(new ExtCTypeBLoc()));

  // Locale
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getlocale"),
      std::make_tuple(new ReturnNamedString<locale_name>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("setlocale"),
      std::make_tuple(new ReturnNamedString<locale_name>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("nl_langinfo"),
      std::make_tuple(new ReturnNamedString<locale_name>()));

  // Errno
  info_.emplace(std::piecewise_construct,
      std::make_tuple("__errno_location"),
      std::make_tuple(new ReturnNamedSize<errno_name, sizeof(int)>()));

  // Env
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getenv"),
      std::make_tuple(new ReturnNamedString<env_name>()));

  //}}}

  // Noop external calls {{{
  info_.emplace(std::piecewise_construct,
      std::make_tuple("atoi"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("atof"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("atol"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("atoll"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("remove"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("unlink"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("rename"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("memcmp"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("llvm.memset"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("llvm.va_copy"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("system"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("link"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("setuid"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("setgid"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("seteuid"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("setegid"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("geteuid"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getegid"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getpid"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("setvbuf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("setbuf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("ftruncate"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("closedir"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("putenv"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("kill"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("frexp"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("__isnan"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strcmp"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strncmp"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("execl"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("execlp"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("execle"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("execv"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("execvp"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("chmod"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("puts"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("write"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("open"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("create"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("open64"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("lstat64"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("truncate"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("chdir"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("mkdir"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("rmdir"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("read"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("pipe"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("wait"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("time"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("stat"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fstat"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("stat64"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fstat64"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("lstat"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strtod"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strtof"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strtold"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fflush"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("feof"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fileno"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("clearerr"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("rewind"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("ftell"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("ferror"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fgetc"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fgetc"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("_IO_getc"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fwrite"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fread"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fgets"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("ungetc"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fputc_unlocked"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fputc"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fputs"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fputs_unlocked"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("putc"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fclose"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("ftell"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("rewind"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("_IO_putc"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fseek"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fgetpos"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fsetpos"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("printf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fprintf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sprintf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("vprintf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("vfprintf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("vsprintf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("scanf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fscanf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sscanf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("__assert_fail"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("modf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("exit"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("_exit"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strlen"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("close"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("abort"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("atexit"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("error"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("umask"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("free"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("setfscreatecon"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strspn"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strcspn"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("bsearch"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("clock"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getpagesize"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("obstack_free"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("_obstack_newchunk"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("_obstack_begin"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("_obstack_memory_used"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("__ctype_get_mb_cur_max"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("iswprint"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("mbsinit"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("mbrtowc"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fchdir"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fseeko"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("ferror_unlocked"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fork"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("waitpid"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("raise"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("__fpending"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("ferror"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fchown"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fchmod"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("lchown"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("chown"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("lchown"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getc_unlocked"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("snprintf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("__freading"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("lseek"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fcntl"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("feeko"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("abs"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("toupper"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("__iso_c99sscanf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("iswupper"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("tolower"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("towupper"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("towlower"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strncasecmp"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("floor"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("ceil"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fabs"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("acos"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("asin"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("atan"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("atan2"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("cos"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("cosh"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("exp"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fmod"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strcasecmp"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("log"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("log10"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sin"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sinh"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("tan"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("tanh"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("readlink"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("qsort"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sqrt"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strftime"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getuid"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getgid"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("gettimeofday"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("settimeofday"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("iconv"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("iconv_close"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("access"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("dup"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strncpy"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("__isoc99_sscanf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("select"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("ctime"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fsync"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("utime"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("mblen"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("perror"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("lseek64"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("perror"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("signal"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("stat64"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("isatty"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("stat64"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("vsnprintf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("__isoc99_fscanf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("pclose"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getrusage"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getrlimit"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("setrlimit"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("cielf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("floorf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sleep"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("setupterm"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("tigetnum"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("times"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sysconf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("ceilf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("setlinebuf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("putchar"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("htons"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("htonl"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("ntohs"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("ntohl"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("random"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("inet_pton"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("rand"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("inet_ntop"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("pthread_mutex_init"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("pthread_cond_init"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sigemtpyset"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sigfillset"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sigaddset"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sigdelset"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sigismember"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("epoll_ctl"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("epoll_wait"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("poll"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("setsocketopt"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("socket"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("bind"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("connect"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("accept"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getpeername"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getsockname"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("setsockopt"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getsockopt"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strcoll"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("syslog"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("uname"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("wait3"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("dup2"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("setsid"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("srand"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getrlimit64"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("setrlimit64"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("pthread_attr_setstacksize"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("pthread_attr_getstacksize"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("ftruncate64"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sync_file_range"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fdatasync"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("truncate64"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("ftello64"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("ftello"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getitimer"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("setitimer"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("__isinf"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("__isinfl"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("__isnan"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("__isnanl"),
      std::make_tuple(new ExtNoop()));
  /*
  info_.emplace("__finitel", ExtNoop);
  info_.emplace("getopt_long", ExtNoop);
  info_.emplace("getopt", ExtNoop);
  //}}}
  //}}}
  */


  // Intrinsics monitored (ex. memcpy) {{{
  // Noops {{{
  // /*
  matchInfo_.emplace_back(std::piecewise_construct,
      std::make_tuple("llvm.memset"),
      std::make_tuple(new ExtNoop()));
  matchInfo_.emplace_back(std::piecewise_construct,
      std::make_tuple("llvm.bswap"),
      std::make_tuple(new ExtNoop()));
  matchInfo_.emplace_back(std::piecewise_construct,
      std::make_tuple("llvm.expect"),
      std::make_tuple(new ExtNoop()));
  matchInfo_.emplace_back(std::piecewise_construct,
      std::make_tuple("llvm.pow"),
      std::make_tuple(new ExtNoop()));
  //}}}

  // Memcpy functions... {{{
  matchInfo_.emplace_back(std::piecewise_construct,
      std::make_tuple("llvm.memcpy"),
      std::make_tuple(new ExtMemcpy()));
  matchInfo_.emplace_back(std::piecewise_construct,
      std::make_tuple("llvm.memmove"),
      std::make_tuple(new ExtMemcpy()));
  matchInfo_.emplace_back(std::piecewise_construct,
      std::make_tuple("memmove"),
      std::make_tuple(new ExtMemcpy()));
  //}}}
  //}}}

  //}}}
}  // NOLINT

