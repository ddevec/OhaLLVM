/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/ExtInfo.h"

#include <dirent.h>

#include <cassert>

#include <map>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"

#include "include/CallInfo.h"
#include "include/Cg.h"
#include "include/ModInfo.h"
#include "include/ValueMap.h"

typedef decltype(llvm::Instruction::Mul) Opcode;
typedef ExtInfo::AllocInfo AllocInfo;
typedef ExtInfo::StaticAllocInfo StaticAllocInfo;

char ctype_name[] = "ctype";
char filestruct_name[] = "struct._IO_FILE";
char dirstruct_name[] = "struct.__dirstream";
char datetimestruct_name[] = "struct.tm";
char pwnamstruct_name[] = "struct.passwd";
char grnamstruct_name[] = "struct.group";

char locale_name[] = "locale";
char env_name[] = "env";
char errno_name[] = "errno";
char dirent_name[] = "dirent_static";
char clib_name[] = "clib";
char dir_name[] = "dir";
char terminfo_name[] = "terminfo";
char datetime_name[] = "datetime_static";
char textdomain_name[] = "textdomain_static";
char gettext_name[] = "gettext_static";
char strtok_name[] = "strtok";
char pwnam_name[] = "pwnam";
char grnam_name[] = "grnam";

typedef ValueMap::Id Id;

// called from malloc-like allocations, to find the largest strcuture size the
// untyped allocation is cast to.
static const llvm::Type *findLargestType(ModInfo &info,
    const llvm::Value &ins,
    bool conservative = true) {
  auto biggest_type = ins.getType()->getContainedType(0);

  bool found = false;
  int32_t max_size = 0;

  // Strip any array qualifiers
  while (auto at = dyn_cast<llvm::ArrayType>(biggest_type)) {
    biggest_type = at->getElementType();
  }

  // If its a struct type, update our lragest size
  if (auto st = dyn_cast<llvm::StructType>(biggest_type)) {
    max_size = info.getStructInfo(st).size();
  }

  // now, see how each use is cast...
  for (auto &use : ins.uses()) {
    auto cast_inst = dyn_cast<llvm::CastInst>(use);

    if (cast_inst && llvm::isa<llvm::PointerType>(cast_inst->getType())) {
      found = true;

      // this is the type were casting to
      auto cast_type = cast_inst->getType()->getContainedType(0);

      int32_t size = 0;

      // strip off array qualifiers
      while (auto at = dyn_cast<llvm::ArrayType>(cast_type)) {
        cast_type = at->getElementType();
      }

      // if we're casting to a strucutre
      if (auto st = dyn_cast<llvm::StructType>(cast_type)) {
        size = info.getStructInfo(st).size();
      }

      if (size > max_size) {
        max_size = size;
        biggest_type = cast_type;
      }
    }
  }

  if (!found && max_size == 0 && conservative) {
    return info.getMaxStructInfo().type();
  }

  return biggest_type;
}

// Constraint Helpers {{{
struct NoopCons {
  bool operator()(Cg &, llvm::ImmutableCallSite &,
      const CallInfo &) const {
    return true;
  }
};

struct AllocCons {
  bool operator()(Cg &cg, llvm::ImmutableCallSite &cs,
      const CallInfo &ci) const {
    auto inst = cs.getInstruction();

    auto dest_id = ci.ret();

    auto type = findLargestType(cg.modInfo(), *inst);
    auto size = cg.modInfo().getSizeOfType(type);

    auto src_obj_id = cg.vals().createAlloc(inst, size);

    cg.add(ConstraintType::AddressOf, src_obj_id, dest_id);

    return true;
  }
};

// Non-structure -- for example, strdup, where strs are not structs
struct AllocNSCons {
  bool operator()(Cg &cg, llvm::ImmutableCallSite &cs,
      const CallInfo &ci) const {
    auto inst = cs.getInstruction();

    auto dest = ci.ret();

    auto src = cg.vals().createAlloc(inst, 1);

    // No type info, can just do simple cg add...
    cg.add(ConstraintType::AddressOf, src, dest);

    return true;
  }
};

template <const char *type_name>
struct AllocTypeCons {
  bool operator()(Cg &cg, llvm::ImmutableCallSite &cs,
      const CallInfo &ci) const {
    auto inst = cs.getInstruction();
    auto m = inst->getParent()->getParent()->getParent();

    auto dest = ci.ret();
    auto type = m->getTypeByName(type_name);
    auto size = cg.modInfo().getSizeOfType(type);
    auto src = cg.vals().createAlloc(inst, size);

    // Add constraints for the alloc type...
    cg.add(ConstraintType::AddressOf, src, dest);

    return true;
  }
};

template <size_t arg_num>
struct ReturnCons {
  bool operator()(Cg &cg, llvm::ImmutableCallSite &,
      const CallInfo &ci) const {
    // The function returns arg(arg_num)
    auto ci_id = ci.ret();
    auto arg0_id = ci.args()[arg_num];

    // Copy the arg into CI
    cg.add(ConstraintType::Copy, arg0_id, ci_id);

    return true;
  }
};

template <const char *name, const char *type_name>
struct ReturnNamedStructCons {
  bool operator()(Cg &cg, llvm::ImmutableCallSite &,
      const CallInfo &ci) const {
    // The function return
    auto ci_id = ci.ret();

    auto named_obj_id = cg.vals().getNamed(name);

    // Copy the arg into CI
    cg.add(ConstraintType::Copy, named_obj_id, ci_id);

    return true;
  }
};

template <const char *name>
struct ReturnNamedNSCons {
  bool operator()(Cg &cg, llvm::ImmutableCallSite &,
      const CallInfo &ci) const {
    // The function return
    auto ci_id = ci.ret();

    auto named_obj_id = cg.vals().getNamed(name);

    // Copy the arg into CI
    cg.add(ConstraintType::Copy, named_obj_id, ci_id);

    return true;
  }
};

template <size_t src, size_t dest>
struct StoreCons {
  bool operator()(Cg &cg, llvm::ImmutableCallSite &,
      const CallInfo &ci) const {
    // The function returns arg(arg_num)
    auto st_id = cg.vals().createPhonyID();
    auto &args = ci.args();

    cg.add(ConstraintType::Store, st_id,
        args[src],
        args[dest]);

    return true;
  }
};

template <size_t arg_num>
struct ReturnArgOrMallocCons {
  bool operator()(Cg &cg, llvm::ImmutableCallSite &cs,
      const CallInfo &ci) const {
    // The function returns arg(arg_num) or allocates a new set of data
    // First, handle the allocation
    // Add objects to the graph
    auto inst = cs.getInstruction();
    auto type = findLargestType(cg.modInfo(), *inst);
    auto size = cg.modInfo().getSizeOfType(type);

    auto ci_obj = cg.vals().createAlloc(inst, size);
    auto ci_id = ci.ret();
    cg.add(ConstraintType::AddressOf,
        ci_obj, ci_id);

    auto &args = ci.args();
    auto arg_id = args[arg_num];
    // Now, handle the arg copy
    cg.add(ConstraintType::Copy, arg_id, ci_id);

    return true;
  }
};

template <size_t arg_num, const char *name>
struct ReturnArgOrStaticCons {
  bool operator()(Cg &cg, llvm::ImmutableCallSite &,
      const CallInfo &ci) const {
    // The function returns arg(arg_num) or allocates a new set of data
    // First, handle the static return case
    // Add objects to the graph
    llvm::dbgs() << "get named: " << name << "\n";
    auto named_id = cg.vals().getNamed(name);
    auto ci_id = ci.ret();
    cg.add(ConstraintType::Copy,
        named_id, ci_id);

    // Now, handle the arg copy
    auto &args = ci.args();
    auto arg_id = args[arg_num];
    cg.add(ConstraintType::Copy, arg_id, ci_id);

    return true;
  }
};

struct MemcpyCons {
  bool operator()(Cg &cg, llvm::ImmutableCallSite &cs,
      const CallInfo &ci) const {
    auto dest = cs.getArgument(0);
    // auto src = cs.getArgument(1);

    auto &args = ci.args();
    auto first_arg = args[0];
    auto second_arg = args[1];

    // Not conservative, string copys are a thing
    auto type = findLargestType(cg.modInfo(), *dest, false);

    if (auto st = dyn_cast<llvm::StructType>(type)) {
      // Okay, for each field of the structure...
      auto &si = cg.modInfo().getStructInfo(st);

      // Now iterate each field, and add a copy for each field
      int32_t i = 0;
      for (auto it = si.sizes_begin(), en = si.sizes_end();
          it != en; ++it) {
        auto load_dest = cg.vals().createPhonyID();
        // The gep dests have equivalent ptsto as the argumens
        auto load_gep_dest = cg.vals().createPhonyID(cs.getArgument(1));
        auto store_gep_dest = cg.vals().createPhonyID(cs.getArgument(0));

        // Okay, now create the constraints
        // The load_dest is the destination address of the load:
        cg.add(ConstraintType::Copy, second_arg, load_gep_dest, i);
        cg.add(ConstraintType::Load, load_gep_dest, load_dest);

        cg.add(ConstraintType::Copy, first_arg, store_gep_dest, i);
        cg.add(ConstraintType::Store, load_dest, store_gep_dest);

        // Create a load at this id
        dout("Adding load: " << load_dest << " and store: " <<
          store_id << "\n");

        i++;
      }
    // If this isn't a struct, handle it normally
    } else {
      auto load_id = cg.vals().createPhonyID();
      auto store_id = cg.vals().createPhonyID();

      cg.add(ConstraintType::Load, load_id, second_arg, load_id);
      cg.add(ConstraintType::Store, store_id, load_id, first_arg);
    }

    return true;
  }
};


// QSORT
struct QSortCons {
  bool operator()(Cg &, llvm::ImmutableCallSite &,
      const CallInfo &) const {
    // Okay, here is where things get ugly...
    // We have to call compar (arg<3>) with base, base
    // First, create a fake callee_info
    llvm::dbgs() << "FIXME: qsort unsupported\n";

    return true;
  }
};

struct PthreadCreateCons {
  bool operator()(Cg &cg, llvm::ImmutableCallSite &cs,
      const CallInfo &ci) const {
    // Need to add an indirect call... and some funky cfg edges

    // pthread_create
    // First, add
    auto callee = cs.getArgument(2);
    auto &args = ci.args();
    auto arg = args[3];

    // Just add a call to callee
    // FIXME(ddevec) -- If callee is not a function, this is harder
    auto fcn = cast<llvm::Function>(callee);


    // FIXME(ddevec) -- handle the indir fcn call
    // llvm_unreachable("pthread_create call unhandled?");

    // Now, copy arg into the function's argument:
    auto fcn_arg = cg.vals().getDef(&(*fcn->arg_begin()));
    auto node_id = cg.vals().createPhonyID();
    cg.add(ConstraintType::Copy, node_id, arg, fcn_arg);

    return true;
  }
};
//}}}

// AllocSize Helpers {{{
struct NoAllocData {
  std::vector<AllocInfo> operator()(llvm::Module &, llvm::CallSite &,
        ValueMap &, llvm::Instruction **) const {
    return std::vector<AllocInfo>();
  }
};

template <size_t arg_num>
struct AllocSize {
  std::vector<AllocInfo> operator()(llvm::Module &,
      llvm::CallSite &cs,
      ValueMap &,
      llvm::Instruction **) const {
    std::vector<AllocInfo> ret;

    auto val = cs.getArgument(arg_num);

    ret.emplace_back(cs.getInstruction(), val, ValueMap::Id::invalid());

    return ret;
  }
};

template <const char *type_name>
struct AllocStruct {
  std::vector<AllocInfo> operator()(llvm::Module &m,
      llvm::CallSite &cs,
      ValueMap &,
      llvm::Instruction **) const {
    std::vector<AllocInfo> ret;

    auto type = m.getTypeByName(type_name);
    const auto &dl = m.getDataLayout();

    int size = dl.getTypeAllocSize(type);
    auto i64_type = llvm::IntegerType::get(m.getContext(), 64);
    auto type_size_ce = llvm::ConstantInt::get(i64_type, size);

    ret.emplace_back(cs.getInstruction(), type_size_ce,
        ValueMap::Id::invalid());

    return ret;
  }
};

template <size_t arg_num0, size_t arg_num1, Opcode op>
struct AllocSizeOp {
  std::vector<AllocInfo> operator()(llvm::Module &,
      llvm::CallSite &cs,
      ValueMap &,
      llvm::Instruction **) const {
    std::vector<AllocInfo> ret;

    auto ci = cs.getInstruction();

    auto arg0 = cs.getArgument(arg_num0);
    auto arg1 = cs.getArgument(arg_num1);

    auto mul = llvm::BinaryOperator::Create(
        llvm::Instruction::Mul, arg0, arg1, "", ci);

    ret.emplace_back(ci, mul, ValueMap::Id::invalid());

    return ret;
  }
};

template <const char *name, const char *type_name>
struct AllocNamedStruct {
  // We know the size -- can gep from type_name
  std::vector<AllocInfo> operator()(llvm::Module &m,
      llvm::CallSite &cs,
      ValueMap &map,
      llvm::Instruction **) const {
    std::vector<AllocInfo> ret;

    auto type = m.getTypeByName(type_name);
    auto type_size_ce = LLVMHelper::calcTypeOffset(m, type, nullptr);

    // We have the size of the type, its returned in the return value
    auto ci = cs.getInstruction();

    auto static_id = map.getNamed(name);

    ret.emplace_back(ci, type_size_ce, static_id);

    return ret;
  }
};

template <const char *type_name, size_t size>
struct AllocNamedSize {
  // We know the size -- can gep from type_name
  std::vector<AllocInfo> operator()(llvm::Module &m,
      llvm::CallSite &cs,
      ValueMap &map,
      llvm::Instruction **) const {
    std::vector<AllocInfo> ret;
    auto i64_type = llvm::IntegerType::get(m.getContext(), 64);

    // We have the size of the type, its returned in the return value
    auto ci = cs.getInstruction();

    auto static_id = map.getNamed(type_name);

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
  auto phi = llvm::PHINode::Create(i64_type, 2, "", &(*std::begin(*bb_succ)));
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
      ValueMap &map,
      llvm::Instruction **insert_after) const {
    std::vector<AllocInfo> ret;

    auto ci = cs.getInstruction();
    // First, get the argument
    auto str_id = map.getNamed(name);

    auto len = add_checked_strlen(m, ci, insert_after);

    ret.emplace_back(ci, len, str_id);

    return ret;
  }
};

struct StringAlloc {
  std::vector<AllocInfo> operator()(llvm::Module &m,
      llvm::CallSite &cs,
      ValueMap &,
      llvm::Instruction **insert_after) const {
    std::vector<AllocInfo> ret;

    auto strlen_fcn = m.getFunction("strlen");
    // I may have to create an external linkage for this in some instances...
    //   ugh
    assert(strlen_fcn != nullptr);

    // We have the size of the type, its returned in the return value
    auto ci = cs.getInstruction();

    auto len = add_checked_strlen(m, ci, insert_after);

    ret.emplace_back(ci, len, ValueMap::Id::invalid());

    return ret;
  }
};

struct CTypeAlloc {
  std::vector<AllocInfo> operator()(llvm::Module &m,
      llvm::CallSite &cs,
      ValueMap &map,
      llvm::Instruction **insert_after) const {
    auto i32_type = llvm::IntegerType::get(m.getContext(), 32);
    auto i64_type = llvm::IntegerType::get(m.getContext(), 64);
    std::vector<AllocInfo> ret;

    // We have the size of the type, its returned in the return value
    auto ci = cs.getInstruction();

    // subtract 128 from ci (gep for -128)
    std::vector<llvm::Value *> indicies = {
      llvm::ConstantInt::get(i32_type, -128)
    };

    auto i16_type = llvm::IntegerType::get(m.getContext(), 16);
    auto gep = llvm::GetElementPtrInst::Create(i16_type->getPointerTo(),
        ci, indicies);

    // Insert the gep after "insert_after"
    gep->insertAfter(*insert_after);

    // The ctype array size is:
    //    384 * sizeof(int16_t)
    // ...because that's what the spec says
    auto len = llvm::ConstantInt::get(i64_type, 384*sizeof(int16_t));

    *insert_after = gep;

    ret.emplace_back(gep, len, map.getNamed("ctype"));

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
      ValueMap &,
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
    auto phi = llvm::PHINode::Create(i64_type, 2, "", &(*std::begin(*bb_succ)));
    phi->addIncoming(inc, bb_strlen);
    phi->addIncoming(arg, bb_prev);

    ret.emplace_back(ci, phi, ValueMap::Id::invalid());

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
      ValueMap &,
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
    auto phi = llvm::PHINode::Create(i64_type, 2, "", &(*std::begin(*bb_succ)));
    phi->addIncoming(inc, bb_strlen);
    phi->addIncoming(llvm::ConstantInt::get(i64_type, 0), bb_prev);

    *insert_after = phi;
    ret.emplace_back(ci, phi, ValueMap::Id::invalid());

    return ret;
  }
};
//}}}

// FreeVal Helpers {{{
struct NoFreeData {
  std::vector<llvm::Value *>
  operator()(llvm::Module &, llvm::CallSite &,
      ValueMap &,
      llvm::Instruction **) const {
    return std::vector<llvm::Value *>();
  }
};

template <size_t op_num>
struct FreeOp {
  std::vector<llvm::Value *>
  operator()(llvm::Module &, llvm::CallSite &cs,
      ValueMap &,
      llvm::Instruction **) const {
    return { cs.getArgument(op_num) };
  }
};
//}}}

// AllocInfo helpers {{{
struct AllocInfoNone {
  StaticAllocInfo operator()(llvm::ImmutableCallSite &,
      ModInfo &) const {
    return StaticAllocInfo(AllocStatus::None, nullptr);
  }
};

struct AllocInfoWeak {
  StaticAllocInfo operator()(llvm::ImmutableCallSite &cs,
      ModInfo &info) const {
    auto ci = cs.getInstruction();
    auto inferred_type = findLargestType(info, *ci);
    return StaticAllocInfo(AllocStatus::Weak, inferred_type);
  }
};

struct AllocInfoWeakNS {
  StaticAllocInfo operator()(llvm::ImmutableCallSite &cs,
      ModInfo &) const {
    auto m = cs.getInstruction()->getParent()->getParent()->getParent();
    auto i8_ptr_type = llvm::PointerType::get(
        llvm::IntegerType::get(m->getContext(), 8), 0);
    return StaticAllocInfo(AllocStatus::Weak, i8_ptr_type);
  }
};

template <const char *type_name>
struct AllocInfoWeakType {
  StaticAllocInfo operator()(llvm::ImmutableCallSite &cs,
      ModInfo &) const {
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
bool UnknownExtInfo::insertCallCons(Cg &cg, llvm::ImmutableCallSite &cs,
    const CallInfo &ci) const {
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
    auto ret_id = ci.ret();
    // Load into ret_id from universal value
    cg.add(ConstraintType::Load, ret_id, ret_id, ValueMap::UniversalValue);
  }

  // For each argument:
  auto arg_ids = ci.args();
  size_t argno = 0;
  for (auto it = cs.arg_begin(), en = cs.arg_end();
      it != en; ++it) {
    auto arg_id = arg_ids[argno];

    auto ld_id = cg.vals().createPhonyID();

    cg.add(ConstraintType::Load, ld_id, arg_id, ValueMap::UniversalValue);
    ++argno;
  }

  return false;
}

std::vector<AllocInfo> UnknownExtInfo::getAllocData(
    llvm::Module &m, llvm::CallSite &ci,
    ValueMap &omap,
    llvm::Instruction **insert_after) const {
  llvm::dbgs() << "WARNING: Unknown alloc data: " <<
    ci.getCalledFunction()->getName() << "\n";
  // Do nothing
  return NoAllocData()(m, ci, omap, insert_after);
}

std::vector<llvm::Value *> UnknownExtInfo::getFreeData(
    llvm::Module &m, llvm::CallSite &ci,
    ValueMap &map, llvm::Instruction **insert_after) const {
  /*
  llvm::dbgs() << "WARNING: Unknown free data: " <<
    ci.getCalledFunction()->getName() << "\n";
  */
  // Do nothing
  return NoFreeData()(m, ci, map, insert_after);
}

StaticAllocInfo UnknownExtInfo::getAllocInfo(llvm::ImmutableCallSite &cs,
    ModInfo &info) const {
  auto ci = cs.getInstruction();

  if (llvm::isa<llvm::PointerType>(ci->getType())) {
    // Assume this may be an allocation function, find the largest type
    auto inferred_type = findLargestType(info, *cs.getInstruction());

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
  bool insertCallCons(Cg &cg, llvm::ImmutableCallSite &cs,
      const CallInfo &ci) const override {
    return alloc_cons()(cg, cs, ci);
  }

  std::vector<AllocInfo>
  getAllocData(llvm::Module &m, llvm::CallSite &ci,
      ValueMap &map,
      llvm::Instruction **insert_after) const override {
    return alloc_size()(m, ci, map, insert_after);
  }

  std::vector<llvm::Value *> getFreeData(llvm::Module &m,
      llvm::CallSite &ci,
      ValueMap &map,
      llvm::Instruction **insert_after) const override {
    return free_pointer()(m, ci, map, insert_after);
  }

  StaticAllocInfo getAllocInfo(llvm::ImmutableCallSite &cs,
      ModInfo &info) const override {
    return alloc_info()(cs, info);
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

class ExtQsort :
  public ExtInfoCRTP<QSortCons,
            NoAllocData, NoFreeData,
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
  public ExtInfoCRTP<AllocTypeCons<dirstruct_name>,
          AllocNamedSize<dirstruct_name, 8>, NoFreeData,
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

ExtLibInfo::ExtLibInfo(ModInfo &info) : modInfo_(info) {
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
      std::make_tuple("memalign"),
      std::make_tuple(new Alloc<1>()));
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

  // mmap?
  info_.emplace(std::piecewise_construct,
      std::make_tuple("mmap64"),
      std::make_tuple(new Alloc<1>()));
  /*
  // Perl calls...
  info_.emplace(std::piecewise_construct,
      std::make_tuple("Perl_safesysmalloc"),
      std::make_tuple(new Alloc<0>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("Perl_safesysrealloc"),
      std::make_tuple(new Realloc1Free0()));
  */
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
      std::make_tuple("fdopendir"),
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
      std::make_tuple(new ReturnNamedString<strtok_name>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("stpcpy"),
      std::make_tuple(new ReturnArg<0>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strcat"),
      std::make_tuple(new ReturnArg<0>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("strstr"),
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
      std::make_tuple("localtime_r"),
      std::make_tuple(new ReturnArg<1>()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("gmtime"),
      std::make_tuple(new ReturnNamedStruct<datetime_name,
        datetimestruct_name>()));
  // Returns pointer into library data -- overwritten by next textdomain call...
  info_.emplace(std::piecewise_construct,
      std::make_tuple("textdomain"),
      std::make_tuple(new ReturnNamedString<textdomain_name>()));
  // Returns pointer into pwnam data -- overwritten by next getpwnam
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getpwnam"),
      std::make_tuple(new ReturnNamedStruct<pwnam_name,
        pwnamstruct_name>()));

  // Returns pointer into grnam data -- overwritten by next getgrnam
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getgrnam"),
      std::make_tuple(new ReturnNamedStruct<grnam_name,
        grnamstruct_name>()));

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
      std::make_tuple(new ReturnArg<1>()));

  // Gettext
  info_.emplace(std::piecewise_construct,
      std::make_tuple("gettext"),
      std::make_tuple(new ReturnArgOrStatic<0, gettext_name>()));

  // freopen -- returns arg2
  info_.emplace(std::piecewise_construct,
      std::make_tuple("freopen"),
      std::make_tuple(new ReturnArg<2>()));

  // fgets -- returns the string passed to it
  info_.emplace(std::piecewise_construct,
      std::make_tuple("fgets"),
      std::make_tuple(new ReturnArg<0>()));

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

  info_.emplace(std::piecewise_construct,
      std::make_tuple("readdir"),
      std::make_tuple(
        new ReturnNamedSize<dirent_name, sizeof(struct dirent)>()));
  /*
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

  // Qsort...
  info_.emplace(std::piecewise_construct,
      std::make_tuple("qsort"),
      std::make_tuple(new ExtQsort()));

  // va_start...
  // TODO(ddevec) - store the varargs field from the callinfo for the
  //   callsite's function into the va_arg's 2nd (from 0) idx, store the
  //   va_list's value in its 3rd addr
  /*
  info_.emplace(std::piecewise_construct,
      std::make_tuple("llvm.va_start"),
      std::make_tuple(new VaStart()));
  */

  //}}}

  // Noop external calls {{{
  info_.emplace(std::piecewise_construct,
      std::make_tuple("llvm.va_end"),
      std::make_tuple(new ExtNoop()));
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
      std::make_tuple("unlinkat"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("setenv"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sigaltstack"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sysinfo"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("tputs"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("tcgetattr"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("tcsetattr"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("tcflush"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("tgetflag"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("tgetnum"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("tgetent"),
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
      std::make_tuple("sethostname"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("gethostname"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("listen"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("socketpair"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sendmsg"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("write"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("open"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("openat"),
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
      std::make_tuple("pwrite64"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("pread64"),
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
      std::make_tuple("utimes"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getchar"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("clock_gettime"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("utimensat"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("futimesat"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("futimens"),
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
      std::make_tuple("srandom"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sigsuspend"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sigaction"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sigprocmask"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("sigemptyset"),
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
      std::make_tuple("epoll_create"),
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
  info_.emplace(std::piecewise_construct,
      std::make_tuple("llvm.dbg.declare"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("llvm.dbg.value"),
      std::make_tuple(new ExtNoop()));
  info_.emplace(std::piecewise_construct,
      std::make_tuple("getopt_long"),
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
}  // NOLINT

// Initialize the internal info_ (unordered_map) here
void ExtLibInfo::addGlobalConstraints(const llvm::Module &m, Cg &cg) {
  // Setup constriants for named values
  // -- (->) indicates points-to // address-of
  // env value -> env object
  // envp value -> evnp object
  // argv value -> argv object
  //  arg value -> arg object
  // The argv value always points to the argv object
  // Do store here...
  // First create named objects:
  //   nullptr as they have a size 1 type (array)

  auto &vals = cg.vals();

  // Now do the stores for argv and envp
  // Envp
  {
    auto env_obj_id = vals.createAlloc(nullptr, 1);
    auto envp_obj_id = vals.createAlloc(nullptr, 1);

    auto env_id = vals.getNamed("env");
    auto envp_id = vals.getNamed("envp");

    cg.add(ConstraintType::AddressOf, env_obj_id, env_id);
    cg.add(ConstraintType::AddressOf, envp_obj_id, envp_id);

    auto env_st_id = vals.createPhonyID();
    cg.add(ConstraintType::Store, env_st_id,
        env_id, envp_id);
  }

  // Argv
  {
    auto argv_obj_id = vals.createAlloc(nullptr, 1);
    auto arg_obj_id = vals.createAlloc(nullptr, 1);

    auto argv_id = vals.getNamed("argv");
    auto arg_id = vals.getNamed("arg");

    cg.add(ConstraintType::AddressOf, arg_obj_id, arg_id);
    cg.add(ConstraintType::AddressOf, argv_obj_id, argv_id);

    auto argv_st_id = vals.createPhonyID();
    cg.add(ConstraintType::Store, argv_st_id,
        arg_id, argv_id);
  }

  auto add_constraints = [&cg, &vals] (const char *name, size_t size) {
    auto obj = vals.createAlloc(nullptr, size);
    auto id = vals.getNamed(name);
    cg.add(ConstraintType::AddressOf, obj, id);
  };

  // Now do other named values...
  add_constraints("errno", 1);
  add_constraints("strtok", 1);
  add_constraints("gettext_static", 1);
  add_constraints("dir", 1);
  auto tm_type = m.getTypeByName("struct.tm");
  auto tm_size = modInfo_.getSizeOfType(tm_type);
  add_constraints("datetime_static", tm_size);
  add_constraints("ctype", 1);
  add_constraints("textdomain_static", 1);
  add_constraints("gettext_static", 1);
  add_constraints("terminfo", 1);
  add_constraints("clib", 1);
  add_constraints("locale", 1);
  add_constraints("errno", 1);
  auto pw_type = m.getTypeByName("struct.passwd");
  auto pw_size = modInfo_.getSizeOfType(pw_type);
  add_constraints("pwnam", pw_size);
  auto gr_type = m.getTypeByName("struct.group");
  auto gr_size = modInfo_.getSizeOfType(gr_type);
  add_constraints("grnam", gr_size);

  // Constraints for stdio
  {
    // Create a fileio struct:
    // auto obj = omap.createPhonyObjectIDs(M.getTypeByName("struct._IO_FILE"));
    auto type = m.getTypeByName("struct._IO_FILE");
    auto size = modInfo_.getSizeOfType(type);
    auto stdio_obj = vals.createAlloc(nullptr, size);
    auto stdio_id = vals.getNamed("stdio");

    cg.add(ConstraintType::AddressOf,
        stdio_obj, stdio_id);
  }
}

void ExtLibInfo::init(const llvm::Module &m, ValueMap &map) {  //  NOLINT
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
  map.allocNamed(1, "ctype");
  auto tm_type = m.getTypeByName("struct.tm");
  auto tm_size = modInfo_.getSizeOfType(tm_type);
  map.allocNamed(tm_size, "datetime_static");
  map.allocNamed(1, "textdomain_static");
  map.allocNamed(1, "gettext_static");
  map.allocNamed(1, "terminfo");
  map.allocNamed(1, "clib");
  map.allocNamed(1, "locale");
  map.allocNamed(1, "errno");
  map.allocNamed(1, "dir");
  map.allocNamed(1, "env");
  map.allocNamed(1, "envp");
  map.allocNamed(1, "argv");
  map.allocNamed(1, "arg");
  map.allocNamed(1, "stdio");
  map.allocNamed(1, "strtok");
  map.allocNamed(1, "dirent_static");
  map.allocNamed(1, dirstruct_name);
  auto pw_type = m.getTypeByName("struct.passwd");
  auto pw_size = modInfo_.getSizeOfType(pw_type);
  map.allocNamed(pw_size, "pwnam");
  auto gr_type = m.getTypeByName("struct.group");
  auto gr_size = modInfo_.getSizeOfType(gr_type);
  map.allocNamed(gr_size, "grnam");

  // Does the named data need constraints?
  // Largely no...
  //}}}

  //}}}
}

