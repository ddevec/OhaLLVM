/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_OBJECTMAP_H_
#define INCLUDE_OBJECTMAP_H_

#include <cstdint>

#include <unordered_map>
#include <utility>
#include <vector>

#include "include/id.h"

#include "llvm/Constants.h"
#include "llvm/GlobalValue.h"
#include "llvm/Instruction.h"
#include "llvm/Value.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

struct omap_id { };

class ObjectMap {
  //{{{
 public:
    typedef ID<omap_id, int32_t, -1> ObjID;

    enum class Type {
      Special,
      Value,
      Object,
      Return,
      VarArg
    };

    // Exported Constant ObjIDs {{{
    static enum ObjEnum : int32_t {
      eNullValue = 0,
      eNullObjectValue,
      eIntValue,
      eUniversalValue,
      ePthreadSpecificValue,
      eNumDefaultObjs
    } DefaultObjs;

    // I hate static consts I should find a better fix
    static const ObjID NullValue;
    static const ObjID NullObjectValue;
    static const ObjID IntValue;
    static const ObjID UniversalValue;
    static const ObjID PthreadSpecificValue;
    //}}};

    // Constructor/Copiers {{{
    ObjectMap();
    ObjectMap(const ObjectMap &) = delete;
    ObjectMap(ObjectMap &&) = delete;

    ObjectMap &operator=(const ObjectMap &) = delete;
    ObjectMap &operator=(ObjectMap &&) = delete;
    //}}}

    // Value insertion {{{
    // Top level variable/node
    void addValue(const llvm::Value *val) {
      __do_add(val, valToID_, idToVal_);
    }

    // Allocation site
    void addObject(const llvm::Value *val) {
      __do_add(val, objToID_, idToObj_);
    }
    // Function return
    void addReturn(const llvm::Value *val) {
      __do_add(val, retToID_, idToRet_);
    }

    // Varadic Argument
    void addVarArg(const llvm::Value *val) {
      __do_add(val, vargToID_, idToVararg_);
    }
    //}}}

    // Value Retrieval {{{
    ObjID getValue(const llvm::Value *val) const {
      // Check for a constant first
      if (auto C = llvm::dyn_cast<const llvm::Constant>(val)) {
        if (!llvm::isa<llvm::GlobalValue>(C)) {
          return getConstValue(C);
        }
      }

      auto ret = __do_get(val, valToID_);
      return ret;
    }
    // Return for a function
    ObjID getValueReturn(const llvm::Value *val) const {
      return __do_get(val, retToID_);
    }
    // Allocated object id
    ObjID getObject(const llvm::Value *val) const {
      return __do_get(val, objToID_);
    }

    static constexpr ObjID getOffsID(ObjID id, int32_t offs) {
      return ObjID(id.val() + offs);
    }

    ObjID getReturn(const llvm::Value *val) const {
      auto id = __do_get(val, valToID_);
    }

    ObjID getVarArg(const llvm::Value *val) const {
      auto id = __do_get(val, vargToID_);
    }

    // ddevec -- FIXME: Does this really belong here?
    ObjID getConstValue(const llvm::Constant *C) const {
      __const_node_helper(C, &ObjectMap::getValue, NullValue);
    }

    ObjID getConstValueTarget(const llvm::Constant *C) const {
      __const_node_helper(C, &ObjectMap::getObject, NullObjectValue);
    }

    std::pair<Type, const llvm::Value *>
    getValueInfo(ObjID id) const {
      if (id.val() < eNumDefaultObjs) {
        return std::make_pair(Type::Special, nullptr);
      }

      auto val = __find_helper(id, idToVal_);
      if (val != nullptr) {
        return std::make_pair(Type::Value, val);
      }

      val = __find_helper(id, idToObj_);
      if (val != nullptr) {
        return std::make_pair(Type::Object, val);
      }

      val = __find_helper(id, idToRet_);
      if (val != nullptr) {
        return std::make_pair(Type::Return, val);
      }

      val = __find_helper(id, idToVararg_);
      if (val != nullptr) {
        return std::make_pair(Type::VarArg, val);
      }

      llvm_unreachable("Couldn't Find id!!");
      return std::make_pair(Type::Value, nullptr);
    }
    //}}}

    // Misc helpers {{{
    size_t size() const {
      return mapping_.size();
    }

    ObjID makeTempValue() {
      auto ret = getNextID();
      mapping_.push_back(nullptr);

      return ret;
    }
    //}}}

 private:
    // Private variables {{{
    // Forward mapping
    std::vector<const llvm::Value *> mapping_;

    // Reverse mapping
    std::unordered_map<const llvm::Value *, ObjID> valToID_;
    std::unordered_map<const llvm::Value *, ObjID> objToID_;
    std::unordered_map<const llvm::Value *, ObjID> retToID_;
    std::unordered_map<const llvm::Value *, ObjID> vargToID_;

    // Reverse mapping
    typedef std::unordered_map<ObjID, const llvm::Value *, ObjID::hasher>
      idToValMap;
    idToValMap idToVal_;
    idToValMap idToObj_;
    idToValMap idToRet_;
    idToValMap idToVararg_;
    ///}}}

    // Internal helpers {{{
    ObjID getNextID() const {
      return ObjID(mapping_.size());
    }

    const llvm::Value *__find_helper(ObjID id, const idToValMap &map) const {
      auto it = map.find(id);

      if (it != std::end(map)) {
        return it->second;
      }

      return nullptr;
    }

    void __do_add(const llvm::Value *val,
        std::unordered_map<const llvm::Value *, ObjID> &mp,
        idToValMap &pm) {
      assert(mp.find(val) == std::end(mp));

      // getNextID must happen before emplace back... ugh
      auto id = getNextID();

      mapping_.emplace_back(val);

      mp.insert(std::make_pair(val, id));
      pm.insert(std::make_pair(id, val));
    }

    ObjID __do_get(const llvm::Value *val,
        const std::unordered_map<const llvm::Value *, ObjID> &mp) const {
      auto it = mp.find(val);

      if (it == std::end(mp)) {
        return ObjectMap::NullValue;
      }

      return it->second;
    }

    ObjID __const_node_helper(const llvm::Constant *C,
        ObjID (ObjectMap::*diff)(const llvm::Value *) const,
        ObjID nullv) const {
      if (llvm::isa<const llvm::ConstantPointerNull>(C) ||
          llvm::isa<const llvm::UndefValue>(C)) {
        return nullv;
      } else if (auto GV = llvm::dyn_cast<llvm::GlobalValue>(C)) {
        return (this->*diff)(GV);
      } else if (auto CE = llvm::dyn_cast<llvm::ConstantExpr>(C)) {
        switch (CE->getOpcode()) {
          case llvm::Instruction::GetElementPtr:
            return __const_node_helper(CE->getOperand(0), diff, nullv);
          case llvm::Instruction::IntToPtr:
            return UniversalValue;
          case llvm::Instruction::PtrToInt:
            return IntValue;
          case llvm::Instruction::BitCast:
            return __const_node_helper(CE->getOperand(0), diff, nullv);
          default:
            llvm::errs() << "Const Expr not yet handled: " << *CE << "\n";
            llvm_unreachable(0);
        }
      } else {
        llvm_unreachable("Unknown constant expr ptr");
      }
    }
  //}}}
  //}}}
};

#endif  // INCLUDE_OBJECTMAP_H_
