/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_OBJECTMAP_H_
#define INCLUDE_OBJECTMAP_H_

#include <cstdint>

#include <unordered_map>
#include <utility>
#include <vector>

#include "include/util.h"

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
    // Exported Constant ObjIDs {{{
    typedef ID<omap_id, int32_t, -1> ObjID;

    enum class Type {
      Special,
      Value,
      Object,
      Return,
      VarArg
    };

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
    void addValueFunction(const llvm::Value *val) {
      auto id = __do_add(val, valToID_, idToVal_);
      functions_.push_back(std::make_pair(id, val));
    }

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
    const llvm::Value *valueAtID(ObjID id) const {
      return mapping_.at(id.val());
    }

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

    bool isObject(const ObjID id) const {
      return (id == NullObjectValue || id == UniversalValue ||
          (idToObj_.find(id) != std::end(idToObj_)));
      return (id == NullObjectValue || id == UniversalValue ||
          id == IntValue ||
          (idToObj_.find(id) != std::end(idToObj_)));
    }

    static constexpr ObjID getOffsID(ObjID id, int32_t offs) {
      return ObjID(id.val() + offs);
    }

    ObjID getReturn(const llvm::Value *val) const {
      return __do_get(val, valToID_);
    }

    ObjID getVarArg(const llvm::Value *val) const {
      return __do_get(val, vargToID_);
    }

    // ddevec -- FIXME: Does this really belong here?
    ObjID getConstValue(const llvm::Constant *C) const {
      return __const_node_helper(C, &ObjectMap::getValue, NullValue);
    }

    ObjID getConstValueTarget(const llvm::Constant *C) const {
      return __const_node_helper(C, &ObjectMap::getObject, NullObjectValue);
    }

    std::pair<Type, const llvm::Value *>
    getValueInfo(ObjID id) const;
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

    // Iterators {{{
    typedef std::unordered_map<const llvm::Value *, ObjID>::iterator
      to_id_iterator;
    typedef std::unordered_map<const llvm::Value *, ObjID>::const_iterator
      const_to_id_iterator;

    typedef std::unordered_map<ObjID, const llvm::Value *, ObjID::hasher>
      idToValMap;
    typedef idToValMap::iterator to_val_iterator;
    typedef idToValMap::const_iterator const_to_val_iterator;

    typedef std::vector<std::pair<ObjID, const llvm::Value *>>::iterator
      function_iterator;
    typedef std::vector<std::pair<ObjID, const llvm::Value *>>::const_iterator
      const_function_iterator;

    function_iterator functions_begin() {
      return std::begin(functions_);
    }

    function_iterator functions_end() {
      return std::end(functions_);
    }

    const_function_iterator functions_begin() const {
      return std::begin(functions_);
    }

    const_function_iterator functions_end() const {
      return std::end(functions_);
    }

    const_function_iterator functions_cbegin() const {
      return functions_.cbegin();
    }

    const_function_iterator functions_cend() const {
      return functions_.cend();
    }

    to_val_iterator values_begin() {
      return std::begin(idToVal_);
    }

    to_val_iterator values_end() {
      return std::end(idToVal_);
    }

    const_to_val_iterator values_begin() const {
      return std::begin(idToVal_);
    }

    const_to_val_iterator values_end() const {
      return std::end(idToVal_);
    }

    const_to_val_iterator values_cbegin() const {
      return idToVal_.cbegin();
    }

    const_to_val_iterator values_cend() const {
      return idToVal_.cend();
    }




    //}}}
 private:
    // Private variables {{{
    // Forward mapping
    std::vector<const llvm::Value *> mapping_;
    std::vector<std::pair<ObjID, const llvm::Value *>> functions_;

    // Reverse mapping
    std::unordered_map<const llvm::Value *, ObjID> valToID_;
    std::unordered_map<const llvm::Value *, ObjID> objToID_;
    std::unordered_map<const llvm::Value *, ObjID> retToID_;
    std::unordered_map<const llvm::Value *, ObjID> vargToID_;

    // Reverse mapping
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

    ObjID __do_add(const llvm::Value *val,
        std::unordered_map<const llvm::Value *, ObjID> &mp,
        idToValMap &pm) {
      assert(mp.find(val) == std::end(mp));

      // getNextID must happen before emplace back... ugh
      auto id = getNextID();

      mapping_.emplace_back(val);

      mp.insert(std::make_pair(val, id));
      pm.insert(std::make_pair(id, val));

      return id;
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
        ObjID nullv) const;
  //}}}
  //}}}
};

#endif  // INCLUDE_OBJECTMAP_H_
