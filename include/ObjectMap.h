/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_OBJECTMAP_H_
#define INCLUDE_OBJECTMAP_H_

#include <cstdint>

#include <algorithm>
#include <map>
#include <set>
#include <unordered_map>
#include <utility>
#include <vector>

#include "include/Debug.h"
#include "include/util.h"

// Don't use llvm includes in unit tests
#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Function.h"
#include "llvm/GlobalValue.h"
#include "llvm/Instruction.h"
#include "llvm/Instructions.h"
#include "llvm/Value.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"

class ObjectMap {
  //{{{
 public:
  // Internal types {{{
  // NOTE: I use int32_t for size reasons
  struct omap_id { };
  typedef util::ID<omap_id, int32_t, -1> ObjID;

  typedef std::unordered_map<ObjID, int32_t, ObjID::hasher> StructMap;
  //}}}

  // Exported Constant ObjIDs {{{
  enum class Type {
    Special,
    Value,
    Object,
    Return,
    VarArg
  };

  enum class ObjEnum : int32_t {
    eNullValue = 0,
    eNullObjectValue = 1,
    eIntValue = 2,
    eUniversalValue = 3,
    eAggregateValue = 4,
    ePthreadSpecificValue = 5,
    eArgvValue = 6,
    eArgvValueObject = 7,
    eLocaleObject = 8,
    eCTypeObject = 9,
    eErrnoObject = 10,
    eCLibObject = 11,
    eTermInfoObject = 12,
    eArgvObject = 13,
    eArgvObjectObject = 14,
    eStdIOValue = 15,
    eIoctlValue = 16,
    eDirObject = 17,
    eNumDefaultObjs
  } DefaultObjs;

  // I hate static consts I should find a better fix
  static const ObjID NullValue;
  static const ObjID NullObjectValue;
  static const ObjID IntValue;
  static const ObjID AggregateValue;
  static const ObjID UniversalValue;
  static const ObjID PthreadSpecificValue;
  static const ObjID ArgvValue;
  static const ObjID ArgvValueObject;
  static const ObjID LocaleObject;
  static const ObjID CTypeObject;
  static const ObjID ErrnoObject;
  static const ObjID CLibObject;
  static const ObjID TermInfoObject;
  static const ObjID ArgvObject;
  static const ObjID ArgvObjectObject;
  static const ObjID StdIOObject;
  static const ObjID StdIOValue;
  static const ObjID IoctlValue;
  static const ObjID DirObject;
  //}}}

  static constexpr ObjID getOffsID(ObjID id, int32_t offs) {
    return ObjID(id.val() + offs);
  }

  static void replaceDbgOmap(ObjectMap &omap);

  // Internal classes {{{
  class StructInfo {
    //{{{
   public:
    StructInfo(ObjectMap &omap, const llvm::StructType *type) :
        type_(type) {
      int32_t field_count = 0;
      std::for_each(type->element_begin(), type->element_end(),
          [this, &omap, &field_count]
          (const llvm::Type *element_type) {
        // We start by assuming structure fields are strong
        bool strong = true;

        // If this is an array, strip away the outer typing
        while (auto at = dyn_cast<llvm::ArrayType>(element_type)) {
          strong = false;
          element_type = at->getContainedType(0);
        }

        offsets_.emplace_back(field_count);

        if (auto struct_type =
            dyn_cast<llvm::StructType>(element_type)) {
          auto &struct_info = omap.getStructInfo(struct_type);
          sizes_.insert(std::end(sizes_), struct_info.sizes_begin(),
            struct_info.sizes_end());

          // This field is strong if the substruct field was strong, and
          //   we're currently strong
          std::for_each(struct_info.strong_begin(),
              struct_info.strong_end(),
              [this, &strong] (bool sub_strong) {
            // If we're strong, and their strong the field is strong
            fieldStrong_.push_back(strong & sub_strong);
          });

          field_count += struct_info.numFields();
        } else {
          sizes_.emplace_back(1);
          fieldStrong_.push_back(strong);
          field_count++;
        }
      });
    }

    StructInfo(StructInfo &&) = default;
    StructInfo &operator=(StructInfo &&) = default;

    StructInfo(const StructInfo &) = default;
    StructInfo &operator=(const StructInfo &) = delete;

    // The number of elements in the structure
    int32_t size() const {
      return sizes_.size();
    }

    size_t numSizes() const {
      return sizes_.size();
    }

    size_t numFields() const {
      return offsets_.size();
    }

    int32_t getFieldOffset(int32_t idx) const {
      return offsets_.at(idx);
    }

    int32_t getFieldSize(int32_t idx) const {
      return sizes_.at(idx);
    }

    const llvm::StructType *type() const {
      return type_;
    }

    // ddevec - TODO: Should keep track of if field is within array...
    bool fieldStrong(int32_t idx) const {
      return fieldStrong_.at(idx);
    }

    // Iteration {{{
    typedef std::vector<int32_t>::iterator size_iterator;
    typedef std::vector<int32_t>::const_iterator const_size_iterator;

    size_iterator sizes_begin() {
      return std::begin(sizes_);
    }

    size_iterator sizes_end() {
      return std::end(sizes_);
    }

    const_size_iterator sizes_begin() const {
      return std::begin(sizes_);
    }

    const_size_iterator sizes_end() const {
      return std::end(sizes_);
    }

    const_size_iterator sizes_cbegin() const {
      return std::begin(sizes_);
    }

    const_size_iterator sizes_cend() const {
      return std::end(sizes_);
    }

    typedef std::vector<int8_t>::iterator strong_iterator;
    typedef std::vector<int8_t>::const_iterator const_strong_iterator;

    strong_iterator strong_begin() {
      return std::begin(fieldStrong_);
    }

    strong_iterator strong_end() {
      return std::end(fieldStrong_);
    }

    const_strong_iterator strong_begin() const {
      return std::begin(fieldStrong_);
    }

    const_strong_iterator strong_end() const {
      return std::end(fieldStrong_);
    }

    const_strong_iterator strong_cbegin() const {
      return std::begin(fieldStrong_);
    }

    const_strong_iterator strong_cend() const {
      return std::end(fieldStrong_);
    }

    //}}}

    // Wohoo printing {{{
    friend llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
        const StructInfo &si) {
      // FIXME(ddevec): Cannot do getName on "literal" structs
      // os << "StructInfo( " << si.type()->getName() << ", [";
      os << "StructInfo( [";
      std::for_each(si.sizes_begin(), si.sizes_end(),
          [&os] (int32_t size) {
        os << " " << size;
      });
      os << " ] )";
      return os;
    }
    //}}}

   private:
    // Private Variables {{{
    std::vector<int32_t> offsets_;
    std::vector<int32_t> sizes_;
    std::vector<int8_t> fieldStrong_;
    const llvm::StructType *type_;
    //}}}
    //}}}
  };
  //}}}

  // Constructor/Copiers {{{
  ObjectMap();
  // FIXME: Not strictly safe, with the maxStructInfo pointer, but I don't
  //   want to write a custom constructor which must be contained, for a
  //   corner case that will likely never come back to bite me...
  ObjectMap(const ObjectMap &) = default;
  ObjectMap(ObjectMap &&) = delete;

  ObjectMap &operator=(const ObjectMap &) = default;
  ObjectMap &operator=(ObjectMap &&) = delete;
  //}}}

  // Value insertion {{{
  // Used to create phony identifers for nodes that don't have llvm::Values
  //    (actual program values) associated with them
  ObjID createPhonyID() {
    auto ret = createMapping(nullptr);
    // assert(ret.val() != 191197);
    return ret;
  }

  ObjID createPhonyID(const llvm::Value *val) {
    auto ret = createMapping(val);

    return ret;
  }

  ObjID createPhonyObjectIDs(const llvm::Type *type) {
    while (auto at = dyn_cast<llvm::ArrayType>(type)) {
      type = at->getElementType();
    }

    if (auto st = dyn_cast<llvm::StructType>(type)) {
      auto &struct_info = getStructInfo(st);

      int num_sizes = struct_info.size();
      numObjs_ += num_sizes;
      assert(num_sizes > 0);

      int cur_size = 0;

      auto ret = createMapping(nullptr);
      objIsStruct_.emplace(ret, num_sizes);

      for (int i = 1; i < num_sizes; i++) {
        auto id = createMapping(nullptr);

        objIsStruct_.emplace(id, num_sizes - i);
        cur_size++;
      }

      return ret;
    } else {
      return createMapping(nullptr);
    }
  }

  ObjID createPhonyObjectID(const llvm::Value *val) {
    auto ret = createMapping(val);

    numObjs_++;
    idToObj_.emplace(ret, val);

    return ret;
  }

  // Top level variable/node
  ObjID addValueFunction(const llvm::Value *val) {
    auto id = __do_add(val, valToID_, idToVal_, nullptr);
    functions_.push_back(std::make_pair(id, val));
    functionSet_.insert(id);
    return id;
  }

  void mergeObjRep(ObjID orig_id, ObjID new_id) {
    reps_.merge(orig_id, new_id);
  }

  void addValue(const llvm::Value *val) {
    __do_add(val, valToID_, idToVal_, nullptr);
  }

  void addObjects(const llvm::Type *type, const llvm::Value *val) {
    if (auto st = dyn_cast<llvm::StructType>(type)) {
      auto &struct_info = getStructInfo(st);

      int num_sizes = struct_info.size();
      numObjs_ += num_sizes;
    }

    __do_add_struct(type, val, objToID_, idToObj_, nullptr, &objSet_);
  }

  // Allocation site
  void addObject(const llvm::Value *val) {
    numObjs_++;
    __do_add(val, objToID_, idToObj_, &objSet_);
  }

  // Function return
  void addReturn(const llvm::Value *val) {
    __do_add(val, retToID_, idToRet_, nullptr);
  }

  // Varadic Argument
  void addVarArg(const llvm::Value *val) {
    __do_add(val, vargToID_, idToVararg_, nullptr);
  }
  //}}}

  // Value Retrieval {{{
  const StructMap &getIsStructSet() const {
    return objIsStruct_;
  }

  static bool isSpecial(ObjID id) {
    assert(id.val() >= 0);
    return id.val() < static_cast<int32_t>(ObjEnum::eNumDefaultObjs);
  }

  static void printSpecial(llvm::raw_ostream &o, ObjID id) {
    if (id == NullValue) {
      o << "(NullValue)";
    } else if (id == NullObjectValue) {
      o << "(NullObjectValue)";
    } else if (id == IntValue) {
      o << "(IntValue)";
    } else if (id == AggregateValue) {
      o << "(AggregateValue)";
    } else if (id == UniversalValue) {
      o << "(UniversalValue)";
    } else if (id == PthreadSpecificValue) {
      o << "(PthreadSpecificValue)";
    } else if (id == ArgvValueObject) {
      o << "(Argv val object)";
    } else if (id == ArgvValue) {
      o << "(Argv)";
    } else if (id == StdIOValue) {
      o << "(stdio)";
    } else if (id == ArgvObject) {
      o << "(Argv object)";
    } else if (id == ArgvObjectObject) {
      o << "(Argv obj object)";
    } else if (id == LocaleObject) {
      o << "(locale)";
    } else if (id == CTypeObject) {
      o << "(ctype)";
    } else if (id == ErrnoObject) {
      o << "(errno)";
    } else if (id == CLibObject) {
      o << "(clib)";
    } else if (id == TermInfoObject) {
      o << "(terminfo)";
    } else if (id == ArgvObject) {
      o << "(argv)";
    } else if (id == ArgvObjectObject) {
      o << "(argv obj)";
    } else {
      llvm_unreachable("not special");
    }
  }

  ObjID getRep(ObjID id) const {
    return reps_.find(id);
  }

  const llvm::Value *valueAtRep(ObjID id) const {
    auto rep = reps_.find(id);
    return mapping_.at(rep.val());
  }

  const llvm::Value *valueAtID(ObjID id) const {
    return mapping_.at(id.val());
  }

  ObjID getValueRep(const llvm::Value *val) {
    // This function doesn't support contstants -- except global values
    assert(!llvm::isa<llvm::Constant>(val) ||
        llvm::isa<llvm::GlobalValue>(val));

    auto id = __do_get(val, valToID_);
    auto ret = getRep(id);
    return ret;
  }

  ObjID getValue(const llvm::Value *val) {
    // This function doesn't support contstants -- except global values
    assert(!llvm::isa<llvm::Constant>(val) ||
        llvm::isa<llvm::GlobalValue>(val));

    auto ret = __do_get(val, valToID_);
    return ret;
  }

  // Return for a function
  ObjID getValueReturn(const llvm::Value *val) const {
    return __do_get(val, retToID_);
  }


  ObjID getFunction(const llvm::Function *fcn) const {
    return valToID_.at(cast<const llvm::Value>(fcn));
  }

  ObjID getFunctionRep(const llvm::Function *fcn) const {
    auto ret_id = valToID_.at(cast<const llvm::Value>(fcn));
    return getRep(ret_id);
  }

  const llvm::Function *getFunction(ObjID id) const {
    return cast<const llvm::Function>(idToVal_.at(id));
  }

  // Allocated object id
  ObjID getObject(const llvm::Value *val) {
    auto id = __do_get(val, objToID_);

    // Objects should never be merged
    assert(getRep(id) == id);

    return id;
  }

  bool isObject(const ObjID id) const {
    return (isSpecial(id) ||
        (idToObj_.find(id) != std::end(idToObj_)));
  }

  bool isValue(const ObjID id) const {
    // Also, functions aren't values
    return (idToVal_.find(id) != std::end(idToObj_) &&
        functionSet_.find(id) == std::end(functionSet_));
  }

  ObjID getReturn(const llvm::Value *val) const {
    return __do_get(val, retToID_);
  }

  ObjID getVarArg(const llvm::Value *val) const {
    return __do_get(val, vargToID_);
  }

  ObjID getReturnRep(const llvm::Value *val) const {
    auto id = __do_get(val, retToID_);
    auto ret = getRep(id);
    return ret;
  }

  ObjID getVarArgRep(const llvm::Value *val) const {
    auto id = __do_get(val, vargToID_);
    auto ret = getRep(id);
    return ret;
  }

  // ddevec -- FIXME: Does this really belong here?
  /*
  ObjID getConstValue(const llvm::Constant *C) {
    return __const_node_helper(C, &ObjectMap::getValue, NullValue);
  }

  ObjID getConstValueTarget(const llvm::Constant *C) {
    return __const_node_helper(C, &ObjectMap::getObject, NullObjectValue);
  }
  */

  std::pair<Type, const llvm::Value *>
  getValueInfo(ObjID id) const;
  //}}}

  // Misc helpers {{{
  int64_t getNumObjs() const {
    return numObjs_;
  }

  size_t size() const {
    return mapping_.size();
  }
  //}}}

  // Structure field tracking {{{
  bool addStructInfo(const llvm::StructType *type) {
    bool ret = true;
    auto it = structInfo_.find(type);
    // llvm::dbgs() << "Adding struct info for: " << type << "\n";

    if (it == std::end(structInfo_)) {
      auto emp_ret = structInfo_.emplace(type,
          StructInfo(*this, type));
      assert(emp_ret.second);

      it = emp_ret.first;
      ret = emp_ret.second;

      auto &info = it->second;
      if (maxStructInfo_ == nullptr ||
          info.size() > maxStructInfo_->size()) {
        maxStructInfo_ = &info;
      }
    }


    return ret;
  }

  const StructInfo &getStructInfo(const llvm::StructType *type) {
    auto st_type = cast<llvm::StructType>(type);

    auto struct_info_it = structInfo_.find(st_type);

    // Its not in our struct list, create a new one
    if (struct_info_it == std::end(structInfo_)) {
      addStructInfo(type);

      struct_info_it = structInfo_.find(st_type);
    }

    return struct_info_it->second;
  }

  const StructInfo &getMaxStructInfo() const {
    assert(maxStructInfo_ != nullptr);
    return *maxStructInfo_;
  }

  void addObjAlias(ObjID obj_id, ObjID alias_id) {
    auto it =  objToAliases_.find(obj_id);
    if (it == std::end(objToAliases_)) {
      auto em_ret = objToAliases_.emplace(
          obj_id, std::vector<ObjID>());
      assert(em_ret.second);

      it = em_ret.first;
      it->second.emplace_back(obj_id);
    }

    it->second.emplace_back(alias_id);
    aliasToObjs_[alias_id] = obj_id;
  }

  std::pair<bool, const std::vector<ObjID> &>
  findObjAliases(ObjID obj_id) const {
    // To return on failure;
    static std::vector<ObjID> empty_vector;
    auto it =  objToAliases_.find(obj_id);
    if (it == std::end(objToAliases_)) {
      return std::make_pair(false, std::ref(empty_vector));
    }
    return std::make_pair(true, std::ref(it->second));
  }

  std::pair<bool, ObjID>
  findObjBase(ObjID obj_id) {
    auto it = aliasToObjs_.find(obj_id);
    if (it == std::end(aliasToObjs_)) {
      return std::make_pair(false, ObjID());
    }

    return std::make_pair(true, it->second);
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

  /*
  static bool isPhony(ObjID id) {
    return id.val() >= phonyIdBase;
  }
  */
  //}}}

  // Remapping optimizations {{{
  // Lowers all objects to the lowest set of obj-ids to increase SparseBitmap
  //   efficiency
  util::ObjectRemap<ObjID> lowerObjects() {
    util::ObjectRemap<ObjID> remap(mapping_.size());
    // Find all objects, and lower them...

    // First map through special identifiers
    ObjID remap_id(0);
    for (ObjID i(0);
        i < ObjID(static_cast<int32_t>(ObjEnum::eNumDefaultObjs));
        ++i) {
      remap.set(i, remap_id);
      assert(i == remap_id);
      ++remap_id;
    }

    assert(remap_id == ObjID(static_cast<int32_t>(ObjEnum::eNumDefaultObjs)));

    // Make a place for all of the objects in the remap
    for (auto obj_id : objSet_) {
      remap.set(obj_id, remap_id);
      remap_id++;
    }

    maxObj_ = remap_id;

    // Now handle non-objects...

    // Assert that we haven't repeated any ids...
    // Now remap all of the other values.... uhh is this ideal?
    // I don't really think so... b/c I don't know what the other values are?
    // False -- I do know what the other values are..
    // for id in all_ids:
    //   if id NOT obj (as known by testing objSet_)
    //     remap ID
    for (ObjID i(0); i < ObjID(mapping_.size()); ++i) {
      // If this is special, or an object, don't remap
      if (isSpecial(i) || objSet_.test(i)) {
        continue;
      }

      // Otherwise, remap this sucker
      remap.set(i, remap_id);
      remap_id++;
    }

    assert(static_cast<size_t>(remap_id) == mapping_.size());

    objSet_.clear();

    // Now, update all of our internal structures... meh
    __update_internal(remap);

    return remap;
  }

  // Lowers all used ids, to increase SparseBitmap efficiency
  util::ObjectRemap<ObjID> lowerUsed() {
    util::ObjectRemap<ObjID> remap(mapping_.size());
    // First, loop through all ids, remapping any that are reps
    ObjID remap_id(0);
    for (ObjID i(0); i < ObjID(mapping_.size()); ++i) {
      // If i is a rep, push it
      if (getRep(i) == i) {
        remap.set(i, remap_id);
        ++remap_id;
      }
    }

    // Then, loop through all ids, remapping any that are not reps
    for (ObjID i(0); i < ObjID(mapping_.size()); ++i) {
      // Push all non-reps
      if (getRep(i) != i) {
        remap.set(i, remap_id);
        ++remap_id;
      }
    }

    // FIXME: Should actually be asserting that no mappings in remap map to an
    //   invalid id
    assert(remap.size() == mapping_.size());
    // Update where our maps point
    __update_internal(remap);

    return remap;
  }
  //}}}

 private:
  // Private variables {{{
  // Forward mapping
  std::vector<const llvm::Value *> mapping_;
  std::vector<std::pair<ObjID, const llvm::Value *>> functions_;
  std::set<ObjID> functionSet_;

  // Reverse mapping
  std::unordered_map<const llvm::Value *, ObjID> valToID_;
  std::unordered_map<const llvm::Value *, ObjID> objToID_;
  std::unordered_map<const llvm::Value *, ObjID> retToID_;
  std::unordered_map<const llvm::Value *, ObjID> vargToID_;

  util::SparseBitmap<ObjID> objSet_;
  ObjID maxObj_ = ObjID::invalid();

  // Reverse mapping
  idToValMap idToVal_;
  idToValMap idToObj_;
  idToValMap idToRet_;
  idToValMap idToVararg_;

  // Rep useage (for optimization merging)
  mutable util::UnionFind<ObjID> reps_;

  int64_t numObjs_ = 0;

  // Struct info
  std::map<const llvm::StructType *, StructInfo> structInfo_;
  std::map<ObjID, std::vector<ObjID>> objToAliases_;
  std::map<ObjID, ObjID> aliasToObjs_;
  StructMap objIsStruct_;
  const StructInfo *maxStructInfo_ = nullptr;
  ///}}}

  // Internal helpers {{{
  // FIXME: If this winds up being slow, I don't need to update any of the
  //   object mappings after the first lowerObjects() call...
  static void __remap_valToID(const util::ObjectRemap<ObjID> &remap,
      std::unordered_map<const llvm::Value *, ObjID> &map) {
    for (auto &pr : map) {
      pr.second = remap[pr.second];
    }
  }

  static void __remap_idToVal(const util::ObjectRemap<ObjID> &remap,
      idToValMap &map) {
    idToValMap newmap;

    for (auto &pr : map) {
      // UGH, I don't think htis will acutually work...
      if_debug_enabled(auto rc =)
        newmap.emplace(remap[pr.first], pr.second);
      assert(rc.second);
    }

    map = std::move(newmap);
  }

  void __update_internal(const util::ObjectRemap<ObjID> &remap) {
    // First, do the valToID_ mappings
    __remap_valToID(remap, valToID_);
    __remap_valToID(remap, objToID_);
    __remap_valToID(remap, retToID_);
    __remap_valToID(remap, vargToID_);

    // Now the idToVal_ mappings
    __remap_idToVal(remap, idToVal_);
    __remap_idToVal(remap, idToObj_);
    __remap_idToVal(remap, idToRet_);
    __remap_idToVal(remap, idToVararg_);

    // Then aliases
    std::map<ObjID, std::vector<ObjID>> new_aliases;
    for (auto &pr : objToAliases_) {
      std::vector<ObjID> new_alias_vec(pr.second.size());
      std::transform(std::begin(pr.second), std::end(pr.second),
          std::begin(new_alias_vec),
          [&remap](ObjID alias) { return remap[alias]; });

      if_debug_enabled(auto rc =)
        new_aliases.emplace(remap[pr.first], std::move(new_alias_vec));
      assert(rc.second);
    }
    objToAliases_ = std::move(new_aliases);

    std::map<ObjID, ObjID> new_to_obj;
    for (auto &pr : aliasToObjs_) {
      if_debug_enabled(auto rc =)
        new_to_obj.emplace(remap[pr.first], remap[pr.second]);
      assert(rc.second);
    }
    aliasToObjs_ = std::move(new_to_obj);

    // Then objIsStruct
    StructMap new_obj_is_struct;
    for (auto &pr : objIsStruct_) {
      if_debug_enabled(auto rc =)
        new_obj_is_struct.emplace(remap[pr.first], pr.second);
      assert(rc.second);
    }
    objIsStruct_ = std::move(new_obj_is_struct);

    // And function mappings
    {
      for (auto &pr : functions_) {
        pr.first = remap[pr.first];
      }

      std::set<ObjID> new_fcn_set;
      for (auto &id : functionSet_) {
        new_fcn_set.emplace(remap[id]);
      }
      functionSet_ = std::move(new_fcn_set);
    }

    // Finally redo the mappings
    std::vector<const llvm::Value *> new_mappings(mapping_.size());
    for (ObjID i(0); i < ObjID(mapping_.size()); ++i) {
      new_mappings[remap[i].val()] = mapping_[i.val()];
    }
    mapping_ = std::move(new_mappings);

    // Remap the reps...
    reps_.remap(remap);
  }

  ObjID getNextID() const {
    return ObjID(mapping_.size());
  }

  ObjID createMapping(const llvm::Value *val) {
    ObjID ret = getNextID();
    mapping_.emplace_back(val);
    if_debug_enabled(auto rep_id =)
      reps_.add();
    assert(rep_id == ret);
    // assert(ret.val() >= 0 && ret.val() < phonyIdBase);
    assert(ret.val() >= 0);
    return ret;
  }

  const llvm::Value *__find_helper(ObjID id, const idToValMap &map) const {
    auto it = map.find(id);

    if (it != std::end(map)) {
      return it->second;
    }

    return nullptr;
  }

  ObjID __do_add_struct(const llvm::Type *type,
      const llvm::Value *val,
      std::unordered_map<const llvm::Value *, ObjID> &mp,
      idToValMap &pm, const std::vector<ObjID> *alias,
      util::SparseBitmap<ObjID> *set) {
    ObjID ret_id;

    // Strip away array references:
    while (auto at = dyn_cast<llvm::ArrayType>(type)) {
      type = at->getElementType();
    }

    if (auto st = dyn_cast<llvm::StructType>(type)) {
      // id is the first field of the struct
      // Fill out the struct:
      auto &struct_info = getStructInfo(st);

      int num_sizes = struct_info.size();
      int cur_size = 0;
      // llvm::dbgs() << "Got StructInfo: " << struct_info << "\n";
      bool first = true;
      std::for_each(struct_info.sizes_begin(), struct_info.sizes_end(),
          [this, &ret_id, &alias, &pm, &mp, &first, &val, &num_sizes,
            &cur_size, &set]
          (int32_t) {
        // This is logically reserving an ObjID for this index within the
        //   struct
        ObjID id = createMapping(val);

        if (first) {
          ret_id = id;
          assert(mp.find(val) == std::end(mp));
          mp.emplace(val, id);
          first = false;
        }

        // llvm::dbgs() << "Allocating struct id: " << id << "\n";

        assert(pm.find(id) == std::end(pm));
        pm.emplace(id, val);
        if (set != nullptr) {
          set->set(id);
        }


        objIsStruct_.emplace(id, num_sizes - cur_size);
        cur_size++;
        // Denote which objects this structure field occupies
        if (alias == nullptr) {
          objToAliases_[ret_id].emplace_back(id);
          aliasToObjs_[id] = ret_id;
        } else {
          for (auto &obj_id : *alias) {
            objToAliases_[obj_id].emplace_back(id);
            aliasToObjs_[id] = obj_id;
          }
        }
      });

      assert(ret_id != ObjID::invalid());
    // Not a struct
    } else {
      assert(mp.find(val) == std::end(mp));
      ret_id = createMapping(val);

      mp.emplace(val, ret_id);
      assert(pm.find(ret_id) == std::end(pm));
      pm.emplace(ret_id, val);
      if (alias != nullptr) {
        for (auto &obj_id : *alias) {
          objToAliases_[obj_id].emplace_back(ret_id);
          aliasToObjs_[ret_id] = obj_id;
        }
      }
    }

    return ret_id;
  }

  ObjID __do_add(const llvm::Value *val,
      std::unordered_map<const llvm::Value *, ObjID> &mp,
      idToValMap &pm, util::SparseBitmap<ObjID> *set) {
    ObjID id;

    assert(mp.find(val) == std::end(mp));

    id = createMapping(val);

    mp.emplace(val, id);
    pm.emplace(id, val);
    if (set != nullptr) {
      set->set(id);
    }

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

  //}}}
  //}}}
};

// structure identification/offset helpers {{{

// Gets the type of a value, stripping the first layer of bitcasts if needed
// NOTE: Does not strip away pointer type
[[ gnu::unused ]]
static const llvm::Type *getTypeOfVal(llvm::Value *val) {
  auto ret = val->getType();

  if (auto ce = dyn_cast<llvm::ConstantExpr>(val)) {
    if (ce->getOpcode() == llvm::Instruction::BitCast) {
      // Also strip away pointer type
      ret = ce->getOperand(0)->getType();
    }
  }

  return ret;
}

// called from malloc-like allocations, to find the largest strcuture size the
// untyped allocation is cast to.
// FIXME: Should put somewhere I don't have to deal with unused warnings
[[ gnu::unused ]]
static const llvm::Type *findLargestType(ObjectMap &omap,
    const llvm::Instruction &ins) {
  auto biggest_type = ins.getType()->getContainedType(0);

  bool found = false;
  int32_t max_size = 0;

  // Strip any array qualifiers
  while (auto at = dyn_cast<llvm::ArrayType>(biggest_type)) {
    biggest_type = at->getElementType();
  }

  // If its a struct type, update our lragest size
  if (auto st = dyn_cast<llvm::StructType>(biggest_type)) {
    max_size = omap.getStructInfo(st).size();
  }

  // now, see how each use is cast...
  std::for_each(ins.use_begin(), ins.use_end(),
      [&max_size, &found, &biggest_type, &omap]
      (const llvm::User *use) {
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

// FIXME: Should put somewhere I don't have to deal with unused warnings
// NOTE: User can be both a ConstantExpr, and a GetElementPtrInst
[[ gnu::unused ]]
static int32_t getGEPOffs(ObjectMap &omap, const llvm::User &gep) {
  int32_t offs = 0;

  // This loop is essentially to handle the nested nature of
  //   GEP instructions
  // It basically says, For the outer-layer of the struct
  for (auto gi = llvm::gep_type_begin(gep),
        en = llvm::gep_type_end(gep);
      gi != en; ++gi) {
    auto type = *gi;
    auto struct_type = dyn_cast<llvm::StructType>(type);
    // If it isn't a struct field, don't add subfield offsets
    if (struct_type == nullptr) {
      continue;
    }

    auto &si = omap.getStructInfo(cast<llvm::StructType>(type));

    auto operand = gi.getOperand();

    // Get the offset from this const value
    auto cons_op = dyn_cast<llvm::ConstantInt>(operand);
    assert(cons_op);
    uint32_t idx = cons_op ? cons_op->getZExtValue() : 0;

    // Add the translated offset
    offs += si.getFieldOffset(idx);
  }

  return offs;
}

// }}}

// For debug only, not guaranteed to persist
extern ObjectMap *g_omap;

// Also for debug, using g_omap
class ValPrint {
  //{{{
 public:
    explicit ValPrint(ObjectMap::ObjID id) : id_(id), omap_(g_omap) { }
    ValPrint(ObjectMap::ObjID id, const ObjectMap &omap) : id_(id),
        omap_(&omap) { }

    friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
        const ValPrint &pr) {
      // If its not in the map, its probably been added later as an indirect
      // object...
      auto val = pr.omap_->valueAtID(pr.id_);

      if (val != nullptr) {
        if (auto gv = dyn_cast<const llvm::GlobalValue>(val)) {
          o << gv->getName();
        } else if (auto fcn = dyn_cast<const llvm::Function>(val)) {
          o << fcn->getName();
        } else if (auto bb = dyn_cast<const llvm::BasicBlock>(val)) {
          o << bb->getParent()->getName() << ": " << bb->getName();
        } else {
          o << *val;
        }
      } else {
        // If its a special value:
        if (ObjectMap::isSpecial(pr.id_)) {
          ObjectMap::printSpecial(o, pr.id_);
        } else {
          o << "(null)";
        }
      }
      return o;
    }

 private:
    ObjectMap::ObjID id_;
    const ObjectMap *omap_;
  //}}}
};

class FullValPrint {
  //{{{
 public:
    explicit FullValPrint(ObjectMap::ObjID id) : id_(id), omap_(g_omap) { }
    FullValPrint(ObjectMap::ObjID id, const ObjectMap &omap) : id_(id),
        omap_(&omap) { }

    friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
        const FullValPrint &pr) {
      // If its not in the map, its probably been added later as an indirect
      // object...
      auto val = pr.omap_->valueAtID(pr.id_);

      if (val != nullptr) {
        if (auto gv = dyn_cast<const llvm::GlobalValue>(val)) {
          o << gv->getName();
        } else if (auto fcn = dyn_cast<const llvm::Function>(val)) {
          o << fcn->getName();
        } else if (auto bb = dyn_cast<const llvm::BasicBlock>(val)) {
          o << bb->getParent()->getName() << ": " << bb->getName();
        } else if (auto arg = dyn_cast<const llvm::Argument>(val)) {
          o << arg->getParent()->getName() << ": " << *val;
        } else if (auto ins = dyn_cast<const llvm::Instruction>(val)) {
          o << ins->getParent()->getParent()->getName() << ": " << *val;
        } else {
          o << *val;
        }
      } else {
        // If its a special value:
        if (ObjectMap::isSpecial(pr.id_)) {
          ObjectMap::printSpecial(o, pr.id_);
        } else {
          o << "(null)";
        }
      }
      return o;
    }

 private:
    ObjectMap::ObjID id_;
    const ObjectMap *omap_;
  //}}}
};

#endif  // INCLUDE_OBJECTMAP_H_
