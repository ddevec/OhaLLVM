/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_OBJECTMAP_H_
#define INCLUDE_OBJECTMAP_H_

#include <cstdint>

#include <map>
#include <set>
#include <unordered_map>
#include <utility>
#include <vector>

#include "include/Debug.h"
#include "include/util.h"

// Don't use llvm includes in unit tests
#ifndef SPECSFS_IS_TEST
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
#endif

class ObjectMap {
  //{{{
 public:
    // Internal types {{{
    // NOTE: I use int32_t for size reasons
    struct omap_id { };
    typedef ID<omap_id, int32_t> ObjID;
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
      eNullObjectValue,
      eIntValue,
      eUniversalValue,
      eAggregateValue,
      ePthreadSpecificValue,
      eArgvValue,
      eArgvObjectValue,
      eLocaleObject,
      eCTypeObject,
      eErrnoObject,
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
    static const ObjID ArgvObjectValue;
    static const ObjID LocaleObject;
    static const ObjID CTypeObject;
    static const ObjID ErrnoObject;
    //}}}

    static constexpr ObjID getOffsID(ObjID id, int32_t offs) {
      return ObjID(id.val() + offs);
    }

#ifdef SPECSFS_IS_TEST
};
#else

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

        StructInfo(const StructInfo &) = delete;
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
    ObjectMap(const ObjectMap &) = delete;
    ObjectMap(ObjectMap &&) = delete;

    ObjectMap &operator=(const ObjectMap &) = delete;
    ObjectMap &operator=(ObjectMap &&) = delete;
    //}}}

    // Value insertion {{{
    // Used to create phony identifers for nodes that don't have values
    ObjID createPhonyID() {
      return phonyIdGen_.next();
    }

    ObjID createPhonyID(const llvm::Value *val) {
      auto ret = phonyIdGen_.next();

      assert(phonyMap_.find(ret) == std::end(phonyMap_));
      phonyMap_.emplace(ret, val);

      return ret;
    }

    ObjID createPhonyObjectID(const llvm::Value *val) {
      auto ret = phonyIdGen_.next();

      assert(phonyMap_.find(ret) == std::end(phonyMap_));
      idToObj_.emplace(ret, val);

      return ret;
    }
    // Top level variable/node
    ObjID addValueFunction(const llvm::Value *val) {
      auto id = __do_add(val, valToID_, idToVal_);
      functions_.push_back(std::make_pair(id, val));
      return id;
    }

    void addValues(const llvm::Type *type, const llvm::Value *val) {
      __do_add_struct(type, val, valToID_, idToVal_, nullptr);
    }

    void addValue(const llvm::Value *val) {
      __do_add(val, valToID_, idToVal_);
    }

    void addObjects(const llvm::Type *type, const llvm::Value *val) {
      __do_add_struct(type, val, objToID_, idToObj_, nullptr);
    }

    void addObjectsAlias(const llvm::Type *type, const llvm::Value *val,
        const std::vector<ObjID> &alias) {
      __do_add_struct(type, val, objToID_, idToObj_, &alias);
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
    const std::map<ObjID, int32_t> &getIsStructSet() const {
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
      } else if (id == ArgvObjectValue) {
        o << "(Argv object)";
      } else if (id == ArgvValue) {
        o << "(Argv)";
      } else if (id == LocaleObject) {
        o << "(locale)";
      } else if (id == CTypeObject) {
        o << "(ctype)";
      } else if (id == ErrnoObject) {
        o << "(errno)";
      } else {
        llvm_unreachable("not special");
      }
    }

    const llvm::Value *valueAtID(ObjID id) const {
      if (isPhony(id)) {
        auto phony_it = phonyMap_.find(id);
        if (phony_it != std::end(phonyMap_)) {
          return phony_it->second;
        }
        return nullptr;
      }
      return mapping_.at(id.val());
    }

    ObjID getValue(const llvm::Value *val) {
      // Check for a constant first
      if (auto C = dyn_cast<const llvm::Constant>(val)) {
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


    ObjID getFunction(const llvm::Function *fcn) const {
      return valToID_.at(cast<const llvm::Value>(fcn));
    }

    const llvm::Function *getFunction(ObjID id) const {
      return cast<const llvm::Function>(idToVal_.at(id));
    }

    // Allocated object id
    ObjID getObject(const llvm::Value *val) {
      return __do_get(val, objToID_);
    }

    bool isObject(const ObjID id) const {
      return (id == NullObjectValue || id == UniversalValue ||
          (idToObj_.find(id) != std::end(idToObj_)));
      return (id == NullObjectValue || id == UniversalValue ||
          id == IntValue ||
          (idToObj_.find(id) != std::end(idToObj_)));
    }

    ObjID getReturn(const llvm::Value *val) const {
      return __do_get(val, retToID_);
    }

    ObjID getVarArg(const llvm::Value *val) const {
      return __do_get(val, vargToID_);
    }

    // ddevec -- FIXME: Does this really belong here?
    ObjID getConstValue(const llvm::Constant *C) {
      return __const_node_helper(C, &ObjectMap::getValue, NullValue);
    }

    ObjID getConstValueTarget(const llvm::Constant *C) {
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
      return createMapping(nullptr);
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
    idToValMap phonyMap_;

    // Struct info
    std::map<const llvm::StructType *, StructInfo> structInfo_;
    std::map<ObjID, std::vector<ObjID>> objToAliases_;
    std::map<ObjID, int32_t> objIsStruct_;
    const StructInfo *maxStructInfo_ = nullptr;

    static constexpr int32_t phonyIdBase = 1<<30;
    IDGenerator<ObjID, phonyIdBase> phonyIdGen_;
    ///}}}

    // Internal helpers {{{
    bool isPhony(ObjID id) const {
      return id.val() >= phonyIdBase;
    }
    ObjID getNextID() const {
      return ObjID(mapping_.size());
    }

    ObjID createMapping(const llvm::Value *val) {
      ObjID ret = getNextID();
      mapping_.emplace_back(val);
      assert(ret.val() >= 0 && ret.val() < phonyIdBase);
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
        idToValMap &pm, const std::vector<ObjID> *alias) {
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
              &cur_size]
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


          objIsStruct_.emplace(id, num_sizes-cur_size);
          cur_size++;
          // Denote which objects this structure field occupies
          if (alias == nullptr) {
            objToAliases_[ret_id].emplace_back(id);
          } else {
            for (auto &obj_id : *alias) {
              objToAliases_[obj_id].emplace_back(id);
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
          }
        }
      }

      return ret_id;
    }

    ObjID __do_add(const llvm::Value *val,
        std::unordered_map<const llvm::Value *, ObjID> &mp,
        idToValMap &pm) {
      ObjID id;

      assert(mp.find(val) == std::end(mp));

      id = createMapping(val);

      mp.emplace(val, id);
      pm.emplace(id, val);

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
        ObjID (ObjectMap::*diff)(const llvm::Value *),
        ObjID nullv);
  //}}}
  //}}}
};

// structure identification/offset helpers {{{

// Gets the type of a value, stripping the first layer of bitcasts if needed
// NOTE: Does not strip away pointer type
__attribute__((unused))
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
__attribute__((unused))
static const llvm::Type *findLargestType(ObjectMap &omap,
    const llvm::Instruction &ins) {
  auto biggest_type = ins.getType()->getContainedType(0);

  bool found = false;
  int32_t max_size = 0;

  while (auto at = dyn_cast<llvm::ArrayType>(biggest_type)) {
    biggest_type = at->getElementType();
  }

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
__attribute__((unused))
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
    ValPrint(ObjectMap::ObjID id, ObjectMap &omap) : id_(id), omap_(&omap) { }

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
    ObjectMap *omap_;
  //}}}
};

#endif  // SPECSFS_IS_TEST

#ifdef SPECSFS_IS_TEST
class ValPrint {
  //{{{
 public:
    explicit ValPrint(ObjectMap::ObjID id) : id_(id) { }

    friend dbg_type &operator<<(dbg_type &o,
        const ValPrint &pr) {
      o << pr.id_;
      return o;
    }

 private:
    ObjectMap::ObjID id_;
  //}}}
};
#endif

#endif  // INCLUDE_OBJECTMAP_H_
