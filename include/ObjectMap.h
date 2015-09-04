/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_OBJECTMAP_H_
#define INCLUDE_OBJECTMAP_H_

#include <cstdint>

#include <map>
#include <unordered_map>
#include <utility>
#include <vector>

#include "include/util.h"

#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Function.h"
#include "llvm/GlobalValue.h"
#include "llvm/Instruction.h"
#include "llvm/Value.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

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
      ePthreadSpecificValue,
      eNumDefaultObjs
    } DefaultObjs;

    // I hate static consts I should find a better fix
    static const ObjID NullValue;
    static const ObjID NullObjectValue;
    static const ObjID IntValue;
    static const ObjID UniversalValue;
    static const ObjID PthreadSpecificValue;
    //}}}

    // Internal classes {{{
    class StructInfo {
      //{{{
     public:
        StructInfo(ObjectMap &omap, const llvm::StructType *type) :
            type_(type) {
          int32_t field_count = 0;
          llvm::dbgs() << "Creating struct info for: " << type->getName() <<
            "\n";
          std::for_each(type->element_begin(), type->element_end(),
              [this, &omap, &field_count]
              (const llvm::Type *element_type) {
            // If this is an array, strip away the outer typing
            llvm::dbgs() << "  Have element type!!!\n";
            while (auto at = llvm::dyn_cast<llvm::ArrayType>(element_type)) {
              element_type = at;
            }

            llvm::dbgs() << "Adding field to offsets_" << "\n";
            offsets_.emplace_back(field_count);

            if (auto struct_type =
                llvm::dyn_cast<llvm::StructType>(element_type)) {
              auto &struct_info = omap.getStructInfo(struct_type);

              llvm::dbgs() << "Inserting sizes from nested struct!\n";
              sizes_.insert(std::end(sizes_), struct_info.sizes_begin(),
                struct_info.sizes_end());
              field_count += struct_info.numFields();
            } else {
              llvm::dbgs() << "Inserting size 1\n";
              sizes_.emplace_back(1);
              field_count++;
            }


            llvm::dbgs() << "end loop iter, have sizes: ";
            for (auto size : sizes_) {
              llvm::dbgs() << " " << size;
            }
            llvm::dbgs() << "\n";
          });

          if (omap.maxStructInfo_ == nullptr ||
              size() > omap.maxStructInfo_->size()) {
            omap.maxStructInfo_ = this;
          }

          llvm::dbgs() << "End of create: " << *this << "\n";
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
        //}}}

        // Wohoo printing {{{
        friend llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
            const StructInfo &si) {
          os << "StructInfo( " << si.type()->getName() << ", [";
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
    // Top level variable/node
    ObjID addValueFunction(const llvm::Value *val) {
      auto id = __do_add(val, valToID_, idToVal_);
      functions_.push_back(std::make_pair(id, val));
      return id;
    }

    void addValue(const llvm::Value *val) {
      __do_add(val, valToID_, idToVal_);
    }

    ObjID addObject(const llvm::StructType *ty, const llvm::Value *val) {
      return allocStructSpace(ty, val, idToObj_);
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
      if (isPhony(id)) {
        return nullptr;
      }
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


    ObjID getFunction(const llvm::Function *fcn) const {
      return valToID_.at(llvm::cast<const llvm::Value>(fcn));
    }

    const llvm::Function *getFunction(ObjID id) const {
      return llvm::cast<const llvm::Function>(idToVal_.at(id));
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
      return createMapping(nullptr);
    }
    //}}}

    // Structure field tracking {{{
    bool addStructInfo(const llvm::StructType *type) {
      auto emp_ret = structInfo_.emplace(type, StructInfo(*this, type));
      assert(emp_ret.second);

      return emp_ret.second;
    }

    const StructInfo &getStructInfo(const llvm::StructType *type) {
      auto st_type = llvm::cast<llvm::StructType>(type);

      auto struct_info_it = structInfo_.find(st_type);

      // Its not in our struct list, create a new one
      if (struct_info_it == std::end(structInfo_)) {
        auto emp_ret = structInfo_.emplace(st_type, StructInfo(*this, st_type));
        assert(emp_ret.second);
        struct_info_it = emp_ret.first;
      }

      return struct_info_it->second;
    }

    const StructInfo &getMaxStructInfo() const {
      return *maxStructInfo_;
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

    // Struct info
    std::map<const llvm::StructType *, StructInfo> structInfo_;
    const StructInfo *maxStructInfo_ = nullptr;

    IDGenerator<ObjID, 1<<30> phonyIdGen_;
    ///}}}

    // Internal helpers {{{
    bool isPhony(ObjID id) const {
      return id.val() >= (1<<30);
    }
    ObjID getNextID() const {
      return ObjID(mapping_.size());
    }

    ObjID createMapping(const llvm::Value *val) {
      ObjID ret = getNextID();
      mapping_.emplace_back(val);
      assert(ret.val() >= 0 && ret.val() < (1<<30));
      return ret;
    }

    const llvm::Value *__find_helper(ObjID id, const idToValMap &map) const {
      auto it = map.find(id);

      if (it != std::end(map)) {
        return it->second;
      }

      return nullptr;
    }

    ObjID allocStructSpace(const llvm::StructType *struct_type,
        const llvm::Value *val, idToValMap &pm, bool skip_first = false) {
      ObjID ret;
      // id is the first field of the struct
      // Fill out the struct:
      auto &struct_info = getStructInfo(struct_type);

      llvm::dbgs() << "Got StructInfo: " << struct_info << "\n";
      bool first = true;
      std::for_each(struct_info.sizes_begin(), struct_info.sizes_end(),
          [this, &ret, &pm, &first, &skip_first, &val] (int32_t) {
        // This is logically reserving an ObjID for this index within the
        //   struct

        ObjID id;
        if (first) {
          if (!skip_first) {
            id = createMapping(val);
            auto em_ret = pm.emplace(id, val);
            assert(em_ret.second);
          }
          ret = id;
          first = false;
        } else {
          id = createMapping(val);
          auto em_ret = pm.emplace(id, val);
          assert(em_ret.second);
        }
      });

      assert(ret != ObjID::invalid());
      return ret;
    }

    ObjID __do_add(const llvm::Value *val,
        std::unordered_map<const llvm::Value *, ObjID> &mp,
        idToValMap &pm) {
      ObjID id;

      assert(mp.find(val) == std::end(mp));

      id = createMapping(val);

      mp.emplace(val, id);
      pm.emplace(id, val);

      // If its a struct we must preserve an ObjID per field
      if (auto struct_type = llvm::dyn_cast<llvm::StructType>(val->getType())) {
        allocStructSpace(struct_type, val, pm, true);
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

    ObjID __const_node_helper(const llvm::Constant *C,
        ObjID (ObjectMap::*diff)(const llvm::Value *) const,
        ObjID nullv) const;
  //}}}
  //}}}
};

// For debug only, not guaranteed to persist
extern ObjectMap *g_omap;

// Also for debug, using g_omap
class ValPrint {
  //{{{
 public:
    explicit ValPrint(ObjectMap::ObjID id) : id_(id) { }

    friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
        const ValPrint &pr) {
      auto val = g_omap->valueAtID(pr.id_);

      if (val != nullptr) {
        if (auto gv = llvm::dyn_cast<const llvm::GlobalValue>(val)) {
          o << gv->getName();
        } else if (auto fcn = llvm::dyn_cast<const llvm::Function>(val)) {
          o << fcn->getName();
        } else {
          o << *val;
        }
      } else {
        o << "(null)";
      }
      return o;
    }

 private:
    ObjectMap::ObjID id_;
  //}}}
};

#endif  // INCLUDE_OBJECTMAP_H_
