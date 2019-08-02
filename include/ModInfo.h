/*
 * Copyright (C) 2016 David Devecsery
 */

#ifndef INCLUDE_MODINFO_H_
#define INCLUDE_MODINFO_H_

#include "llvm/IR/Function.h"

#include "include/util.h"
#include "include/ValueMap.h"

#include <map>
#include <vector>

class ModInfo {
 public:
  class StructInfo {
    //{{{
   public:
    StructInfo(ModInfo &info, const llvm::StructType *type) :
        type_(type) {
      int32_t field_count = 0;
      for (const llvm::Type *element_type : type->elements()) {
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
          auto &struct_info = info.getStructInfo(struct_type);
          sizes_.insert(std::end(sizes_), struct_info.sizes_begin(),
            struct_info.sizes_end());

          // This field is strong if the substruct field was strong, and
          //   we're currently strong
          for (bool sub_strong : struct_info.strongs()) {
            // If we're strong, and their strong the field is strong
            fieldStrong_.push_back(strong & sub_strong);
          }

          field_count += struct_info.numFields();
        } else {
          sizes_.emplace_back(1);
          fieldStrong_.push_back(strong);
          field_count++;
        }
      }
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

    const std::vector<int32_t> &offsets() const {
      return offsets_;
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

    llvm::iterator_range<size_iterator> sizes() {
      return llvm::iterator_range<size_iterator>(sizes_);
    }

    llvm::iterator_range<const_size_iterator> sizes() const {
      return llvm::iterator_range<const_size_iterator>(sizes_);
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

    llvm::iterator_range<strong_iterator> strongs() {
      return llvm::iterator_range<strong_iterator>(fieldStrong_);
    }

    llvm::iterator_range<const_strong_iterator> strongs() const {
      return llvm::iterator_range<const_strong_iterator>(fieldStrong_);
    }

    //}}}

    // Wohoo printing {{{
    friend llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
        const StructInfo &si) {
      // FIXME(ddevec): Cannot do getName on "literal" structs
      // os << "StructInfo( " << si.type()->getName() << ", [";
      os << "StructInfo( [";
      for (int32_t size : si.sizes()) {
        os << " " << size;
      }
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

  ModInfo(llvm::Module &m) {
    std::vector<llvm::StructType *> types =
      m.getIdentifiedStructTypes();
    for (auto type : types) {
      addStructInfo(type);
    }
  }

  ModInfo(const ModInfo &) = delete;
  ModInfo(ModInfo &&) = delete;

  ModInfo &operator=(const ModInfo &) = delete;
  ModInfo &operator=(ModInfo &&) = delete;

  // Handle structure infos

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

  size_t getSizeOfType(const llvm::Type *type) {
    // Strip away any array typing:
    while (auto at = dyn_cast_or_null<llvm::ArrayType>(type)) {
      type = at->getContainedType(0);
    }
    
    if (auto st = dyn_cast_or_null<llvm::StructType>(type)) {
      auto &info = getStructInfo(st);
      return info.size();
    }

    return 1;
  }

 private:
  bool addStructInfo(const llvm::StructType *type) {
    bool ret = true;
    auto it = structInfo_.find(type);
    // llvm::dbgs() << "Adding struct info for: " << type << "\n";

    if (it == std::end(structInfo_)) {
      auto emp_ret = structInfo_.emplace(std::piecewise_construct,
          std::make_tuple(type),
          std::make_tuple(std::reference_wrapper<ModInfo>(*this), type));
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

  std::map<const llvm::StructType *, StructInfo> structInfo_;
  const StructInfo *maxStructInfo_ = nullptr;
};

#endif // INCLUDE_MODINFO_H_
