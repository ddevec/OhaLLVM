/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_DUG_H_
#define INCLUDE_DUG_H_

#include <cstdint>

#include <list>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "include/id.h"
#include "include/ObjectMap.h"

class PtsSet {
  //{{{
 public:
    PtsSet() = default;

 private:
  //}}}
};

class Constraint {
  //{{{
 public:
    enum class Type { Copy, Load, Store, AddressOf };

    Constraint(Type t, ObjectMap::ObjID d, ObjectMap::ObjID s);
    Constraint(Type t, ObjectMap::ObjID d, ObjectMap::ObjID s, int32_t o);

    Type type() const {
      return type_;
    }

    ObjectMap::ObjID src() const {
      return src_;
    }

    ObjectMap::ObjID dest() const {
      return dest_;
    }

    int32_t offs() const {
      return offs_;
    }

    bool targetIsDest() const {
      // Okay, which target is the target of node?
      switch (type_) {
        case Type::AddressOf:
          return true;
        case Type::Load:
          return false;
        case Type::Store:
          return true;
        default:
          return false;
      }
    }

    ObjectMap::ObjID getTarget() const {
      if (targetIsDest()) {
        return dest();
      } else {
        return src();
      }
    }

 private:
    Type type_;

    ObjectMap::ObjID src_;
    ObjectMap::ObjID dest_;

    int32_t offs_ = 0;
  //}}}
};

class DUG {
  //{{{
 public:
    struct dug_id { };
    typedef ObjectMap::ObjID ObjID;

    DUG() = default;

    // No copy/move semantics
    DUG(const DUG &) = delete;
    DUG(DUG &&) = delete;

    DUG &operator=(const DUG &) = delete;
    DUG &operator=(DUG &&) = delete;

    void prepare(const ObjectMap &omap);

    void add(Constraint::Type, ObjID d, ObjID s, int32_t o = 0);

    ObjID addNode(ObjectMap &omap);

    void addIndirectCall(ObjID id, const llvm::Value *val);

    void addIndirect(const llvm::Value *v, Constraint::Type type,
        ObjID d, ObjID s, int32_t o = 0);

    void associateNode(ObjID node, const llvm::Value *val);

    // ddevec - FIXME: this is sloppy, should clean up
    const llvm::Value *getValue(ObjID node) const {
      return nodes_[node.val()].value();
    }

    // Iterate?
    typedef std::vector<Constraint>::iterator constraint_iterator;
    typedef std::vector<Constraint>::const_iterator const_constraint_iterator;

    constraint_iterator constraint_begin() {
      return std::begin(constraints_);
    }

    constraint_iterator constraint_end() {
      return std::end(constraints_);
    }

    const_constraint_iterator constraint_begin() const {
      return std::begin(constraints_);
    }

    const_constraint_iterator constraint_end() const {
      return std::end(constraints_);
    }

    // DFS Iterate?


    // For debugging
    void printDotConstraintGraph(const std::string &graphname,
        const ObjectMap &omap) const;

 private:
    // An individual node within the DUG
    class DUGNode {
      //{{{
     public:
        DUGNode() = default;

        void setValue(const llvm::Value *val) {
          value_ = val;
        }

        const llvm::Value *value() const {
          return value_;
        }

     private:
        // The llvm values that this node represents
        const llvm::Value *value_;

        std::vector<PtsSet> to_;
        std::vector<PtsSet> from_;

        std::vector<DUGNode *> part_succ_;

        ObjID rep_;

        std::list<Constraint> constraints_;
      //}}}
    };

    // Our vector of nodes
    std::vector<DUGNode> nodes_;
    std::vector<Constraint> constraints_;

    std::vector<std::pair<const llvm::Value *, ObjID>> indirectCalls_;
  //}}}
};

#endif  // INCLUDE_DUG_H_

