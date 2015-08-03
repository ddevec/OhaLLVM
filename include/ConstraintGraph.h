/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_CONSTRAINTGRAPH_H_
#define INCLUDE_CONSTRAINTGRAPH_H_

#include "include/ObjectMap.h"

#include "include/SEG.h"

#include <utility>


enum class ConstraintType { Copy, Load, Store, AddressOf };
template <typename id_type>
class Constraint : public SEGEdge<id_type> {
  //{{{
 public:
    // Constructors {{{
    Constraint(id_type s, id_type d, ConstraintType t) :
      Constraint(s, d, t, 0) { }
    Constraint(id_type s, id_type d, ConstraintType t, int32_t o) :
      SEGEdge<id_type>(EdgeKind::Constraint, s, d),
      type_(t), offs_(o) { }

    // For conversion from another constraint type
    template <typename old_id_type, typename id_converter>
    Constraint(id_type src, id_type dest, const SEGEdge<old_id_type> &old_con,
            SEG<id_type> &, id_converter) :
        SEGEdge<id_type>(EdgeKind::Constraint, src, dest),
        type_(llvm::cast<Constraint<old_id_type>>(old_con).type()),
        offs_(llvm::cast<Constraint<old_id_type>>(old_con).offs()) { }

    // No copys, yes moves {{{
    Constraint(const Constraint &) = default;
    Constraint &operator=(const Constraint&) = default;

    Constraint(Constraint &&) = default;
    Constraint &operator=(Constraint&&) = default;
    //}}}
    //}}}

    // Accessors {{{
    ConstraintType type() const {
      return type_;
    }

    int32_t offs() const {
      return offs_;
    }

    // For LLVM RTTI {{{
    static bool classof(const SEGEdge<id_type> *id) {
      return id->getKind() == EdgeKind::Constraint;
    }
    //}}}
    //}}}

    // Target helpers {{{
    bool targetIsDest() const {
      // Okay, which target is the target of node?
      switch (type_) {
        case ConstraintType::AddressOf:
          return true;
        case ConstraintType::Load:
          return false;
        case ConstraintType::Store:
          return true;
        case ConstraintType::Copy:
          return false;
        /*
        case Type::Noop:
          return false;
          */
        default:
          llvm_unreachable("Unrecognized constraint type");
      }
    }

    id_type getTarget() const {
      if (targetIsDest()) {
        return SEGEdge<id_type>::dest();
      } else {
        return SEGEdge<id_type>::src();
      }
    }
    //}}}

    // Print helper {{{
    void print_label(llvm::raw_ostream &ofil, const ObjectMap &) const {
      switch (type()) {
        case ConstraintType::Copy:
          ofil << "copy";
          break;
        case ConstraintType::AddressOf:
          ofil << "addr_of";
          break;
        case ConstraintType::Load:
          ofil << "load";
          break;
        case ConstraintType::Store:
          ofil << "store";
          break;
        default:
          llvm_unreachable("Constraint with unexpected type!");
          ofil << "BLEH";
      }
    }
    //}}}

 private:
    // Private Data {{{
    ConstraintType type_;

    int32_t offs_ = 0;
    //}}}
  //}}}
};

class ConstraintGraph {
  //{{{
 public:
    // Typedefs {{{
    // ObjIDs
    typedef ObjectMap::ObjID ObjID;
    typedef std::pair<ObjID, ObjID> ConsID;

    // SEG
    typedef SEG<ObjID> ConstraintSEG;
    //}}}

    // Internal classes {{{
    // ConstraintNode {{{
    struct ConstraintNode : public UnifyNode<ObjID> {
      //{{{
      ConstraintNode(int32_t nodenum, ObjID id) :
        UnifyNode<ObjID>(NodeKind::ConstraintNode, nodenum, id) { }

      /*
      ConstraintNode(int32_t nodenum, ObjID id, const ConstraintNode &con) :
        UnifyNode<ObjID>(NodeKind::ConstraintNode, nodenum, id, con) { }
        */

      void print_label(llvm::raw_ostream &ofil,
          const ObjectMap &omap) const override {
        std::for_each(UnifyNode<ObjID>::rep_begin(),
            UnifyNode<ObjID>::rep_end(),
            [&ofil, &omap](const ObjID &id) {
          auto pr = omap.getValueInfo(id);
          if (pr.first != ObjectMap::Type::Special) {
            const llvm::Value *val = pr.second;
            if (val == nullptr) {
              ofil << "temp node";
            } else if (auto GV = llvm::dyn_cast<const llvm::GlobalValue>(val)) {
              ofil <<  GV->getName();
            } else if (auto F = llvm::dyn_cast<const llvm::Function>(val)) {
              ofil <<  F->getName();
            } else {
              ofil << *val;
            }
          } else {
            if (id == ObjectMap::NullValue) {
              ofil << "NullValue";
            } else if (id == ObjectMap::NullObjectValue) {
              ofil << "NullObjectValue";
            } else if (id == ObjectMap::IntValue) {
              ofil << "IntValue";
            } else if (id == ObjectMap::UniversalValue) {
              ofil << "UniversalValue";
            } else if (id == ObjectMap::UniversalValue) {
              ofil << "PthreadSpecificValue";
            } else {
              llvm_unreachable("Shouldn't have unknown value here!");
            }
          }
          ofil << "\n";
        });
      }
      //}}}
    };
    //}}}
    //}}}

    // Modifiers {{{
    ConsID add(ConstraintType type, ObjID d, ObjID s) {
      return add(type, d, s, 0);
    }

    ConsID add(ConstraintType type, ObjID d, ObjID s, int o) {
      auto s_it = constraintGraph_.findNode(s);
      if (s_it == std::end(constraintGraph_)) {
        constraintGraph_.addNode<ConstraintNode>(s);
      }

      auto d_it = constraintGraph_.findNode(d);
      if (d_it == std::end(constraintGraph_)) {
        constraintGraph_.addNode<ConstraintNode>(d);
      }

      constraintGraph_.addEdge<Constraint<ObjID>>(s, d, type, o);

      return ConsID(s, d);
    }

    ObjID addNode(ObjectMap &omap) {
      auto id = omap.makeTempValue();

      // Put a new node on the back of nodes
      constraintGraph_.addNode<ConstraintNode>(id);

      return id;
    }

    void removeConstraint(ConsID id) {
      constraintGraph_.removeEdge(id);
    }

    void associateNode(ObjID, ObjID) { }

    ConstraintSEG &getSEG() {
      return constraintGraph_;
    }
    //}}}

    // Accessors {{{
    const Constraint<ObjID>  &getConstraint(ConsID id) const {
      return constraintGraph_.getEdge<Constraint<ObjID>>(id);
    }

    ConstraintNode &getNode(ObjID id) {
      return constraintGraph_.getNode<ConstraintNode>(id);
    }
    //}}}

    // Graph print debugging {{{
    void printDotConstraintGraph(const std::string &graphname,
        const ObjectMap &omap) const;
    //}}}

 private:
    // Private data {{{
    ConstraintSEG constraintGraph_;
    //}}}
  //}}}
};

#endif  // INCLUDE_CONSTRAINTGRAPH_H_
