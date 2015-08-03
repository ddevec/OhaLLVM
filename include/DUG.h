/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_DUG_H_
#define INCLUDE_DUG_H_

#include <cstdint>

#include <functional>
#include <list>
#include <map>
#include <queue>
#include <set>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "include/util.h"
#include "include/ConstraintGraph.h"
#include "include/ControlFlowGraph.h"
#include "include/ObjectMap.h"
#include "include/SEG.h"
#include "include/SolveHelpers.h"


class DUG {
  //{{{
 public:
    // Id Types {{{
    /* -- We switched this to pair<ObjID, ObjID>
    struct con_id { };
    typedef ID<con_id, int32_t, -1> ConsID;
    */

    struct part_id { };
    typedef ID<part_id, int32_t> PartID;
    //}}}

    // Internal classes {{{
    /*
    // SEGNodeGroup {{{
    struct SEGNodeGroup : public UnifyNode<ObjID> {
      //{{{
      // Constructors {{{
      SEGNodeGroup(int32_t nodenum, ObjectMap::ObjID id, ObjID base_id) :
          UnifyNode<ObjectMap::ObjID>(NodeKind::SEGNodeGroup, nodenum, id) {
        oids.insert(base_id);
      }

      template <typename id_converter>
      SEGNodeGroup(int32_t nodenum, ObjectMap::ObjID id, const SEGNode<ObjID> &old_node,
            id_converter convert) :
          UnifyNode<ObjectMap::ObjID>(NodeKind::SEGNodeGroup, nodenum, id,
              old_node, convert) {
        oids.insert(old_node.id());

        if (auto pun = llvm::dyn_cast<UnifyNode<ObjID>>(&old_node)) {
          auto &node = *pun;

          std::for_each(node.rep_begin(), node.rep_end(),
              [this](ObjID oid) {
            oids.insert(oid);
          });
        }
      }
      //}}}

      // Printing for DOT debugging {{{
      void print_label(llvm::raw_ostream &ofil,
          const ObjectMap &omap) const override {
        // So I can know when the end is coming, for newline printing
        for (auto it = oids.begin(),
            en = oids.end(); it != en;) {
          auto id = *it;
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

          ++it;
          if (it != en) {
            ofil << "\n";
          }
        }
      }
      //}}}

      // Unite/merge overrides {{{
      void unite(SEG<ObjectMap::ObjID> &graph, SEGNode<ObjectMap::ObjID> &n) override {
        auto &grp = llvm::cast<SEGNodeGroup>(n);

        oids.insert(std::begin(grp.oids), std::end(grp.oids));

        UnifyNode<ObjectMap::ObjID>::unite(graph, n);
      }

      void merge(const SEGNode<ObjectMap::ObjID> &n) override {
        auto &grp = llvm::cast<SEGNodeGroup>(n);

        oids.insert(std::begin(grp.oids), std::end(grp.oids));

        UnifyNode<ObjectMap::ObjID>::merge(n);
      }
      //}}}

      // For llvm RTTI {{{
      static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
        return node->getKind() == NodeKind::SEGNodeGroup;
      }
      //}}}

      std::set<ObjID> oids;
      //}}}
    };
    */
    //}}}

    //}}}


    // Constructors {{{
    // Default constructor
    DUG() = default;

    // No copy/move semantics {{{
    DUG(const DUG &) = delete;
    DUG(DUG &&) = delete;

    DUG &operator=(const DUG &) = delete;
    DUG &operator=(DUG &&) = delete;
    //}}}
    //}}}

    // Top-level Construction Methods {{{

    // Populate the top level DUG information.
    // This means creating a node for each Pointer Equivalent enetity
    //   (ObjectMap::ObjID), and creating edges for each of the
    //   top level variables
    void fillDUGTopLevel();
    //}}}

    // DUG Construction Methods {{{
    ConstraintGraph::ObjID addDUGphi();
    void addDUGEdge(ObjectMap::ObjID src, ObjectMap::ObjID dest, PartID part);
    //}}}


    // Equivalence mappings {{{
    // PE stuffs
    /*
    void setPEs(std::map<ObjectObjID, ObjectMap::ObjID> mapping) {
      objToPE_ = std::move(mapping);
    }

    ObjectMap::ObjID getPE(ObjID id) const {
      ObjectMap::ObjID ret;
      auto it = objToPE_.find(id);
      if (it != std::end(objToPE_)) {
        ret = it->second;
      }

      return ret;
    }
    */


    // Parititon stuffs:
    void setPartitions(std::map<ObjectMap::ObjID, PartID> mapping,
        std::map<PartID, std::vector<ObjectMap::ObjID>> rev_mapping) {
      partitionMap_ = std::move(mapping);
      revPartitionMap_ = std::move(rev_mapping);
    }

    PartID getPartition(ObjectMap::ObjID id) const {
      PartID ret;

      auto it = partitionMap_.find(id);
      if (it != std::end(partitionMap_)) {
        return it->second;
      }

      return ret;
    }
    //}}}

    // Iterators {{{
    // Iterator helper {{{
    // Iterates an iter itype, returning a std::pair<ObjID(id), outp>
    /*
    template<typename itype, typename outp>
    struct pair_iter {
      //{{{
     public:
        typedef std::pair<ObjectMap::ObjID, outp &> value_type;

        explicit pair_iter(itype iter) :
            iter_(iter) { }

        value_type operator*() {
          return std::make_pair(ObjectMap::ObjID(pos_),
              std::ref(*iter_));
        }

        pair_iter &operator++() {
          ++pos_;
          ++iter_;

          return *this;
        }

        pair_iter &operator--() {
          --pos_;
          --iter_;

          return *this;
        }

        bool operator==(const pair_iter &it) const {
          return it.iter_ == iter_;
        }

        bool operator!=(const pair_iter &it) const {
          return it.iter_ != iter_;
        }

        bool operator<(const pair_iter &it) const {
          return it.iter_ < iter_;
        }

     private:
        itype iter_;
        size_t pos_ = 0;
      //}}}
    };
    */
    //}}}

    // Partition map iterators {{{
    typedef std::map<PartID, std::vector<ConstraintGraph::ObjID>>::const_iterator // NOLINT
      const_part_iterator;

    const_part_iterator part_begin() const {
      return std::begin(revPartitionMap_);
    }

    const_part_iterator part_end() const {
      return std::end(revPartitionMap_);
    }

    //}}}
    //}}}

    // For debugging {{{
    //}}}

 private:
    // An individual node within the DUG
    class DUGNode : public SEGNode<ObjectMap::ObjID> {
      //{{{
     public:
       // Constructors {{{
        DUGNode(NodeKind kind, int32_t nodenum, ObjectMap::ObjID dest,
            ObjectMap::ObjID src) :
          SEGNode<ObjectMap::ObjID>(kind, nodenum, dest),
          dest_(dest), src_(src) { }
       //}}}

        // For llvm RTTI {{{
        bool classof(const SEGNode<ObjectMap::ObjID> *node) {
          return node->getKind() >= NodeKind::DUGNode &&
            node->getKind() < NodeKind::DUGNodeEnd;
        }

        virtual void process(PtstoData &pts, Worklist &wl) = 0;
        //}}}
     protected:
        // Private variables {{{
        ObjectMap::ObjID dest_;
        ObjectMap::ObjID src_;
        //}}}
      //}}}
    };

    // Different DUG node types {{{
    class AllocNode : public DUGNode {
      //{{{
     public:
        AllocNode(int32_t nodenum, ObjectMap::ObjID dest,
            ObjectMap::ObjID src) :
          DUGNode(NodeKind::AllocNode, nodenum, dest, src) { }

        void process(PtstoData &pts, Worklist &wl) override;

        bool classof(const SEGNode<ObjectMap::ObjID> *node) {
          return node->getKind() == NodeKind::AllocNode;
        }
      //}}}
    };

    class CopyNode : public DUGNode {
      //{{{
     public:
        CopyNode(int32_t nodenum, ObjectMap::ObjID dest, ObjectMap::ObjID src,
            PtstoSet in) :
          DUGNode(NodeKind::CopyNode, nodenum, dest, src),
          in_(std::move(in)) { }


        void process(PtstoData &pts, Worklist &wl) override;

        bool classof(const SEGNode<ObjectMap::ObjID> *node) {
          return node->getKind() == NodeKind::CopyNode;
        }

     private:
        PtstoSet in_;
      //}}}
    };

    class LoadNode : public DUGNode {
      //{{{
     public:
        LoadNode(int32_t nodenum, ObjectMap::ObjID dest, ObjectMap::ObjID src,
            PtstoSet in) :
          DUGNode(NodeKind::LoadNode, nodenum, dest, src),
          in_(std::move(in)) { }


        void process(PtstoData &pts, Worklist &wl) override;

        bool classof(const SEGNode<ObjectMap::ObjID> *node) {
          return node->getKind() == NodeKind::LoadNode;
        }

     private:
        PtstoSet in_;
      //}}}
    };

    class StoreNode : public DUGNode {
      //{{{
     public:
        StoreNode(int32_t nodenum, ObjectMap::ObjID dest, ObjectMap::ObjID src,
            PtstoSet in, PtstoSet out, std::set<ObjectMap::ObjID> part_succ) :
          DUGNode(NodeKind::StoreNode, nodenum, dest, src),
          in_(std::move(in)), out_(std::move(out)),
          part_succ_(std::move(part_succ)) { }


        void process(PtstoData &pts, Worklist &wl) override;

        bool classof(const SEGNode<ObjectMap::ObjID> *node) {
          return node->getKind() == NodeKind::StoreNode;
        }

     private:
        PtstoSet in_;
        PtstoSet out_;

        // Successor partitons -- Used to update worklist on process
        std::set<ObjectMap::ObjID> part_succ_;
      //}}}
    };

    class PhiNode : public DUGNode {
      //{{{
     public:
        PhiNode(int32_t nodenum, ObjectMap::ObjID dest, ObjectMap::ObjID src,
            PtstoSet in) :
          DUGNode(NodeKind::PhiNode, nodenum, dest, src),
          in_(std::move(in)) { }

        void process(PtstoData &pts, Worklist &wl) override;

        bool classof(const SEGNode<ObjectMap::ObjID> *node) {
          return node->getKind() == NodeKind::PhiNode;
        }
     private:
        PtstoSet in_;
      //}}}
    };
    //}}}

    // Private variables {{{

    // The Partition equivalence for each object in the graph
    std::map<ObjectMap::ObjID, PartID> partitionMap_;
    std::map<PartID, std::vector<ObjectMap::ObjID>> revPartitionMap_;
    //}}}
  //}}}
};

#endif  // INCLUDE_DUG_H_

