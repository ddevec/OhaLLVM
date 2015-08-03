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


// Each entry in the DUG has its own DUGid
// Each entry represents an operation (store/load/etc)
//    This may map to several instructions
// Each entry operates on a set of "top level" variables and "address taken"
//       variables
//    I need to work this out?
// ?All operations inherited from the "top-level" are of the form "Copy" or
//    "AddressOf"?
//
// How do I handle copies?
//    Each node will be identified by its dest?
//
//
// So, when I fill in top level constraints
//    I know all "nodes" except phi nodes, I just don't know edges
//    I can create a node for each non-phi node
//    I can add all top-level edges
// Later when I add partition edges
//    I will create phi nodes for some nodes
//    I can create edges between address-taken variables
//
// Each node has a src and dest -- these are where the info is propigated from
// Each Load/PHI has an IN set that holds ptsto data for address-taken variables
//     accessed by that node
// Each Store node has a IN and OUT set for pointer information
class DUG {
  //{{{
 public:
    // Id Types {{{
    struct part_id { };
    typedef ID<part_id, int32_t> PartID;

    /*
    struct dug_id { };
    typedef ID<dug_id, int32_t> DUGid;
    */

    typedef ObjectMap::ObjID ObjID;
    typedef ObjID DUGid;
    //}}}

    // Internal Classes {{{
    class DUGEdge : public SEGEdge<ObjID> {
     public:
        DUGEdge(ObjID s, ObjID d) : SEGEdge<ObjID>(EdgeKind::DUG, s, d) { }

        // For LLVM RTTI {{{
        static bool classof(const SEGEdge<ObjID> *id) {
          return id->getKind() == EdgeKind::DUG;
        }
        //}}}
    };
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
    void fillTopLevel(const ConstraintGraph &cg) {
      // We iterate each constraint, and add a node for that constraint
      // The node has:  src, dest, type
      // Then, depending on type:
      //   IN, OUT, part_succ, phi_succ, succ
      auto &seg = cg.getSEG();
      std::for_each(seg.edges_begin(), seg.edges_end(),
          [this](const SEG<ObjID>::edge_iter_type &pr) {
        auto &edge = llvm::cast<Constraint<ObjID>>(*pr.second);
        // Insert the node into the seg
        ObjectMap::ObjID dest = edge.dest();
        ObjectMap::ObjID src = edge.src();
        switch (edge.type()) {
          case ConstraintType::AddressOf:
            // Add AllocNode
            DUG_.addNode<AllocNode>(dest, src);
            break;
          case ConstraintType::Store:
            DUG_.addNode<StoreNode>(dest, src);
            break;
          case ConstraintType::Load:
            DUG_.addNode<LoadNode>(dest, src);
            break;
          case ConstraintType::Copy:
            DUG_.addNode<CopyNode>(dest, src);
            break;
          default:
            llvm_unreachable("Unrecognized constraint type");
        }
      });

      // We add unnamed edges for top-level transitions
      std::for_each(seg.edges_begin(), seg.edges_end(),
          [this](const SEG<ObjID>::edge_iter_type &pr) {
        auto &edge = llvm::cast<Constraint<ObjID>>(*pr.second);
        ObjectMap::ObjID dest = edge.dest();
        ObjectMap::ObjID src = edge.src();
        DUG_.addEdge<DUGEdge>(dest, src);
      });
    }
    //}}}

    // DUG Construction Methods {{{
    DUGid addPhi();

    void addEdge(DUGid src, DUGid dest) {
      addEdge(src, dest, PartID::invalid());
    }

    void addEdge(DUGid src, DUGid dest, PartID part) {
      // Okay, add a named edge from src to dest
      if (part == PartID::invalid()) {
        DUG_.addEdge<DUGEdge>(src, dest);
      } else {
        auto &st = DUG_.getNode<StoreNode>(dest);

        // Okay, we have the node, add a named edge
        st.addSucc(dest, part);
      }
    }
    //}}}

    // Equivalence mappings {{{
    // Parititon stuffs:
    /*
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
    */
    //}}}

    // Iterators {{{
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
        static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
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

        static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
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

        CopyNode(int32_t nodenum, ObjectMap::ObjID dest, ObjectMap::ObjID src)
          : DUGNode(NodeKind::CopyNode, nodenum, dest, src) { }


        void process(PtstoData &pts, Worklist &wl) override;

        static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
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

        LoadNode(int32_t nodenum, ObjectMap::ObjID dest, ObjectMap::ObjID src)
          : DUGNode(NodeKind::LoadNode, nodenum, dest, src) { }

        void process(PtstoData &pts, Worklist &wl) override;

        static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
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

        StoreNode(int32_t nodenum, ObjectMap::ObjID dest, ObjectMap::ObjID src)
          : DUGNode(NodeKind::StoreNode, nodenum, dest, src) { }

        void addSucc(ObjectMap::ObjID dest, PartID) {
          part_succ_.insert(dest);
        }

        void process(PtstoData &pts, Worklist &wl) override;

        static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
          return node->getKind() == NodeKind::StoreNode;
        }

     private:
        PtstoSet in_;
        PtstoSet out_;

        bool strong_ = false;

        // Successor partitons -- Used to update worklist on process
        std::set<ObjectMap::ObjID> part_succ_;
      //}}}
    };

    class PhiNode : public DUGNode {
      //{{{
     public:
        PhiNode(int32_t nodenum, ObjectMap::ObjID dest, ObjectMap::ObjID src)
          : DUGNode(NodeKind::PhiNode, nodenum, dest, src) { }

        PhiNode(int32_t nodenum, ObjectMap::ObjID dest, ObjectMap::ObjID src,
            PtstoSet in) :
          DUGNode(NodeKind::PhiNode, nodenum, dest, src),
          in_(std::move(in)) { }

        void process(PtstoData &pts, Worklist &wl) override;

        static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
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

    SEG<DUGid> DUG_;
    //}}}
  //}}}
};

#endif  // INCLUDE_DUG_H_

