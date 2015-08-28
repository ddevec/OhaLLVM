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

class DUG;
// An individual node within the DUG
class DUGNode : public SEGNode<ObjectMap::ObjID> {
  //{{{
 public:
    // Constructors {{{
     DUGNode(NodeKind kind, SEG<ObjectMap::ObjID>::NodeID id,
         ObjectMap::ObjID dest, ObjectMap::ObjID src) :
      SEGNode<ObjectMap::ObjID>(kind, id, dest),
      dest_(dest), src_(src) { }
    //}}}

    // For llvm RTTI {{{
    static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
      return node->getKind() >= NodeKind::DUGNode &&
        node->getKind() < NodeKind::DUGNodeEnd;
    }

    virtual void process(DUG &dug, PtstoGraph &pts, Worklist &wl) = 0;

    virtual PtstoGraph &in() {
      static PtstoGraph bad;
      llvm_unreachable("Shouldn't get here...");
      return bad;
    }

    // For most nodes, rep and dest_ are the same thing
    virtual ObjectMap::ObjID dest() const {
      return dest_;
    }

    virtual ObjectMap::ObjID rep() const {
      return dest_;
    }

    ObjectMap::ObjID src() const {
      return src_;
    }

    bool strong() const {
      return strong_;
    }
    //}}}

 protected:
    // Private variables {{{
    ObjectMap::ObjID dest_;
    ObjectMap::ObjID src_;
    bool strong_ = false;
    //}}}
  //}}}
};

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
    typedef __PartID PartID;

    /*
    struct dug_id { };
    typedef ID<dug_id, int32_t> DUGid;
    */

    typedef ObjectMap::ObjID ObjID;
    typedef SEG<ObjID>::NodeID DUGid;
    typedef SEG<ObjID>::EdgeID EdgeID;
    //}}}

    // Internal Classes {{{
    class DUGEdge : public SEGEdge<ObjID> {
     public:
        DUGEdge(SEG<ObjID>::NodeID s, SEG<ObjID>::NodeID d) :
          SEGEdge<ObjID>(EdgeKind::DUG, s, d) { }

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
    // NOTE: omap needed to make phony objects for store nodes... this is kind
    //     of clunky... but I don't see a way around it
    void fillTopLevel(const ConstraintGraph &cg, ObjectMap &omap) {
      // We iterate each constraint, and add a node for that constraint
      // The node has:  src, dest, type
      // Here we will also have to keep track of which cg::NodeID maps to which
      //   DUG::NodeID so we can transfer the ObjectMap mappings afterwards
      std::for_each(std::begin(cg), std::end(cg),
          [this, &omap]
          (const ConstraintGraph::iter_type &pcons) {
        // Ignore nullptrs, they've been deleted
        if (pcons == nullptr) {
          return;
        }
        auto &cons = llvm::cast<Constraint>(*pcons);
        // Insert the node into the seg
        auto dest = cons.dest();
        auto src = cons.src();

        llvm::dbgs() << "Adding node to DUG for obj_id: " << dest << ": " <<
            ValPrint(dest) << "\n";

        llvm::dbgs() << "  node src_obj_id: " << src << ": " <<
            ValPrint(src) << "\n";

        switch (cons.type()) {
          case ConstraintType::AddressOf:
            {
              llvm::dbgs() << "  node is AddressOf\n";
              // Add AllocNode
              bool strong = cons.strong();
              auto ret = DUG_.addNode<AllocNode>(dest, src, strong);
              llvm::dbgs() << "  DUGid is " << ret->second << "\n";
            }
            break;
          case ConstraintType::Store:
            // NOTE: we don't actually have a dest for stores, so we don't add
            //   any mappings associated with them
            // WRONG: We want the stores to be associated with the node that the
            //   CFG would have given them (typically shared with an addressof
            //     operator)
            // Make a phony dest for this store:
            {
              auto &stcons = llvm::cast<NodeConstraint>(cons);
              llvm::dbgs() << "  node is Store\n";
              auto st_id = stcons.nodeId();
              llvm::dbgs() << "  adding for store: (" << st_id << ") "
                << ValPrint(st_id) << "\n";
              auto ret =
                DUG_.addNode<StoreNode>(st_id, dest, src);
              llvm::dbgs() << "  DUGid is " << ret->second << "\n";
            }
            break;
          case ConstraintType::Load:
            {
              auto &ldcons = llvm::cast<NodeConstraint>(cons);
              llvm::dbgs() << "  node is Load\n";
              auto ld_id = ldcons.nodeId();
              llvm::dbgs() << "  Actual load_id is: (" << ld_id << ") " <<
                ValPrint(ld_id) << "\n";
              auto ret = DUG_.addNode<LoadNode>(ld_id, dest, src);
              llvm::dbgs() << "  Confirming load node!\n";
              auto &nd = DUG_.getNode<LoadNode>(ret->second);
              llvm::dbgs() << "    dest is: " << ValPrint(nd.dest())
                  << "\n";
              llvm::dbgs() << "    src is: " << ValPrint(nd.src())
                  << "\n";
              llvm::dbgs() << "  DUGid is " << ret->second << "\n";
            }
            break;
          case ConstraintType::GlobalInit:
            {
              auto &glblcons = llvm::cast<NodeConstraint>(cons);
              llvm::dbgs() << "  node is GlobalInit\n";

              auto glbl_id = glblcons.nodeId();
              llvm::dbgs() << "  Actual glbl_id is: (" << glbl_id << ")\n";
              auto ret = DUG_.addNode<GlobalInitNode>(glbl_id, dest, src);
              llvm::dbgs() << "  Confirming GlobalInit node!\n";
              auto &nd = DUG_.getNode<GlobalInitNode>(ret->second);
              llvm::dbgs() << "    dest is: " << ValPrint(nd.dest())
                  << "\n";
              llvm::dbgs() << "    src is: " << ValPrint(nd.src())
                  << "\n";
              llvm::dbgs() << "  DUGid is " << ret->second << "\n";
            }
            break;
          case ConstraintType::Copy:
            {
              llvm::dbgs() << "  node is Copy\n";
              auto ret = DUG_.addNode<CopyNode>(dest, src);
              llvm::dbgs() << "  DUGid is " << ret->second << "\n";
            }
            break;
          default:
            llvm_unreachable("Unrecognized constraint type");
        }
      });

      // What I really want:
      //   for each node in DUG:
      //     Create an edge from my dest to all src's matching it
      //     (except for stores, all edges go into those)
      //     Uhh, I think I only have to do first step, 2nd will be done
      //        automatically
      //     create an edge from my src to all dests matching it

      // Also, add all CG node equivalencies to my DUG

      // Solve AE problem by:
      //   Don't give store nodes NodeID's or extId value mappings

      // We add unnamed edges for top-level transitions
      // For each node, add an edge from its src() (if it exists) to it
      std::for_each(std::begin(DUG_), std::end(DUG_),
          [this] (SEG<ObjID>::node_iter_type &upnode) {
        auto pnode = upnode.get();

        auto &node = llvm::cast<DUGNode>(*pnode);

        // Add an incoming edge from src
        auto src_node_set = DUG_.getNodesOrNull(node.src());
        std::for_each(src_node_set.first, src_node_set.second,
            [this, &node] (std::pair<const ObjID, SEG<ObjID>::NodeID> &pr) {
          DUG_.addEdge<DUGEdge>(pr.second, node.id());
        });

        // StoreNode's also need an incoming edge from dest, because dest is the
        //   store address, not an actual top level variable, and therefore the
        //   store must be recomputed on dest changes
        if (auto pst_node = llvm::dyn_cast<StoreNode>(pnode)) {
          auto dest_id = pst_node->dest();
          auto dest_nodes = DUG_.getNodesOrNull(dest_id);

          std::for_each(dest_nodes.first, dest_nodes.second,
              [this, &node] (std::pair<const ObjID, SEG<ObjID>::NodeID> &pr) {
            DUG_.addEdge<DUGEdge>(pr.second, node.id());
          });
        }
      });

      // Now fixup the object mapping, using cg_to_dug and
      //     seg node_map iteration
      /*
      std::for_each(seg.node_map_begin(), seg.node_map_end(),
          [this, &cg_to_dug]
          (const std::pair<const ObjID, SEG<ObjID>::NodeID> &pr) {
        // Now, do the mapping for DUG's node_map
        llvm::dbgs() << "adding mapping to DUG: (" << pr.first << ", " <<
            cg_to_dug[pr.second] << ")\n";
        DUG_.addMapping(pr.first, cg_to_dug[pr.second]);
      });
      */
    }
    //}}}

    // DUG Construction Methods {{{
    DUGid addPhi() {
      return DUG_.addNode<PhiNode>(ObjectMap::UniversalValue)->second;
    }

    void addEdge(DUGid src, DUGid dest) {
      addEdge(src, dest, PartID::invalid());
    }

    void addEdge(DUGid src, DUGid dest, PartID part) {
      // Okay, add a named edge from src to dest
      if (part == PartID::invalid()) {
        DUG_.addEdge<DUGEdge>(src, dest);
      } else {
        auto &pn = DUG_.getNode<PartNode>(src);

        // Okay, we have the node, add a named edge
        pn.addPartitionSuccessor(part);
      }
    }
    //}}}

    // Accessors {{{
    DUGEdge &getEdge(EdgeID id) {
      return DUG_.getEdge<DUGEdge>(id);
    }

    DUGNode &getNode(DUGid id) {
      return DUG_.getNode<DUGNode>(id);
    }

    const DUGNode &getNode(DUGid id) const {
      return DUG_.getNode<DUGNode>(id);
    }

    /*
    std::pair<SEG<ObjID>::NodeMap::iterator, SEG<ObjID>::NodeMap::iterator>
    getNodes(ObjectMap::ObjID id) {
      return DUG_.getNodes(id);
    }
    */

    DUGNode &getNode(ObjectMap::ObjID id) {
      auto ret_pr = DUG_.getNodes(id);
      assert(std::distance(ret_pr.first, ret_pr.second) == 1);
      return getNode(ret_pr.first->second);
    }

    const DUGNode &getNode(ObjectMap::ObjID id) const {
      auto ret_pr = DUG_.getNodes(id);
      assert(std::distance(ret_pr.first, ret_pr.second) == 1);
      return getNode(ret_pr.first->second);
    }

    /*
    std::pair<SEG<ObjID>::node_map_iterator, SEG<ObjID>::node_map_iterator>
    getNode(ObjectMap::ObjID id) {
      return DUG_.getNodes(id);
    }
    */
    //}}}

    // Equivalence mappings {{{
    // Parititon stuffs:
    void setPartitionToNodes(
        std::map<PartID, std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>>> mapping) {  // NOLINT
      partitionMap_ = std::move(mapping);
    }

    void setRelevantNodes(
        std::map<PartID, std::vector<std::pair<DUGid, ObjID>>>
        mapping) {
      relevantNodes_ = std::move(mapping);
    }

    void setNodeToPartition(
        std::map<ObjID, PartID> mapping) {
      revPartitionMap_ = std::move(mapping);
    }

    std::map<PartID, std::vector<std::pair<DUGid, ObjID>>>
    &getRelevantNodes() {
      return relevantNodes_;
    }

    std::map<ObjID, PartID> &objToPartMap() {
      return revPartitionMap_;
    }

    PartID getPart(ObjID obj_id) {
      return revPartitionMap_.at(obj_id);
    }

    std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>> &getObjs(PartID part_id) {  // NOLINT
      return partitionMap_.at(part_id);
    }
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
    typedef std::map<PartID, std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>>>::iterator // NOLINT
      part_iterator;
    typedef std::map<PartID, std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>>>::const_iterator // NOLINT
      const_part_iterator;

    part_iterator part_begin() {
      return std::begin(partitionMap_);
    }

    part_iterator part_end() {
      return std::end(partitionMap_);
    }

    const_part_iterator part_cbegin() const {
      return std::begin(partitionMap_);
    }

    const_part_iterator part_cend() const {
      return std::end(partitionMap_);
    }

    const_part_iterator part_begin() const {
      return std::begin(partitionMap_);
    }

    const_part_iterator part_end() const {
      return std::end(partitionMap_);
    }

    //}}}

    // Node iteration {{{
    typedef SEG<ObjID>::node_iterator node_iterator;
    typedef SEG<ObjID>::const_node_iterator const_node_iterator;
    typedef SEG<ObjID>::node_iter_type node_iter_type;

    node_iterator nodes_begin() {
      return std::begin(DUG_);
    }

    node_iterator nodes_end() {
      return std::end(DUG_);
    }

    const_node_iterator nodes_begin() const {
      return std::begin(DUG_);
    }

    const_node_iterator nodes_end() const {
      return std::end(DUG_);
    }

    const_node_iterator nodes_cbegin() const {
      return std::begin(DUG_);
    }

    const_node_iterator nodes_cend() const {
      return std::end(DUG_);
    }
    //}}}

    // Node Map iteration {{{
    typedef SEG<ObjID>::const_node_map_iterator const_node_map_iterator;

    const_node_map_iterator node_map_cbegin() const {
      return DUG_.node_map_begin();
    }

    const_node_map_iterator node_map_cend() const {
      return DUG_.node_map_end();
    }
    //}}}
    //}}}

    // For debugging {{{
    //}}}

    // Different DUG node types {{{
    class AllocNode : public DUGNode {
      //{{{
     public:
        AllocNode(SEG<ObjID>::NodeID node_id, ObjectMap::ObjID dest,
              ObjectMap::ObjID src, bool strong) :
            DUGNode(NodeKind::AllocNode, node_id, dest, src) {
          // FIXME: Hacky
          strong_ = strong;
        }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, PtstoGraph &pts, Worklist &wl) override;

        static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
          return node->getKind() == NodeKind::AllocNode;
        }
      //}}}
    };

    class CopyNode : public DUGNode {
      //{{{
     public:
        CopyNode(SEG<ObjID>::NodeID node_id, ObjectMap::ObjID dest,
            ObjectMap::ObjID src)
          : DUGNode(NodeKind::CopyNode, node_id, dest, src) { }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, PtstoGraph &pts, Worklist &wl) override;

        static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
          return node->getKind() == NodeKind::CopyNode;
        }
      //}}}
    };

    class PartNode : public DUGNode {
      //{{{
     public:
      PartNode(NodeKind kind, SEG<ObjID>::NodeID node_id, ObjectMap::ObjID dest,
          ObjectMap::ObjID src) : DUGNode(kind, node_id, dest, src) {
        assert(kind > NodeKind::PartNode && kind < NodeKind::PartNodeEnd);
      }

      PtstoGraph &in() override {
        return in_;
      }

      void addPartitionSuccessor(PartID id) {
        part_succs_.insert(id);
      }

      bool hasNoPartitionSuccessors() const {
        return part_succs_.size() == 0;
      }

      virtual void setupPartGraph(const std::vector<ObjectMap::ObjID> &vars) {
        in_ = PtstoGraph(vars);
      }

      static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
        return node->getKind() >= NodeKind::PartNode &&
          node->getKind() < NodeKind::PartNodeEnd;
      }

     protected:
        // Successor partitons
        std::set<DUG::PartID> part_succs_;

        PtstoGraph in_;
      //}}}
    };

    class LoadNode : public PartNode {
      //{{{
     public:
        LoadNode(SEG<ObjID>::NodeID node_id, ObjectMap::ObjID rep,
            ObjectMap::ObjID dest, ObjectMap::ObjID src)
          : PartNode(NodeKind::LoadNode, node_id, rep, src),
        realDest_(dest) { }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, PtstoGraph &pts, Worklist &wl) override;

        static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
          return node->getKind() == NodeKind::LoadNode;
        }

        ObjectMap::ObjID rep() const override {
          return dest_;
        }

        ObjectMap::ObjID dest() const override {
          return realDest_;
        }
      //}}}

     private:
        ObjectMap::ObjID realDest_;
    };

    class StoreNode : public PartNode {
      //{{{
     public:
        StoreNode(SEG<ObjID>::NodeID node_id, ObjectMap::ObjID rep,
            ObjectMap::ObjID dest, ObjectMap::ObjID src)
          : PartNode(NodeKind::StoreNode, node_id, rep, src),
          realDest_(dest) { }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, PtstoGraph &pts, Worklist &wl) override;

        static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
          return node->getKind() == NodeKind::StoreNode;
        }

        void setupPartGraph(const std::vector<ObjectMap::ObjID> &vars)
            override {
          PartNode::setupPartGraph(vars);
          out_ = PtstoGraph(vars);
        }

        ObjectMap::ObjID rep() const override {
          return dest_;
        }

        ObjectMap::ObjID dest() const override {
          return realDest_;
        }

     private:
        PtstoGraph out_;

        ObjectMap::ObjID realDest_;

        bool strong_ = false;
      //}}}
    };

    class GlobalInitNode : public PartNode {
      //{{{
     public:
        GlobalInitNode(SEG<ObjID>::NodeID node_id, ObjectMap::ObjID rep,
            ObjectMap::ObjID dest, ObjectMap::ObjID src)
          : PartNode(NodeKind::GlobalInitNode, node_id, rep, src),
          realDest_(dest) { }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, PtstoGraph &pts, Worklist &wl) override;

        static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
          return node->getKind() == NodeKind::GlobalInitNode;
        }

        ObjectMap::ObjID rep() const override {
          return dest_;
        }

        ObjectMap::ObjID dest() const override {
          return realDest_;
        }

     private:
        ObjectMap::ObjID realDest_;
      //}}}
    };

    class PhiNode : public PartNode {
      //{{{
     public:
        PhiNode(SEG<ObjID>::NodeID node_id, ObjectMap::ObjID id)
          : PartNode(NodeKind::PhiNode, node_id, id, id) { }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, PtstoGraph &pts, Worklist &wl) override;

        static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
          return node->getKind() == NodeKind::PhiNode;
        }
      //}}}
    };
    //}}}

 private:
    // Private variables {{{
    // The Partition equivalence for each object in the graph
    // std::map<ObjectMap::ObjID, PartID> partitionMap_;
    std::map<PartID, std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>>>
      partitionMap_;
    std::map<PartID, std::vector<std::pair<DUGid, ObjID>>>
      relevantNodes_;
    std::map<ObjID, PartID> revPartitionMap_;

    SEG<ObjID> DUG_;
    //}}}
  //}}}
};

#endif  // INCLUDE_DUG_H_

