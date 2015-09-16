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
         ObjectMap::ObjID dest, ObjectMap::ObjID src, int32_t offset) :
      SEGNode<ObjectMap::ObjID>(kind, id, dest),
      dest_(dest), src_(src), offset_(offset) { }
    //}}}

    // For llvm RTTI {{{
    static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
      return node->getKind() >= NodeKind::DUGNode &&
        node->getKind() < NodeKind::DUGNodeEnd;
    }

    virtual void process(DUG &dug, TopLevelPtsto &pts, Worklist &wl) = 0;

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

    int32_t offset() const {
      return offset_;
    }

    void setStrong() {
      strong_ = true;
    }

    bool strong() const {
      return strong_;
    }
    //}}}

 protected:
    // Private variables {{{
    ObjectMap::ObjID dest_;
    ObjectMap::ObjID src_;
    int32_t offset_;
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
      std::map<ObjID, bool> strongCons;

      std::for_each(std::begin(cg), std::end(cg),
          [this, &omap, &strongCons]
          (const ConstraintGraph::iter_type &pcons) {
        // Ignore nullptrs, they've been deleted
        if (pcons == nullptr) {
          return;
        }
        auto &cons = llvm::cast<Constraint>(*pcons);
        // Insert the node into the seg
        auto dest = cons.dest();
        auto src = cons.src();
        auto offs = cons.offs();

        dout << "Adding node to DUG for obj_id: " << dest << ": " <<
            ValPrint(dest) << "\n";

        dout << "  node src_obj_id: " << src << ": " <<
            ValPrint(src) << "\n";

        switch (cons.type()) {
          case ConstraintType::AddressOf:
            {
              dout << "  node is AddressOf\n";
              // Add AllocNode
              bool strong = cons.strong();
              auto ret = DUG_.addNode<AllocNode>(dest, src, offs, strong);
              dout << "  DUGid is " << ret->second << "\n";

              // FIXME: Should store strong information in ptsset for top lvl
              //    variables...
              auto it = strongCons.find(dest);
              if (it == std::end(strongCons)) {
                strongCons.emplace(dest, strong);
              } else {
                it->second &= strong;
              }
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
              dout << "  node is Store\n";
              auto st_id = stcons.nodeId();
              dout << "  adding for store: (" << st_id << ") "
                << ValPrint(st_id) << "\n";
              auto ret =
                DUG_.addNode<StoreNode>(st_id, dest, src, offs);
              dout << "  DUGid is " << ret->second << "\n";
              auto strong_ret = strongCons.emplace(st_id, cons.strong());
              assert(strong_ret.second);
            }
            break;
          case ConstraintType::Load:
            {
              auto &ldcons = llvm::cast<NodeConstraint>(cons);
              dout << "  node is Load\n";
              auto ld_id = ldcons.nodeId();
              dout << "  Actual load_id is: (" << ld_id << ") " <<
                ValPrint(ld_id) << "\n";
              auto ret = DUG_.addNode<LoadNode>(ld_id, dest, src, offs);
              dout << "  Confirming load node!\n";
              auto &nd = DUG_.getNode<LoadNode>(ret->second);
              dout << "    dest is: " << ValPrint(nd.dest())
                  << "\n";
              dout << "    src is: " << ValPrint(nd.src())
                  << "\n";
              dout << "  DUGid is " << ret->second << "\n";
              strongCons.emplace(ld_id, cons.strong());
              // Just trust me on this one...
              // We don't enforce this... assert(strong_ret.second);
            }
            break;
          case ConstraintType::GlobalInit:
            {
              auto &glblcons = llvm::cast<NodeConstraint>(cons);
              dout << "  node is GlobalInit\n";

              auto glbl_id = glblcons.nodeId();
              dout << "  Actual glbl_id is: (" << glbl_id << ")\n";
              auto ret = DUG_.addNode<GlobalInitNode>(glbl_id, dest, src, offs);
              dout << "  Confirming GlobalInit node!\n";
              auto &nd = DUG_.getNode<GlobalInitNode>(ret->second);
              dout << "    dest is: " << ValPrint(nd.dest())
                  << "\n";
              dout << "    src is: " << ValPrint(nd.src())
                  << "\n";
              dout << "  DUGid is " << ret->second << "\n";
              auto strong_ret = strongCons.emplace(glbl_id, cons.strong());
              assert(strong_ret.second);
            }
            break;
          case ConstraintType::Copy:
            {
              if (auto ncons = llvm::dyn_cast<NodeConstraint>(&cons)) {
                dout << "  node is Copy\n";
                auto ret = DUG_.addNode<CopyNode>(ncons->nodeId(), dest, src,
                    offs);
                dout << "  DUGid is " << ret->second << "\n";
                strongCons.emplace(dest, cons.strong());
              } else {
                dout << "  node is Copy\n";
                auto ret = DUG_.addNode<CopyNode>(dest, src, offs);
                dout << "  DUGid is " << ret->second << "\n";
                strongCons.emplace(dest, cons.strong());
              }
            }
            break;
          default:
            llvm_unreachable("Unrecognized constraint type");
        }
      });

      // Update strength for each store node
      std::for_each(std::begin(DUG_), std::end(DUG_),
          [this, &strongCons] (SEG<ObjID>::node_iter_type &upnode) {
        auto pnode = upnode.get();

        if (auto pst = llvm::dyn_cast<DUG::StoreNode>(pnode)) {
          if (strongCons[pst->src()]) {
            pst->setStrong();
          }
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
      // FIXME: Due to phony ids this doesn't work!!!
      // Need to create a list of providers for each id, and go from there...
      // First, map all ids to sources
      std::multimap<ObjID, DUGid> dest_to_node;
      std::for_each(std::begin(DUG_), std::end(DUG_),
          [this, &dest_to_node] (SEG<ObjID>::node_iter_type &upnode) {
        auto &node = llvm::cast<DUGNode>(*upnode);
        dest_to_node.emplace(node.dest(), node.id());
      });

      std::for_each(std::begin(DUG_), std::end(DUG_),
          [this, &dest_to_node] (SEG<ObjID>::node_iter_type &upnode) {
        auto pnode = upnode.get();

        auto &node = llvm::cast<DUGNode>(*pnode);

        // Add an incoming edge from src
        auto src_node_set = dest_to_node.equal_range(node.src());
        std::for_each(src_node_set.first, src_node_set.second,
            [this, &node] (std::pair<const ObjID, SEG<ObjID>::NodeID> &pr) {
          auto &pr_node = DUG_.getNode<DUGNode>(pr.second);
          auto dest_id = pr_node.id();
          // Don't add an edge to yourself!
          if (dest_id != node.id()) {
            /*
            dout << "Adding edge: " << pr.second << " -> " <<
                node.id() << "\n";
            */
            DUG_.addEdge<DUGEdge>(dest_id, node.id());
          }
        });

        // StoreNode's also need an incoming edge from dest, because dest is the
        //   store address, not an actual top level variable, and therefore the
        //   store must be recomputed on dest changes
        if (llvm::isa<StoreNode>(pnode) || llvm::isa<GlobalInitNode>(pnode)) {
          auto dest_id = node.dest();
          auto dest_nodes = dest_to_node.equal_range(dest_id);

          std::for_each(dest_nodes.first, dest_nodes.second,
              [this, &node] (std::pair<const ObjID, SEG<ObjID>::NodeID> &pr) {
            // Don't add an edge to yourself!
            if (pr.second != node.id()) {
              /*
              dout << "Adding glbl/store edge: " << pr.second << " -> "
                  << node.id() << "\n";
              */
              DUG_.addEdge<DUGEdge>(pr.second, node.id());
            }
          });
        }
      });
    }
    //}}}

    // DUG Construction Methods {{{
    DUGid addPhi() {
      return DUG_.addNode<PhiNode>(ObjectMap::UniversalValue, 0)->second;
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
        pn.addPartitionSuccessor(part, dest);
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
        std::map<PartID, std::vector<ObjectMap::ObjID>> mapping) {
      partitionMap_ = std::move(mapping);
    }

    void setRelevantNodes(std::map<ObjID, Bitmap> mapping) {
      relevantNodes_ = std::move(mapping);
    }

    void setPartNodes(std::map<ObjID, std::vector<DUGid>> mapping) {
      partNodes_ = std::move(mapping);
    }

    void setNodeToPartition(std::map<ObjID, PartID> mapping) {
      revPartitionMap_ = std::move(mapping);
    }

    std::vector<DUGid> &getPartNodes(ObjID obj_id) {
      return partNodes_.at(obj_id);
    }

    std::map<ObjID, Bitmap> &getRelevantNodes() {
      return relevantNodes_;
    }

    std::map<ObjID, PartID> &objToPartMap() {
      return revPartitionMap_;
    }

    PartID getPart(ObjID obj_id) {
      return revPartitionMap_.at(obj_id);
    }

    std::vector<ObjectMap::ObjID> &getObjs(PartID part_id) {
      return partitionMap_.at(part_id);
    }
    //}}}

    // Iterators {{{
    // Partition map iterators {{{
    typedef std::map<PartID, std::vector<ObjectMap::ObjID>>::iterator
      part_iterator;
    typedef std::map<PartID, std::vector<ObjectMap::ObjID>>::const_iterator
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
              ObjectMap::ObjID src, int32_t offset, bool strong) :
            DUGNode(NodeKind::AllocNode, node_id, dest, src, offset) {
          // FIXME: Hacky
          strong_ = strong;
        }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, TopLevelPtsto &pts, Worklist &wl) override;

        static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
          return node->getKind() == NodeKind::AllocNode;
        }
      //}}}
    };

    class CopyNode : public DUGNode {
      //{{{
     public:
        CopyNode(SEG<ObjID>::NodeID node_id, ObjectMap::ObjID dest,
            ObjectMap::ObjID src, int32_t offset)
          : DUGNode(NodeKind::CopyNode, node_id, dest, src, offset),
            realDest_(dest) { }

        CopyNode(SEG<ObjID>::NodeID node_id, ObjectMap::ObjID node,
            ObjectMap::ObjID dest, ObjectMap::ObjID src, int32_t offset)
          : DUGNode(NodeKind::CopyNode, node_id, node, src, offset),
          realDest_(dest) { }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, TopLevelPtsto &pts, Worklist &wl) override;

        static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
          return node->getKind() == NodeKind::CopyNode;
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

    class PartNode : public DUGNode {
      //{{{
     public:
      PartNode(NodeKind kind, SEG<ObjID>::NodeID node_id, ObjectMap::ObjID dest,
            ObjectMap::ObjID src, int32_t offset) :
          DUGNode(kind, node_id, dest, src, offset) {
        assert(kind > NodeKind::PartNode && kind < NodeKind::PartNodeEnd);
      }

      PtstoGraph &in() override {
        return in_;
      }

      void addPartitionSuccessor(PartID part_id, DUGid dest_id) {
        part_succs_.emplace_back(part_id, dest_id);
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
        std::vector<std::pair<DUG::PartID, DUG::DUGid>> part_succs_;

        PtstoGraph in_;
      //}}}
    };

    class LoadNode : public PartNode {
      //{{{
     public:
        LoadNode(SEG<ObjID>::NodeID node_id, ObjectMap::ObjID rep,
            ObjectMap::ObjID dest, ObjectMap::ObjID src, int32_t offset)
          : PartNode(NodeKind::LoadNode, node_id, rep, src, offset),
            realDest_(dest) { }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, TopLevelPtsto &pts, Worklist &wl) override;

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
            ObjectMap::ObjID dest, ObjectMap::ObjID src, int32_t offset)
          : PartNode(NodeKind::StoreNode, node_id, rep, src, offset),
          realDest_(dest) { }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, TopLevelPtsto &pts, Worklist &wl) override;

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
            ObjectMap::ObjID dest, ObjectMap::ObjID src, int32_t offset)
          : PartNode(NodeKind::GlobalInitNode, node_id, rep, src, offset),
          realDest_(dest) { }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, TopLevelPtsto &pts, Worklist &wl) override;

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
        bool first_ = true;
      //}}}
    };

    class PhiNode : public PartNode {
      //{{{
     public:
        PhiNode(SEG<ObjID>::NodeID node_id, ObjectMap::ObjID id, int32_t offset)
          : PartNode(NodeKind::PhiNode, node_id, id, id, offset) { }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, TopLevelPtsto &pts, Worklist &wl) override;

        static bool classof(const SEGNode<ObjectMap::ObjID> *node) {
          return node->getKind() == NodeKind::PhiNode;
        }
      //}}}
    };
    //}}}

 private:
    // Private variables {{{
    // The Partition equivalence for each object in the graph
    std::map<PartID, std::vector<ObjID>> partitionMap_;
    std::map<ObjID, Bitmap> relevantNodes_;
    std::map<ObjID, PartID> revPartitionMap_;
    std::map<ObjID, std::vector<DUGid>> partNodes_;

    SEG<ObjID> DUG_;
    //}}}
  //}}}
};

#endif  // INCLUDE_DUG_H_

