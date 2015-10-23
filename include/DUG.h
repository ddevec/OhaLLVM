/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_DUG_H_
#define INCLUDE_DUG_H_

#include <cstdint>

#include <algorithm>
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
class DUGNode : public SEG::Node {
  //{{{
 public:
    // Constructors {{{
     DUGNode(NodeKind kind, SEG::NodeID id,
         ObjectMap::ObjID dest, ObjectMap::ObjID src, int32_t offset) :
      SEG::Node(kind, id),
      dest_(dest), src_(src), offset_(offset) { }
    //}}}

    // For llvm RTTI {{{
    static bool classof(const SEG::Node *node) {
      return node->getKind() >= NodeKind::DUGNode &&
        node->getKind() < NodeKind::DUGNodeEnd;
    }

    virtual void process(DUG &dug, TopLevelPtsto &pts, Worklist &wl,
        const std::vector<uint32_t> &priority) = 0;

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

    void addConstraintsWithAliases(const std::set<ObjectMap::ObjID> &pts_set,
        const ObjectMap &omap) {
      if (dynConstraints_ == nullptr) {
        dynConstraints_ = std::unique_ptr<Bitmap>(new Bitmap());
      }

      for (auto &cons : pts_set) {
        auto pr = omap.findObjAliases(cons);

        if (pr.first) {
          for (auto field : pr.second) {
            dynConstraints_->set(field.val());
          }
        }

        dynConstraints_->set(cons.val());
      }
    }

    //}}}

 protected:
    // Private variables {{{
    ObjectMap::ObjID dest_;
    ObjectMap::ObjID src_;
    int32_t offset_;
    bool strong_ = false;

    // Our output ptsto can only be a subset of this set
    std::unique_ptr<Bitmap> dynConstraints_ = nullptr;
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
    typedef SEG::NodeID DUGid;
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

      // O(n*log(n)) ?
      int32_t consid = 0;
      {
        PerfTimerPrinter fill_timer(dbg, "fill loop");
        std::for_each(std::begin(cg), std::end(cg),
            [this, &consid, &omap, &strongCons]
            (const ConstraintGraph::iter_type &pcons) {
          // Ignore nullptrs, they've been deleted
          if (pcons == nullptr) {
            consid++;
            return;
          }

          // O(1)
          auto &cons = cast<Constraint>(*pcons);
          // Insert the node into the seg
          auto dest = cons.dest();
          auto src = cons.src();
          auto offs = cons.offs();

          SEG::NodeID node_id;

          dout("Adding node to DUG for obj_id: " << dest << ": " <<
              ValPrint(dest) << "\n");

          dout("  node src_obj_id: " << src << ": " <<
              ValPrint(src) << "\n");

          switch (cons.type()) {
            case ConstraintType::AddressOf:
              {
                dout("  node is AddressOf\n");
                // Add AllocNode
                bool strong = cons.strong();
                // O(log(n))
                node_id = DUG_.addNode<AllocNode>(dest, src, offs, strong);
                dout("  DUGid is " << node_id << "\n");

                // FIXME: Should store strong information in ptsset for top lvl
                //    variables...
                // O(log(n))
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
              // WRONG: We want the stores to be associated with the node
              //   that the CFG would have given them (typically shared
              //   with an addressof operator)
              // Make a phony dest for this store:
              {
                dout("  node is Store\n");
                auto st_id = cons.rep();
                dout("  adding for store: (" << st_id << ") "
                  << ValPrint(st_id) << "\n");
                node_id = DUG_.addNode<StoreNode>(st_id, dest, src, offs);
                dout("  DUGid is " << node_id << "\n");
                // logout("n " << ret << "\n");
                assert(strongCons.find(st_id) == std::end(strongCons));
                strongCons.emplace(st_id, cons.strong());
                // logout("t " << 1 << "\n");
              }
              break;
            case ConstraintType::Load:
              {
                dout("  node is Load\n");
                auto ld_id = cons.rep();
                dout("  Actual load_id is: (" << ld_id << ") " <<
                  ValPrint(ld_id) << "\n");
                node_id = DUG_.addNode<LoadNode>(ld_id, dest, src, offs);
                // logout("n " << ret << "\n");
                dout("  DUGid is " << node_id << "\n");
                strongCons.emplace(ld_id, cons.strong());
                // logout("t " << 2 << "\n");
              }
              break;
            case ConstraintType::Copy:
              {
                dout("  node is Copy\n");
                node_id =
                  DUG_.addNode<CopyNode>(cons.rep(), dest, src, offs);
                // logout("n " << ret << "\n");
                dout("  DUGid is " << node_id << "\n");
                strongCons.emplace(dest, cons.strong());
                // logout("t " << 4 << "\n");
              }
              break;
            default:
              llvm_unreachable("Unrecognized constraint type");
          }

          auto &nd = DUG_.getNode<DUGNode>(node_id);
          nodeMap_.emplace(nd.rep(), node_id);

          // logout("s " << src << "\n");
          // logout("d " << dest << "\n");
          consid++;
        });
      }

      // Update strength for each store node
      // O(n*log(n))
      {
        PerfTimerPrinter strong_timer(dbg, "strong loop");
        std::for_each(std::begin(DUG_), std::end(DUG_),
            [this, &strongCons] (SEG::node_iter_type &upnode) {
          auto pnode = upnode.get();

          if (auto pst = dyn_cast<DUG::StoreNode>(pnode)) {
            if (strongCons[pst->src()]) {
              pst->setStrong();
            }
          }
        });
      }

      // for each node in DUG:
      //   Create an edge from my dest to all src's matching it
      //   (except for stores, all edges go into those)

      // Need to create a list of providers for each id, and go from there...
      // First, map all ids to sources
      // O(n*log(n))
      // std::multimap<ObjID, DUGid> dest_to_node;
      int32_t max_dest = 0;
      int64_t edge_count = 0;
      std::for_each(std::begin(DUG_), std::end(DUG_),
          [this, &max_dest] (SEG::node_iter_type &upnode) {
        auto &node = cast<DUGNode>(*upnode);
        if (node.dest().val() > max_dest) {
          max_dest = node.dest().val();
        }
      });

      std::vector<std::vector<DUGid>> dest_to_node(max_dest+1);
      std::for_each(std::begin(DUG_), std::end(DUG_),
          [this, &dest_to_node, &edge_count] (SEG::node_iter_type &upnode) {
        auto &node = cast<DUGNode>(*upnode);
        dest_to_node[node.dest().val()].push_back(node.id());
        edge_count++;
      });
      llvm::dbgs() << "Discovered " << edge_count << " linkages\n";

      // We add unnamed edges for top-level transitions
      // For each node, add an edge from its src() (if it exists) to it
      // O(n*E)
      {
        int64_t num_edges = 0;
        int64_t st_edges = 0;
        int64_t node_count = 0;
        PerfTimerPrinter edge_addition(llvm::dbgs(), "Edge creation");
        std::for_each(std::begin(DUG_), std::end(DUG_),
            [this, &dest_to_node,
              &num_edges, &st_edges, &node_count]
            (SEG::node_iter_type &upnode) {
          node_count++;
          auto pnode = upnode.get();

          auto &node = cast<DUGNode>(*pnode);

          // Add an incoming edge from src
          // O(log(n))
          // auto src_node_set = dest_to_node.equal_range(node.src());
          /*
          assert(node.src().val() <
              static_cast<int32_t>(dest_to_node.size()));
          */
          if (node.src().val() < static_cast<int32_t>(dest_to_node.size())) {
            auto &srcs = dest_to_node[node.src().val()];
            num_edges += srcs.size();
            for (auto src_id : srcs) {
              auto &pr_node = DUG_.getNode<DUGNode>(src_id);
              auto node_id = node.id();
              // Don't add an edge to yourself!
              // assert(pr_node.id() != node_id);
              if (pr_node.id() != node_id) {
              // O(1)
              // edge_count++;
              // DUG_.addSucc(dest_id, node.id());
                pr_node.succs().insert(node_id);
              }
            }
          } else {
            llvm::dbgs() << "WARNING: fillTopLevel sink without source: (" <<
              node.src() << ") " << ValPrint(node.src()) << "\n";
          }

          // StoreNode's also need an incoming edge from dest, because dest
          //   is the store address, not an actual top level variable, and
          //   therefore the store must be recomputed on dest changes
          if (llvm::isa<StoreNode>(pnode)) {
            auto dest_id = node.dest();

            // O(log(n))
            // auto dest_nodes = dest_to_node.equal_range(dest_id);
            assert(dest_id.val() < static_cast<int32_t>(dest_to_node.size()));
            auto &st_srcs = dest_to_node[dest_id.val()];
            st_edges += st_srcs.size();
            // O(E)
            for (auto src_id : st_srcs) {
              // Don't add an edge to yourself!
              if (src_id != node.id()) {
                // O(1)
                DUG_.addSucc(src_id, node.id());
              }
            }
          }
        });

        // Clean up the succs

        llvm::dbgs() << "edge_count; " << num_edges << "\n";
        llvm::dbgs() << "st_edge_count; " << st_edges << "\n";
        llvm::dbgs() << "node_count; " << node_count << "\n";
      }

      /*
      {
        PerfTimerPrinter edge_addition(llvm::dbgs(), "Edge cleanup");
        DUG_.cleanEdges();
      }
      */
    }
    //}}}

    // DUG Construction Methods {{{
    DUGid addPhi() {
      return DUG_.addNode<PhiNode>(ObjectMap::UniversalValue, 0);
    }

    void addEdge(DUGid src, DUGid dest) {
      addEdge(src, dest, PartID::invalid());
    }

    void addEdge(DUGid src, DUGid dest, PartID part) {
      // Okay, add a named edge from src to dest
      if (part == PartID::invalid()) {
        DUG_.addSucc(src, dest);
      } else {
        auto &pn = DUG_.getNode<PartNode>(src);

        // Okay, we have the node, add a named edge
        pn.addPartitionSuccessor(part, dest);
      }
    }

    void setStructInfo(const std::map<ObjID, int32_t> info) {
      structInfo_ = info;
    }
    //}}}

    // Replacing nodes with constant ptsto nodes {{{
    void replaceWithConstantNode(DUGid id, const std::set<ObjID> &ptsto_set) {
      // Replace the node at ID with a constant ptsto node
      auto &node = getNode(id);
      // If its a PartNode, we have to propigate the correct in-set...
      if (llvm::isa<PartNode>(node)) {
        DUG_.replaceNode<ConstPartNode>(id, node.dest(),
            node.src(), std::begin(ptsto_set), std::end(ptsto_set));
      } else {
        // Its a non-part node, we just treat it as an address of node
        DUG_.replaceNode<ConstNode>(id, node.dest(),
            node.src(), std::begin(ptsto_set), std::end(ptsto_set));
      }
    }
    // }}}

    // Accessors {{{
    const std::map<ObjID, int32_t> &getStructInfo() const {
      return structInfo_;
    }

    size_t getNumNodes() const {
      return DUG_.getNumNodes();
    }

    SEG &getSEG() {
      return DUG_;
    }

    const DUGNode &getRep(DUG::DUGid dug_id) {
      auto &node = DUG_.getNode<DUG::PartNode>(dug_id);
      if (node.isDUGRep()) {
        return node;
      } else {
        auto &ret = cast<DUG::PartNode>(getRep(node.getDUGRep()));
        node.setDUGRep(ret.id());

        return ret;
      }
    }

    const DUGNode &getNode(ObjectMap::ObjID oid) const {
      return DUG_.getNode<DUGNode>(nodeMap_.at(oid));
    }

    DUGNode *tryGetNode(ObjectMap::ObjID oid) {
      auto it = nodeMap_.find(oid);
      if (it != std::end(nodeMap_)) {
        return &DUG_.getNode<DUGNode>(it->second);
      } else {
        return nullptr;
      }
    }

    DUGNode &getNode(ObjectMap::ObjID oid) {
      return DUG_.getNode<DUGNode>(nodeMap_.at(oid));
    }

    DUGNode &getNode(DUGid id) {
      return DUG_.getNode<DUGNode>(id);
    }

    const DUGNode &getNode(DUGid id) const {
      return DUG_.getNode<DUGNode>(id);
    }
    //}}}

    // Equivalence mappings {{{
    // Parititon stuffs:
    void setPartitionToNodes(
        std::map<PartID, std::vector<ObjectMap::ObjID>> mapping) {
      partitionMap_ = std::move(mapping);
    }

    void setRelevantNodes(std::vector<Bitmap> mapping) {
      relevantNodes_ = std::move(mapping);
    }

    /*
    void setPartNodes(std::map<ObjID, std::vector<DUGid>> mapping) {
      partNodes_ = std::move(mapping);
    }
    */
    void setPartNodes(std::vector<std::vector<DUGid>> mapping) {
      partNodes_ = std::move(mapping);
    }

    void setNodeToPartition(std::map<ObjID, PartID> mapping) {
      revPartitionMap_ = std::move(mapping);
    }

    /*
    std::vector<DUGid> &getPartNodes(ObjID obj_id) {
      return partNodes_.at(obj_id);
    }
    */
    std::vector<DUGid> &getPartNodes(ObjID obj_id) {
      return partNodes_[obj_id.val()];
    }

    std::vector<Bitmap> &getRelevantNodes() {
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
    typedef SEG::node_iterator node_iterator;
    typedef SEG::const_node_iterator const_node_iterator;
    typedef SEG::node_iter_type node_iter_type;

    node_iterator begin() {
      return std::begin(DUG_);
    }

    node_iterator end() {
      return std::end(DUG_);
    }

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

    //}}}

    // For debugging {{{
    //}}}

    // Different DUG node types {{{
    class AllocNode : public DUGNode {
      //{{{
     public:
        AllocNode(SEG::NodeID node_id, ObjectMap::ObjID dest,
              ObjectMap::ObjID src, int32_t offset, bool strong) :
            DUGNode(NodeKind::AllocNode, node_id, dest, src, offset) {
          // FIXME: Hacky
          strong_ = strong;
        }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, TopLevelPtsto &pts, Worklist &wl,
            const std::vector<uint32_t> &priority) override;

        static bool classof(const SEG::Node *node) {
          return node->getKind() == NodeKind::AllocNode;
        }
      //}}}
    };

    class ConstNode : public DUGNode {
      //{{{
     public:
        ConstNode(SEG::NodeID node_id, ObjectMap::ObjID dest,
              ObjectMap::ObjID src, std::set<ObjID>::iterator st,
              std::set<ObjID>::iterator en) :
            DUGNode(NodeKind::ConstNode, node_id, dest, src, 0) {
          // Fill the object set
          // constObjSet_.reserve(std::distance(st, en));
          constObjSet_.insert(std::end(constObjSet_), st, en);
        }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, TopLevelPtsto &pts, Worklist &wl,
            const std::vector<uint32_t> &priority) override;

        static bool classof(const SEG::Node *node) {
          return node->getKind() == NodeKind::PartNode;
        }

     private:
        bool run_ = false;
        std::vector<ObjID> constObjSet_;
      //}}}
    };

    class CopyNode : public DUGNode {
      //{{{
     public:
        CopyNode(SEG::NodeID node_id, ObjectMap::ObjID dest,
            ObjectMap::ObjID src, int32_t offset)
          : DUGNode(NodeKind::CopyNode, node_id, dest, src, offset),
            realDest_(dest) { }

        CopyNode(SEG::NodeID node_id, ObjectMap::ObjID node,
            ObjectMap::ObjID dest, ObjectMap::ObjID src, int32_t offset)
          : DUGNode(NodeKind::CopyNode, node_id, node, src, offset),
          realDest_(dest) { }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, TopLevelPtsto &pts, Worklist &wl,
            const std::vector<uint32_t> &priority) override;

        static bool classof(const SEG::Node *node) {
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
      PartNode(NodeKind kind, SEG::NodeID node_id, ObjectMap::ObjID dest,
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
        assert(isDUGRep());
        in_ = PtstoGraph(vars);
      }

      void erasePartSucc(DUG::DUGid id) {
        // Swap out elm w/ end, then pop end
        for (size_t i = 0; i < part_succs_.size(); i++) {
          while (part_succs_[i].second == id) {
            part_succs_[i] = part_succs_.back();
            part_succs_.pop_back();
          }
        }
      }

      void erasePartSucc(const std::vector<DUG::DUGid> &srcs) {
        auto succ_sorter_erase = [] (
            const std::pair<DUG::PartID, DUG::DUGid> &p1,
            const std::pair<DUG::PartID, DUG::DUGid> &p2) -> bool {
          bool ret = p1.second < p2.second;
          return ret;
        };

        auto succ_sorter_unique = [] (
            const std::pair<DUG::PartID, DUG::DUGid> &p1,
            const std::pair<DUG::PartID, DUG::DUGid> &p2) -> bool {
          bool ret = p1.second == p2.second;
          return ret;
        };

        // Create a vector of pairs
        std::vector<std::pair<DUG::PartID, DUG::DUGid>> elms;
        for (auto elm : srcs) {
          elms.push_back(std::make_pair(DUG::PartID::invalid(), elm));
        }

        std::sort(std::begin(elms), std::end(elms), succ_sorter_erase);
        auto it = std::unique(std::begin(elms), std::end(elms),
            succ_sorter_unique);
        elms.erase(it, std::end(elms));

        uniqSuccs();


        /* Can't use this, b/c it only removes 1 elm per elm in elms
        std::set_difference(std::begin(part_succs_), std::end(part_succs_),
            std::begin(elms), std::end(elms),
            std::back_inserter(tmp_succs), succ_sorter_erase);
        */
        std::vector<std::pair<DUG::PartID, DUG::DUGid>> new_part_succs;
        size_t elm_pos = 0;
        for (size_t i = 0; i < part_succs_.size(); i++) {
          // If we need to advance elm, b/c part_succ is larger
          while (elm_pos < elms.size() &&
              elms[elm_pos].second < part_succs_[i].second) {
            elm_pos++;
          }
          if (elm_pos >= elms.size() ||
              elms[elm_pos].second != part_succs_[i].second) {
            new_part_succs.push_back(part_succs_[i]);
          }
        }

        part_succs_.swap(new_part_succs);
      }

      void uniqSuccs() {
        auto succ_sorter = [] (const std::pair<DUG::PartID, DUG::DUGid> &p1,
            const std::pair<DUG::PartID, DUG::DUGid> &p2) {
          if (p1.second == p2.second) {
            return p1.first < p2.first;
          }
          return p1.second < p2.second;
        };
        std::sort(std::begin(part_succs_), std::end(part_succs_), succ_sorter);
        auto it = std::unique(std::begin(part_succs_), std::end(part_succs_));
        part_succs_.erase(it, std::end(part_succs_));
      }

      static bool classof(const SEG::Node *node) {
        return node->getKind() >= NodeKind::PartNode &&
          node->getKind() < NodeKind::PartNodeEnd;
      }

      void setDUGRep(DUG::DUGid new_rep) {
        // We shouldn't have our rep set if we have part data...
        assert(in_.empty());
        dugRep_ = new_rep;
      }

      DUG::DUGid getDUGRep() const {
        return dugRep_;
      }

      bool isDUGRep() const {
        return dugRep_ == DUG::DUGid::invalid();
      }

      void unite(SEG &, SEG::Node &n) {
        auto &node = cast<PartNode>(n);
        // Okay, we are not using the SEG rep stuff here, we have our own rep
        //   info
        node.dugRep_ = id();
        assert(dugRep_ == DUG::DUGid::invalid());

        // NOTE: I intentionally don't call unite down the chain.  We don't want
        //   to merge any other aspect of our node, just the rep
      }

      std::vector<std::pair<DUG::PartID, DUG::DUGid>> &getPartSuccs() {
        return part_succs_;
      }

      const std::vector<std::pair<DUG::PartID, DUG::DUGid>> &
      getPartSuccs() const {
        return part_succs_;
      }

     protected:
        // Successor partitons
        std::vector<std::pair<DUG::PartID, DUG::DUGid>> part_succs_;

        DUG::DUGid dugRep_ = DUG::DUGid::invalid();
        PtstoGraph in_;
      //}}}
    };

    class ConstPartNode : public PartNode {
      //{{{
     public:
        ConstPartNode(SEG::NodeID node_id, ObjectMap::ObjID dest,
              ObjectMap::ObjID src, std::set<ObjID>::iterator st,
              std::set<ObjID>::iterator en) :
            PartNode(NodeKind::ConstPartNode, node_id, dest, src, 0) {
          // Fill the object set
          // constObjSet_.resize(std::distance(st, en));
          constObjSet_.insert(std::end(constObjSet_), st, en);
        }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, TopLevelPtsto &pts, Worklist &wl,
            const std::vector<uint32_t> &priority) override;

        static bool classof(const SEG::Node *node) {
          return node->getKind() == NodeKind::ConstPartNode;
        }

     private:
        bool run_ = false;
        std::vector<ObjID> constObjSet_;
      //}}}
    };


    class LoadNode : public PartNode {
      //{{{
     public:
        LoadNode(SEG::NodeID node_id, ObjectMap::ObjID rep,
            ObjectMap::ObjID dest, ObjectMap::ObjID src, int32_t offset)
          : PartNode(NodeKind::LoadNode, node_id, rep, src, offset),
            realDest_(dest) { }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, TopLevelPtsto &pts, Worklist &wl,
            const std::vector<uint32_t> &priority) override;

        void processShared(DUG &dug, TopLevelPtsto &pts, Worklist &wl,
            const std::vector<uint32_t> &priority,
            PtstoGraph &addr_taken_pts);

        static bool classof(const SEG::Node *node) {
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
        StoreNode(SEG::NodeID node_id, ObjectMap::ObjID rep,
            ObjectMap::ObjID dest, ObjectMap::ObjID src, int32_t offset)
          : PartNode(NodeKind::StoreNode, node_id, rep, src, offset),
          realDest_(dest) { }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, TopLevelPtsto &pts, Worklist &wl,
            const std::vector<uint32_t> &priority) override;

        static bool classof(const SEG::Node *node) {
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

    class PhiNode : public PartNode {
      //{{{
     public:
        PhiNode(SEG::NodeID node_id, ObjectMap::ObjID id, int32_t offset)
          : PartNode(NodeKind::PhiNode, node_id, id, id, offset) { }

        // NOTE: Process implemented in "Solve.cpp"
        void process(DUG &dug, TopLevelPtsto &pts, Worklist &wl,
            const std::vector<uint32_t> &priority) override;

        static bool classof(const SEG::Node *node) {
          return node->getKind() == NodeKind::PhiNode;
        }
      //}}}
    };
    //}}}

 private:
    // Private variables {{{
    // The Partition equivalence for each object in the graph
    std::map<PartID, std::vector<ObjID>> partitionMap_;
    std::vector<Bitmap> relevantNodes_;
    std::map<ObjID, PartID> revPartitionMap_;
    // std::map<ObjID, std::vector<DUGid>> partNodes_;
    std::vector<std::vector<DUGid>> partNodes_;

    std::map<ObjID, SEG::NodeID> nodeMap_;

    std::map<ObjID, int32_t> structInfo_;

    SEG DUG_;
    //}}}
  //}}}
};

#endif  // INCLUDE_DUG_H_

