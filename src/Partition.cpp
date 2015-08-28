/*
 * Copyright (C) 2015 David Devecsery
 */

#include <algorithm>
#include <functional>
#include <map>
#include <tuple>
#include <utility>
#include <vector>

#include "include/SpecSFS.h"

#include "include/util.h"
#include "include/Andersens.h"
#include "include/ObjectMap.h"


#define SPECSFS_DEBUG
#include "include/Debug.h"

#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

// Anon namespace...
namespace {
static std::pair<const llvm::Value *, const llvm::Value *>
getSrcDestValue(ObjectMap::ObjID obj_id, const ObjectMap &omap,
    const DUG &dug) {
  auto src = omap.valueAtID(obj_id);

  const llvm::Value *dest;
  // A global init constraint will have a phony id -- a null value,
  // Instead look up in the DUG, and get the val based on the src
  if (src == nullptr) {
    auto &nd = dug.getNode(obj_id);

    src = omap.valueAtID(nd.src());
    dest = omap.valueAtID(nd.dest());
  } else if (auto pld = llvm::dyn_cast<const llvm::LoadInst>(src)) {
    src = pld->getPointerOperand();
    dest = src;
  } else if (auto pst = llvm::dyn_cast<const llvm::StoreInst>(src)) {
    src = pst->getOperand(0);
    dest = pst->getOperand(1);
  } else {
    llvm_unreachable("Isn't a load, store, or GV?");
  }

  return std::make_pair(src, dest);
}

}  // namespace

// Computes "access equivalent" partitions as described in "Flow-Sensitive
// Pointer ANalysis for Millions fo Lines of Code"
bool SpecSFS::computePartitions(DUG &dug, CFG &cfg, Andersens &aux,
    const ObjectMap &omap) {
  // Okay, heres what we do...
  // Let AE be a map from addr-taken variables to instructions
  //
  // For each load/store instruction I:
  //   for each var v accessed by I:
  //     AE[v].insert(I)
  //
  // For each equiv in AE:
  //   parts[equiv] += v;
  //
  // parts now holds all access equivalent partitons

  // Note I break naming scheme to AE here to match paper description of
  //   algorithm
  dout << "Running computePartitions\n";
  // Reverse aux map stuff, I got rid of it...
  /*
  std::map<int, const llvm::Value *> reverse_aux_map;

  // Create a mapping of aux_id to value *, so for converting aux ptsto sets to
  //   llvm::Values
  auto &aux_omap = aux.getObjectMap();
  std::for_each(std::begin(aux_omap), std::end(aux_omap),
      [&reverse_aux_map]
      (const std::pair<const llvm::Value *, int> &pr) {
    auto ret = reverse_aux_map.insert(std::make_pair(pr.second, pr.first));
    // Hopefully we managed the insert?
    assert(ret.second);
  });
  */


  // This map holds the conservative "Access Equivalence"
  //   sets for each pointer analyzed
  std::map<ObjectMap::ObjID, Bitmap> AE;

  llvm::dbgs() << "Doing AE creation loop\n";
  // Calculate the Access equivalencies:
  //   For each object in the CFG
  std::for_each(cfg.obj_to_cfg_begin(), cfg.obj_to_cfg_end(),
      [&cfg, &aux, &omap, &AE, &dug]
      (const std::pair<const ObjectMap::ObjID, CFG::CFGid> &pr) {
    // For each instruction within that group
    auto obj_id = pr.first;
    // Get the actual instruction
    auto src_dest = getSrcDestValue(obj_id, omap, dug);

    // val is dest...
    auto val = src_dest.second;

    // Now get the objects pointed to by it:
    // llvm::dbgs() << "queried val is : " << *val << "\n";
    auto &ptsto = aux.getPointsTo(val);

    auto old_val = omap.valueAtID(obj_id);
    llvm::dbgs() << "AE: Adding obj_id: " << obj_id << " for val: " <<
        *old_val << "\n";
    llvm::dbgs() << "  ptsto is:";
    for (auto id : ptsto) {
      llvm::dbgs() << " " << id;
    }
    llvm::dbgs() << "\n";

    auto &ae_set = AE[obj_id];
    // Say we do not contain a global initializer for this variable...
    //    That will be handled later

    // Now, add those to our access equivalence set:
    ae_set |= ptsto;
  });

  // Okay, I now have a populated AE, fill out our parts
  // Create the mechanisms needed to generate partition ids:
  IDGenerator<DUG::PartID> part_id_generator;

  // This maps groups together parts into equivalent sets (O(k*log(n)), where k
  //     is the ptsto size)
  std::map<Bitmap, std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>>, BitmapLT>  // NOLINT
    part_finder;

  /*
  llvm::dbgs() << "Dumping node_map for reference:\n";
  std::for_each(dug.node_map_cbegin(), dug.node_map_cend(),
      [](const std::pair<const ObjectMap::ObjID, DUG::DUGid> &pr) {
    llvm::dbgs() << "  " << pr.first << " -> " << pr.second << "\n";
  });
  */

  // Now group AE variables into partitions
  // Do this by iterating each Access Equivalent group, and grouping all
  //   nodes in it to a parttion
  llvm::dbgs() << "Doing AE grouping loop!\n";
  std::for_each(std::begin(AE), std::end(AE),
      [&part_finder, &dug](std::pair<const ObjectMap::ObjID, Bitmap> &pr) {
    llvm::dbgs() << "  For obj_id: " << pr.first << "\n";
    llvm::dbgs() << "  That's value: " << ValPrint(pr.first) << "\n";

    auto obj_id = pr.first;

    // Get the DUG node for this obj_id
    auto &dug_node = dug.getNode(obj_id);
      // auto dug_id = node_set.first->second;
    auto dug_id = dug_node.id();

    // Debug stuffs
    llvm::dbgs() << "Looking at obj: " <<
      ValPrint(obj_id) << "\n";
    llvm::dbgs() << "    got dug_id: " << dug_id << "\n";

    part_finder[pr.second].push_back(std::make_pair(dug_id, obj_id));
  });

  // Maps used to associate Partition Ids (PartID) with their contents
  std::map<DUG::PartID, std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>>>
    rev_part_map;
  std::map<DUG::PartID, std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>>>
    relevant_node_map;

  // We do one final pass to assign ids to the partiton
  // AND to calculate the load/store nodes relevant to that partition
  std::for_each(std::begin(part_finder), std::end(part_finder),
      [&rev_part_map, &relevant_node_map, &aux, &dug, &cfg,
        &part_id_generator, &omap]
      (std::pair<const Bitmap, std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>>> &pr) {  // NOLINT
    auto part_id = part_id_generator.next();

    // Find the relevant value for any member of this partiton (they all have
    //   the same pointsto properties)
    auto src_dest = getSrcDestValue(pr.second.front().second, omap, dug);

    auto src_val = src_dest.first;
    auto dest_val = src_dest.second;

    // Finding all relevant nodes:
    //   For each pointer modifying access, if it can alias with this ptsto set,
    //   add it to the relevant set
    std::for_each(cfg.obj_to_cfg_begin(), cfg.obj_to_cfg_end(),
        [&aux, &dug, &cfg, &relevant_node_map, &omap, &part_id, &src_val,
        &dest_val]
        (const std::pair<const ObjectMap::ObjID, CFG::CFGid> &pr) {
      auto obj_id = pr.first;

      // Find the relevant value of the node (its destination)
      auto src_dest = getSrcDestValue(obj_id, omap, dug);
      auto chk_dest_val = src_dest.first;
      auto chk_src_val = src_dest.second;

      // If that value aliases with a value in the partition (note all values in
      //   the partition are equivalent in this regard)
      // Then add it to our relevant_node_map

      if (llvm::isa<llvm::PointerType>(chk_dest_val->getType()) &&
          llvm::isa<llvm::PointerType>(src_val->getType()) &&
          aux.alias(AliasAnalysis::Location(src_val),
            AliasAnalysis::Location(chk_dest_val)) != AliasResult::NoAlias) {
        auto &node = dug.getNode(obj_id);

        relevant_node_map[part_id].emplace_back(node.id(), obj_id);
      }

      if (llvm::isa<llvm::PointerType>(chk_src_val->getType()) &&
          llvm::isa<llvm::PointerType>(dest_val->getType()) &&
          aux.alias(AliasAnalysis::Location(chk_src_val),
            AliasAnalysis::Location(dest_val)) != AliasResult::NoAlias) {
        auto &node = dug.getNode(obj_id);

        relevant_node_map[part_id].emplace_back(node.id(), obj_id);
      }
    });

    // Also add them if they are access equivalent
    auto &rel_vec = relevant_node_map[part_id];
    rel_vec.insert(std::end(rel_vec), std::begin(pr.second),
        std::end(pr.second));

    // Finally, indicate all top level variables pointed to by our
    //   partition:
    auto &rev_map_vec = rev_part_map[part_id];
    std::for_each(std::begin(pr.second), std::end(pr.second),
        [&rev_map_vec, &part_id, &omap, &dug]
        (std::pair<DUG::DUGid, ObjectMap::ObjID> &id_pr) {
      auto src_dest = getSrcDestValue(id_pr.second, omap, dug);
      auto src_val = src_dest.first;

      auto src_id = omap.getValue(src_val);
      llvm::dbgs() << "!!rev_part_map got src_id: " << src_id <<
          " : from val " << *src_val << "\n";
      rev_map_vec.emplace_back(id_pr.first, src_id);
    });

    // Now clean up rev_part_map vec
    std::sort(std::begin(rev_map_vec), std::end(rev_map_vec));
    auto uni_it = std::unique(std::begin(rev_map_vec), std::end(rev_map_vec));
    rev_map_vec.erase(uni_it, std::end(rev_map_vec));
  });

  // Create the node to partition mapping
  // To do this, we basically just reverse the part to node mapping
  // NOTE: We also deduplicate the node to part mapping here -- Is this needed?
  std::map<ObjectMap::ObjID, DUG::PartID> part_map;
  std::for_each(std::begin(rev_part_map), std::end(rev_part_map),
      [&part_map, &omap]
      (std::pair<const DUG::PartID, std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>>> &pr) {  // NOLINT
    // Okay... here we go
    // First deduplicate rev_part_map:
    std::sort(std::begin(pr.second), std::end(pr.second));
    auto it = std::unique(std::begin(pr.second), std::end(pr.second));
    pr.second.erase(it, std::end(pr.second));

    // Now, create mapping
    std::for_each(std::begin(pr.second), std::end(pr.second),
        [&pr, &part_map, &omap]
        (std::pair<DUG::DUGid, ObjectMap::ObjID> &id_pr) {
      part_map[id_pr.second] = pr.first;
    });
  });

  // Clean up/duplicate nodes in relevant_node_map
  std::for_each(std::begin(relevant_node_map), std::end(relevant_node_map),
      [] (std::pair<const DUG::PartID, std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>>> &pr) {  // NOLINT
    std::sort(std::begin(pr.second), std::end(pr.second));
    auto it = std::unique(std::begin(pr.second), std::end(pr.second));
    pr.second.erase(it, std::end(pr.second));
  });

  llvm::dbgs() << "End partitionToNode map is:\n";
  std::for_each(std::begin(rev_part_map), std::end(rev_part_map),
      [] (std::pair<const DUG::PartID, std::vector<std::pair<DUG::DUGid,
        ObjectMap::ObjID>>> &pr) {
    llvm::dbgs() << "  Have part_id: " << pr.first << "\n";
    std::for_each(std::begin(pr.second), std::end(pr.second),
        [] (std::pair<DUG::DUGid, ObjectMap::ObjID> &pr2) {
      llvm::dbgs() << "    dug_id " << pr2.first << ", obj_id " << pr2.second <<
          " : " << ValPrint(pr2.second) << "\n";
    });
  });

  // We now have our mappings, and we transfer them to the DUG
  dug.setNodeToPartition(std::move(part_map));
  dug.setPartitionToNodes(std::move(rev_part_map));
  dug.setRelevantNodes(std::move(relevant_node_map));

  return false;
}


bool SpecSFS::addPartitionsToDUG(DUG &graph, const CFG &ssa,
    const ObjectMap &omap) {
  // Map to track which partitions use each DUG node
  std::map<DUG::DUGid, std::vector<DUG::PartID>> node_to_partition;

  // For each partition, calculate the SSA of any nodes in that partiton
  std::for_each(graph.part_cbegin(), graph.part_cend(),
      [this, &graph, &ssa, &node_to_partition, &omap]
      (const std::pair<const DUG::PartID, std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>>> &pr) {  // NOLINT
    std::map<CFG::CFGid, DUG::DUGid> cfg_node_rep;

    // Create a clone of the ControlFlowGraph for this partition's ssa
    CFG::ControlFlowGraph part_graph =
      ssa.getSEG().clone<CFG::Node, CFG::Edge>();

    // Okay, now clear out any r, p, or c info for the nodes in that graph
    std::for_each(std::begin(part_graph), std::end(part_graph),
        [&part_graph](CFG::ControlFlowGraph::node_iter_type &pnode) {
      auto &node = llvm::cast<CFG::Node>(*pnode);

      node.clearM();
      node.clearR();
      node.clearC();

      node.clearDefs();
      node.clearUses();
      node.clearGlobalInits();
    });

    // Now calculate and fill in the info for each object
    //   in this partition
    const auto &part_id = pr.first;

    auto &rel_map = graph.getRelevantNodes();
    llvm::dbgs() << "Getting rel_map for: " << part_id << "\n";
    auto &rel_vec = rel_map[part_id];

    // We iterate over each object which may be accessed by this partition,
    //   using our rel_vec
    std::for_each(std::begin(rel_vec), std::end(rel_vec),
        [&ssa, &graph, &part_id, &omap,
            &part_graph, &node_to_partition]
        (const std::pair<DUG::DUGid, ObjectMap::ObjID> &id_pr) {
      DUG::DUGid dug_id = id_pr.first;
      // Get graph DUGid from ObjID
      ObjectMap::ObjID obj_id = id_pr.second;

      llvm::dbgs() << "part: " << part_id <<
          ": Getting obj_id: " << obj_id << " for dug_id: " << dug_id << "\n";
      llvm::dbgs() << "  that's value: " << *omap.valueAtID(obj_id) << "\n";

      auto &node = graph.getNode(dug_id);

      // Okay, now that we have the CFGid, update its info:
      // If this is a load:
      if (llvm::isa<DUG::LoadNode>(node)) {
        assert(llvm::isa<DUG::LoadNode>(graph.getNode(dug_id)));
        auto cfg_id = ssa.getCFGid(obj_id);
        auto node_set = part_graph.getNodes(cfg_id);
        assert(std::distance(node_set.first, node_set.second) == 1);
        // Ooops, I aliased a variable... shame on me
        auto &ld_node = node;
        auto &node = part_graph.getNode<CFG::Node>(node_set.first->second);

        // Set R
        node.setR();

        // Force M for part nodes?
        if (graph.getPart(ld_node.src()) == part_id) {
          node.setM();
        }

        // Denote this CFG node maps to this DUG node
        // FIXME:
        // MAHHHH this is the wrong type of ID... so I'm forcing it... because
        //   I'm ticked off!
        llvm::dbgs() << "Adding use to node: " << node.extId() << "\n";
        node.addUse(ObjectMap::ObjID(dug_id.val()));

        // Denote that this DUG node is part of this partition
        node_to_partition[dug_id].push_back(part_id);
      // If its a store:
      } else if (llvm::isa<DUG::StoreNode>(node)) {
        assert(llvm::isa<DUG::StoreNode>(graph.getNode(dug_id)));

        // Get the cfg_id of this node
        auto cfg_id = ssa.getCFGid(obj_id);

        // Get the node in the CFG
        auto node_set = part_graph.getNodes(cfg_id);
        assert(std::distance(node_set.first, node_set.second) == 1);
        auto &node = part_graph.getNode<CFG::Node>(node_set.first->second);

        // Set M and R
        node.setM();
        node.setR();

        // Possibly set C
        if (ssa.isStrong(obj_id)) {
          node.setC();
        }

        // Denote this CFGid references this DUG entry
        // FIXME:
        // MAHHHH this is the wrong type of ID... so I'm forcing it... because
        //   I'm ticked off!
        llvm::dbgs() << "Adding def to node: " << node.extId() << "\n";
        node.addDef(ObjectMap::ObjID(dug_id.val()));

        node_to_partition[dug_id].push_back(part_id);
      } else if (llvm::isa<DUG::GlobalInitNode>(node)) {
        // Assuming global init
        // For this we need a global init node in the CFG
        // The init node (CFGInit was made especially for this purpose
        auto cfg_node_pr = part_graph.getNodes(CFG::CFGInit);
        assert(std::distance(cfg_node_pr.first, cfg_node_pr.second) == 1);
        auto &cfg_node =
          part_graph.getNode<CFG::Node>(cfg_node_pr.first->second);

        cfg_node.setM();
        cfg_node.setR();

        // Convert the copy into a global init
        cfg_node.addGlobalInit(ObjectMap::ObjID(node.id().val()));
        node_to_partition[node.id()].push_back(part_id);
      } else {
        llvm_unreachable("Unrecognized node type!");
      }
    });

    // Now, calculate ssa form for this graph:
    auto part_ssa = computeSSA(part_graph);

    part_ssa.printDotFile("part_ssa.dot", *g_omap);

    /*
    dout << "part_ssa_map contains cfg ids:";
    std::for_each(part_ssa.node_map_begin(), part_ssa.node_map_end(),
        [] (std::pair<const CFG::CFGid, CFG::NodeID> &node_pair) {
      dout << " " << node_pair.first;
    });
    dout << "\n";
    */

    // Basically need to remap now... I can get a node by CFGid, and remap that
    //   to a NodeID for each CFGid I need...
    /*
    std::map<CFG::NodeID, CFG::CFGid> cfg_to_node;

    auto cfg_to_node_map = [&cfg_to_node, &part_ssa]
          (std::pair<const CFG::CFGid, std::vector<DUG::DUGid>> &pr) {
        auto node_pr = part_ssa.getNodes(pr.first);

        assert(std::distance(node_pr.first, node_pr.second) == 1);
        auto &node = part_ssa.getNode(node_pr.first->second);
        llvm::dbgs() << "  cfg_to_node[" << node.id() << "] = " << pr.first <<
          "\n";
        assert(cfg_to_node.find(node.id()) == std::end(cfg_to_node) ||
            cfg_to_node.at(node.id()) == pr.first);
        cfg_to_node.emplace(node.id(), pr.first);
      };

    llvm::dbgs() << "cfg_to_node_map(part_uses)\n";
    std::for_each(std::begin(part_uses), std::end(part_uses), cfg_to_node_map);
    llvm::dbgs() << "cfg_to_node_map(part_defs)\n";
    std::for_each(std::begin(part_defs), std::end(part_defs), cfg_to_node_map);
    */

    // Here we group the partSSA info, indicating which DUG nodes are affected
    //   by this partition
    // We add the computed partiton info into the part for each node
    // NOTE: We'll need to add some PHI nodes
    std::vector<std::tuple<CFG::NodeID, DUG::DUGid, DUG::PartID>> delayed_edges;
    std::for_each(part_ssa.topo_begin(), part_ssa.topo_end(),
        [&graph, &part_ssa, &cfg_node_rep,
            &delayed_edges, &part_id]
        (const CFG::NodeID node_id) {
      auto &ssa_node = part_ssa.getNode<CFG::Node>(node_id);

      auto cfg_id = ssa_node.extId();
      llvm::dbgs() << "Visiting cfg_id of: " << cfg_id << "\n";

      // The DUG rep of this id
      auto dug_id = DUG::DUGid();

      // If this node has a use, it is a ld node
      auto ld_it = ssa_node.uses_begin();
      // There is only one if its a store (def)
      auto st_it = ssa_node.defs_begin();

      auto glbl_it = ssa_node.glbl_inits_begin();

      bool have_ld = ld_it != ssa_node.uses_end();
      bool have_st = st_it != ssa_node.defs_end();
      bool have_glbl = glbl_it != ssa_node.glbl_inits_end();

      // Elect a "leader" id for each basic block
      if (have_st) {
        // it should be impossible to have a global and a store
        assert(!have_glbl);

        dug_id = DUG::DUGid(st_it->val());
        llvm::dbgs() << "  Got st of: " << dug_id << "\n";
        assert(llvm::isa<DUG::StoreNode>(graph.getNode(dug_id)));
      } else if (have_glbl) {
        auto glbl_dug_id = DUG::DUGid(glbl_it->val());
        auto &node = graph.getNode(glbl_dug_id);

        // We shouldn't have both a store and a global on the same CFG node
        assert(!have_st);

        // Glbl inits are copies...
        assert(llvm::isa<DUG::GlobalInitNode>(node));

        // Add this node to the DUG, and add the src of this copy
        dug_id = glbl_dug_id;
      } else if (have_ld) {
        dug_id = DUG::DUGid(ld_it->val());
        llvm::dbgs() << "  Got ld of: " << dug_id << "\n";
        llvm::dbgs() << "  ld size is: " <<
          std::distance(ssa_node.uses_begin(), ssa_node.uses_end())
          << "\n";
        assert(llvm::isa<DUG::LoadNode>(graph.getNode(dug_id)));
      // There may also be none (in this case its an phi node)
      } else {
        dug_id = graph.addPhi();
        llvm::dbgs() << "  Got phi of: " << dug_id << "\n";
        assert(llvm::isa<DUG::PhiNode>(graph.getNode(dug_id)));
      }

      // Update our cfg_node_rep map, so we can fill in preds later
      llvm::dbgs() << "  Setting cfg_node_rep for " << cfg_id << " to: "
          << dug_id << "\n";
      assert(cfg_node_rep.find(cfg_id) == std::end(cfg_node_rep));
      cfg_node_rep.emplace(cfg_id, dug_id);

      // Put an edge from the basic block's "leader" to its members
      if (have_st) {
        // It should be impossible to have a store and a global
        assert(!have_glbl);
        bool first = true;

        // for (auto &st_id : st_list) {
        std::for_each(ssa_node.defs_begin(), ssa_node.defs_end(),
            [&graph, &dug_id, &part_id, &first]
            (ObjectMap::ObjID obj_id) {
          // FIXME: This is a really hacky thing...
          DUG::DUGid st_id = DUG::DUGid(obj_id.val());

          if (first) {
            first = false;
            return;
          }

          llvm::dbgs() << "  --Adding rep-st edge {" << dug_id << " -(" <<
              part_id << ")-> " << st_id << "}\n";
          graph.addEdge(dug_id, st_id, part_id);
        });
      }

      if (have_ld) {
        bool first = true;
        bool skip_first = !have_st && !have_glbl;

        std::for_each(ssa_node.uses_begin(), ssa_node.uses_end(),
            [&graph, &dug_id, &part_id, &first, &skip_first]
            (ObjectMap::ObjID obj_id) {
          // FIXME: This is a really hacky thing...
          DUG::DUGid ld_id = DUG::DUGid(obj_id.val());
          // Skip the first entry if we have already accounted for it (our rep
          //    is a load)
          if (first && skip_first) {
            first = false;
            return;
          }

          llvm::dbgs() << "  --Adding rep-ld edge {" << dug_id << " -(" <<
              part_id << ")-> " << ld_id << "}\n";
          graph.addEdge(dug_id, ld_id, part_id);
        });
      }

      /*
      auto node_set = part_ssa.getNodes(cfg_cfg_id);
      assert(std::distance(node_set.first, node_set.second) == 1);
      */
      auto &node = part_ssa.getNode<CFG::Node>(node_id);
      const auto &preds = node.preds();

      // Assert says if this node is a phi node, it must have at least one pred
      assert(
          // Is not a phi
          !(!have_ld && !have_st && !have_glbl) ||
          // If it is a phi, it must have at least one pred
          !preds.empty());

      // Put an edge from each pred in G to the part leader
      std::for_each(std::begin(preds), std::end(preds),
          [&graph, &delayed_edges, &cfg_node_rep, &dug_id, &part_id, &part_ssa]
          (const CFG::EdgeID pred_edge_id) {
        auto pred_node_id = part_ssa.getEdge(pred_edge_id).src();

        auto pred_cfg_id = part_ssa.getNode<CFG::Node>(pred_node_id).extId();
        // llvm::dbgs() << "have pred_node_id of: " << pred_node_id << "\n";

        // NOTE: if we were not doing a topo order we may have to evaluate the
        //   pred here
        // dout << "Finding cfg_node_rep at: " << pred_cfg_id << "\n";
        auto pred_rep_it = cfg_node_rep.find(pred_cfg_id);
        if (pred_rep_it == std::end(cfg_node_rep)) {
          // Delay our rep resolving until after we've visited all nodes
          llvm::dbgs() << "  ||Delaying cfg edge (pred id: " << pred_cfg_id
              << ") {" << "??" << " -(" << part_id << ")-> " << dug_id << "}\n";
          delayed_edges.emplace_back(pred_node_id, dug_id, part_id);
        } else {
          DUG::DUGid &pred_rep_id = pred_rep_it->second;

          llvm::dbgs() << "  --Adding cfg edge {" << pred_rep_id << " -(" <<
            part_id << ")-> " << dug_id << "}\n";
          graph.addEdge(pred_rep_id, dug_id, part_id);
        }
      });
    });

    std::vector<std::tuple<CFG::CFGid, DUG::DUGid, DUG::PartID>>
      delayed_dedup_edges;

    std::for_each(std::begin(delayed_edges), std::end(delayed_edges),
        [&graph, &part_ssa, &cfg_node_rep, &delayed_dedup_edges]
        (std::tuple<CFG::NodeID, DUG::DUGid, DUG::PartID> &tup) {
      auto pred_cfg_id = part_ssa.getNode(std::get<0>(tup)).extId();
      delayed_dedup_edges.emplace_back(pred_cfg_id, std::get<1>(tup),
        std::get<2>(tup));
    });

    std::sort(std::begin(delayed_dedup_edges), std::end(delayed_dedup_edges));
    auto dedup_it = std::unique(std::begin(delayed_dedup_edges),
        std::end(delayed_dedup_edges));
    delayed_dedup_edges.erase(dedup_it, std::end(delayed_dedup_edges));

    std::for_each(std::begin(delayed_dedup_edges),
        std::end(delayed_dedup_edges),
          [&graph, &cfg_node_rep]
          (std::tuple<CFG::CFGid, DUG::DUGid, DUG::PartID> &tup) {
        auto pred_cfg_id = std::get<0>(tup);
        auto pred_rep_it = cfg_node_rep.find(pred_cfg_id);
        assert(pred_rep_it != std::end(cfg_node_rep));

        auto pred_rep_id = pred_rep_it->second;

        llvm::dbgs() << "  --Adding delayed-cfg edge {" << pred_rep_id <<
            " -(" << std::get<2>(tup) << ")-> " << std::get<1>(tup) << "}\n";
        graph.addEdge(pred_rep_id, std::get<1>(tup), std::get<2>(tup));
    });
  });

  // We need to alert each load/store node which objects they may possibly
  //   contain
  // This information was gathered from AUX...
  // We have this info in part_map
  // We need DUGid -> part
  // Then for each DUGid:
  //   For each part containing this id:
  //     For each obj in part
  //       add obj to dug_mapping
  //
  //   Add dug_mapping to node ptsto
  llvm::dbgs() << "Setting up partGraph for each node!\n";
  std::for_each(node_to_partition.cbegin(), node_to_partition.cend(),
      [&graph]
      (const std::pair<const DUG::DUGid, std::vector<DUG::PartID>> &pr) {
    auto &part_node = llvm::cast<DUG::PartNode>(graph.getNode(pr.first));
    auto &parts = pr.second;
    std::vector<ObjectMap::ObjID> vars;

    llvm::dbgs() << "  Looking at ID: " << part_node.id() << "\n";

    std::for_each(std::begin(parts), std::end(parts),
        [&graph, &vars] (const DUG::PartID &part_id) {
      auto &objs = graph.getObjs(part_id);
      llvm::dbgs() << "    Checking part_id: " << part_id << "\n";
      std::for_each(std::begin(objs), std::end(objs),
          [&graph, &vars] (std::pair<DUG::DUGid, ObjectMap::ObjID> &pr) {
        llvm::dbgs() << "      Adding var: " << pr.second << "\n";
        vars.emplace_back(pr.second);
      });
    });

    part_node.setupPartGraph(vars);
  });

  return false;
}

