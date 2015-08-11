/*
 * Copyright (C) 2015 David Devecsery
 */

#include <algorithm>
#include <functional>
#include <map>
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

// Computes "access equivalent" partitions as described in "Flow-Sensitive
// Pointer ANalysis for Millions fo Lines of Code"
bool SpecSFS::computePartitions(DUG &dug, CFG &cfg, const Andersens &aux,
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
  std::map<ObjectMap::ObjID, Bitmap> AE;
  auto calc_ae = [&cfg, &aux, &omap, &AE]
      (const std::pair<const CFG::CFGid, std::vector<ObjectMap::ObjID>> &pr) {
    // For each instruction within that group
    std::for_each(std::begin(pr.second), std::end(pr.second),
        [&cfg, &aux, &omap, &AE]
        (ObjectMap::ObjID obj_id) {
      // Get the actual instruction
      const llvm::Value *val = omap.valueAtID(obj_id);

      // Now get the objects pointed to by it:
      auto &ptsto = aux.getPointsTo(val);

      dout << "AE: Adding obj_id: " << obj_id << " for val: " << *val << "\n";

      auto &ae_set = AE[obj_id];
      // Say we do not contain a global initializer for this variable...
      //    That will be handled later

      // Now, add those to our access equivalence set:
      ae_set |= ptsto;
    });
  };

  // For each store group
  std::for_each(cfg.defs_begin(), cfg.defs_end(), calc_ae);

  // Do the same thing for loads
  std::for_each(cfg.uses_begin(), cfg.uses_end(), calc_ae);

  // Okay, I now have a populated AE, fill out our parts
  // Create the mechanisms needed to generate partition ids:
  IDGenerator<DUG::PartID> part_id_generator;

  std::map<Bitmap, std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>>, BitmapLT>  // NOLINT
    part_finder;
  // Now create partitions
  llvm::dbgs() << "Doing part creation loop!\n";
  std::for_each(std::begin(AE), std::end(AE),
      [&part_finder, &dug](std::pair<const ObjectMap::ObjID, Bitmap> &pr) {
    llvm::dbgs() << "  For obj_id: " << pr.first << "\n";
    auto node_set = dug.getNodes(pr.first);
    std::for_each(node_set.first, node_set.second,
        [&dug, &part_finder, &pr]
        (std::pair<const ObjectMap::ObjID, SEG<ObjectMap::ObjID>::NodeID>
         &node_pair) {
      llvm::dbgs() << "    got dug_id: " << node_pair.second << "\n";
      DUG::DUGid dug_id = node_pair.second;
      part_finder[pr.second].push_back(std::make_pair(dug_id, pr.first));
    });
  });

  // Assign ID's to the partitons:
  std::map<DUG::PartID, std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>>>
    rev_part_map;
  std::for_each(std::begin(part_finder), std::end(part_finder),
      [&rev_part_map, &part_id_generator]
      (std::pair<const Bitmap, std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>>> &pr) {  // NOLINT
    // Remove duplicate dugids:
    std::sort(std::begin(pr.second), std::end(pr.second));
    auto dug_id_it = std::unique(std::begin(pr.second), std::end(pr.second));
    pr.second.erase(dug_id_it, std::end(pr.second));

    rev_part_map.emplace(std::piecewise_construct,
          std::make_tuple(part_id_generator.next()),
          std::make_tuple(std::move(pr.second)));
  });

  dout << "Running computePartitions\n";

  dug.setPartitionToNodes(std::move(rev_part_map));

  // We now have our PartID to DUG::ObjID mapping in part_map
  return false;
}


bool SpecSFS::addPartitionsToDUG(DUG &graph, const CFG &ssa) {
  // Map to track which partitions each DUG node is in
  std::map<DUG::DUGid, std::vector<DUG::PartID>> node_to_partition;
  // For each partition, calculate the SSA of any nodes in that partiton
  std::for_each(graph.part_cbegin(), graph.part_cend(),
      [this, &graph, &ssa, &node_to_partition]
      (const std::pair<const DUG::PartID, std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>>> &pr) {  // NOLINT
    std::map<CFG::CFGid, DUG::DUGid> part_rep;

    dout << "ssa contains cfg ids:";
    std::for_each(std::begin(ssa.getSEG()), std::end(ssa.getSEG()),
        [] (const SEG<CFG::CFGid>::node_iter_type &pnode) {
      if (pnode != nullptr) {
        dout << " " << pnode->id();
      }
    });
    dout << "\n";

    // Create a clone of the ControlFlowGraph for this partition's ssa
    CFG::ControlFlowGraph part_graph =
      ssa.getSEG().clone<CFG::Node, CFG::Edge>();

      /*
    // FIXME: DEBUGGING -- remove
    dout << "part_graph contains cfg ids:";
    std::for_each(std::begin(part_graph), std::end(part_graph),
        [] (SEG<CFG::CFGid>::node_iter_type &pnode) {
      dout << " " << pnode->id();
    });
    dout << "\n";

    dout << "part_graph_map contains cfg ids:";
    std::for_each(part_graph.node_map_begin(), part_graph.node_map_end(),
        [] (std::pair<const CFG::CFGid, CFG::NodeID> &node_pair) {
      dout << " " << node_pair.first;
    });
    dout << "\n";
    */

    // Okay, now clear out any r, p, or c info for the nodes in that graph
    std::for_each(std::begin(part_graph), std::end(part_graph),
        [&part_graph](CFG::ControlFlowGraph::node_iter_type &pnode) {
      auto &node = llvm::cast<CFG::Node>(*pnode);

      node.clearM();
      node.clearR();
      node.clearC();
    });

    std::map<CFG::CFGid, DUG::DUGid> part_defs;
    std::map<CFG::CFGid, std::vector<DUG::DUGid>> part_uses;

    // Now calculate and fill in the info for each object
    //   in this partition
    const auto &dug_ids = pr.second;

    const auto &part_id = pr.first;
    std::for_each(std::begin(dug_ids), std::end(dug_ids),
        [&ssa, &graph, &part_defs, &part_uses, &part_id,
            &part_graph, &node_to_partition]
        (const std::pair<DUG::DUGid, ObjectMap::ObjID> &id_pr) {
      DUG::DUGid dug_id = id_pr.first;
      // Get graph DUGid from ObjID
      ObjectMap::ObjID obj_id = id_pr.second;
      // graph.getNode(id_pr.first).extId();

      llvm::dbgs() << "part: " << part_id <<
          ": Getting obj_id: " << obj_id << " for dug_id: " << dug_id << "\n";
      extern ObjectMap &g_omap;
      llvm::dbgs() << "  that's value" << *g_omap.valueAtID(obj_id) << "\n";

      // Get the CFGid associated with this object:
      auto type = ssa.getType(obj_id);

      // Okay, now that we have the CFGid, update its info:
      // If this is a load:
      if (type == ConstraintType::Load) {
        auto cfg_id = ssa.getCFGid(obj_id);
        dout << "  Have Load node at " << cfg_id << "!\n";
        auto node_set = part_graph.getNodes(cfg_id);
        assert(std::distance(node_set.first, node_set.second) == 1);
        auto &node = part_graph.getNode<CFG::Node>(node_set.first->second);
        // Set R
        node.setR();

        // Denote this CFG node maps to this DUG node
        part_uses[cfg_id].push_back(dug_id);

        // Denote that this DUG node is part of this partition
        node_to_partition[dug_id].push_back(part_id);
      // If its a store:
      } else if (type == ConstraintType::Store) {
        auto cfg_id = ssa.getCFGid(obj_id);
        dout << "  Have Store node at " << cfg_id << "!\n";
        auto node_set = part_graph.getNodes(cfg_id);
        assert(std::distance(node_set.first, node_set.second) == 1);
        auto &node = part_graph.getNode<CFG::Node>(node_set.first->second);
        // Set M
        node.setM();
        node.setR();

        // Possibly set C
        if (ssa.isStrong(obj_id)) {
          node.setC();
        }

        // Denote this CFGid references this DUG entry
        llvm::dbgs() << "Adding dug_node: " << dug_id <<
          " as part_def for cfg_id: " << cfg_id << "\n";
        assert(part_defs.find(cfg_id) == std::end(part_defs));
        part_defs[cfg_id] = dug_id;

        node_to_partition[dug_id].push_back(part_id);
      }
    });

    // Now, calculate ssa form for this graph:
    auto part_ssa = computeSSA(part_graph);

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
    std::map<CFG::NodeID, CFG::CFGid> cfg_to_node;
    std::for_each(std::begin(part_uses), std::end(part_uses),
        [&cfg_to_node, &part_ssa]
        (std::pair<const CFG::CFGid, std::vector<DUG::DUGid>> &pr) {
      auto node_pr = part_ssa.getNodes(pr.first);
      assert(std::distance(node_pr.first, node_pr.second) == 1);
      auto &node = part_ssa.getNode(node_pr.first->second);
      cfg_to_node[node.id()] = pr.first;
    });

    std::for_each(std::begin(part_defs), std::end(part_defs),
        [&cfg_to_node, &part_ssa]
        (std::pair<const CFG::CFGid, DUG::DUGid> &pr) {
      llvm::dbgs() << "Scanning for cfgid: " << pr.first <<
          " in ssa from part_defs\n";
      auto node_pr = part_ssa.getNodes(pr.first);
      assert(std::distance(node_pr.first, node_pr.second) == 1);
      auto &node = part_ssa.getNode(node_pr.first->second);
      cfg_to_node[node.id()] = pr.first;
    });


    // Here we group the partSSA info, indicating which DUG nodes are affected
    //   by this partition
    // We add the computed partiton info into the part for each node
    // NOTE: We'll need to add some PHI nodes
    std::for_each(part_ssa.topo_begin(), part_ssa.topo_end(),
        [&graph, &part_ssa, &part_rep, &cfg_to_node,
            &part_uses, &part_defs, &part_id]
        (const CFG::NodeID node_id) {
      // Get the CFGid of this node:
      auto cfg_id = cfg_to_node[node_id];


      auto dug_id = DUG::DUGid();

      // Now, for this CFGid, get all associated DUG Nodes in this partition:
      // There may be many if its a load (use)
      auto ld_it = part_uses.find(cfg_id);
      // There is only one if its a store (def)
      auto st_it = part_defs.find(cfg_id);

      bool have_ld = ld_it != std::end(part_uses);
      bool have_st = st_it != std::end(part_defs);

      // Elect a "leader" id for each part
      if (have_st) {
        dug_id = st_it->second;
        llvm::dbgs() << "Got st of: " << dug_id << "\n";
      } else if (have_ld) {
        dug_id = ld_it->second.front();
        llvm::dbgs() << "Got ld of: " << dug_id << "\n";
      // There may also be none (in this case its an phi node)
      } else {
        dug_id = graph.addPhi();
        llvm::dbgs() << "Got phi of: " << dug_id << "\n";
      }

      // Update our part_rep map, so we can fill in preds later
      auto &part_node = part_ssa.getNode(node_id);
      auto cfg_cfg_id = part_node.extId();
      llvm::dbgs() << "Setting part_rep to: " << dug_id << "\n";
      part_rep[cfg_cfg_id] = dug_id;

      // Put an edge from the part's "leader" to its members
      bool skip_first = !have_st;
      if (have_ld) {
        auto &ld_list = ld_it->second;
        bool first = true;
        for (auto &ld_id : ld_list) {
          // Skip the first entry if we have already accounted for it (our rep
          //    is a load)
          if (first && skip_first) {
            first = false;
            continue;
          }

          graph.addEdge(dug_id, ld_id, part_id);
        }
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
          !(!have_ld && !have_st) ||
          // If it is a phi, it must have at least one pred
          !preds.empty());

      // Put an edge from each pred in G to the part leader
      std::for_each(std::begin(preds), std::end(preds),
          [&graph, &part_rep, &dug_id, &part_id, &part_ssa]
          (const CFG::EdgeID pred_edge_id) {
        auto pred_node_id = part_ssa.getEdge(pred_edge_id).src();
        auto pred_cfg_id = part_ssa.getNode<CFG::Node>(pred_node_id).extId();

        // NOTE: if we were not doing a topo order we may have to evaluate the
        //   pred here
        auto pred_rep_it = part_rep.find(pred_cfg_id);
        assert(pred_rep_it != std::end(part_rep));

        DUG::DUGid &pred_rep_id = pred_rep_it->second;

        dout << "Adding edge {" << pred_rep_id << " -(" << part_id << ")-> "
            << dug_id << "}\n";
        graph.addEdge(pred_rep_id, dug_id, part_id);
      });
    });
  });

  // We need to alert each load/store node which objects they may possibly
  //   contain
  // This information was gathered from AUX...
  // We have this info in part_map
  // We need DUGid -> part
  // Then for each DUGid:
  std::for_each(std::begin(node_to_partition), std::end(node_to_partition),
      [&graph]
      (std::pair<const DUG::DUGid, std::vector<DUG::PartID>> &pr) {
    auto &part_node = llvm::cast<DUG::PartNode>(graph.getNode(pr.first));
    auto &parts = pr.second;
    std::vector<ObjectMap::ObjID> vars;

    std::for_each(std::begin(parts), std::end(parts),
        [&graph, &vars] (DUG::PartID part_id) {
      auto &objs = graph.getObjs(part_id);
      std::for_each(std::begin(objs), std::end(objs),
          [&graph, &vars] (std::pair<DUG::DUGid, ObjectMap::ObjID> &pr) {
        // The var array is of ObjID, (or extIds)
        vars.emplace_back(graph.getNode(pr.first).extId());
      });
    });

    part_node.setupPartGraph(vars);
  });
  //   For each part containing this id:
  //     For each obj in part
  //       add obj to dug_mapping
  //
  //   Add dug_mapping to node ptsto

  return false;
}

