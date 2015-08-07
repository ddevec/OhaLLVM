/*
 * Copyright (C) 2015 David Devecsery
 */

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

  std::map<Bitmap, std::vector<DUG::DUGid>, BitmapLT> part_finder;
  // Now create partitions
  std::for_each(std::begin(AE), std::end(AE),
      [&part_finder, &dug](std::pair<const ObjectMap::ObjID, Bitmap> &pr) {
    DUG::DUGid dug_id = dug.getNode(pr.first).id();
    part_finder[pr.second].push_back(dug_id);
  });

  // Assign ID's to the partitons:
  std::map<DUG::PartID, std::vector<DUG::DUGid>> rev_part_map;
  std::for_each(std::begin(part_finder), std::end(part_finder),
      [&rev_part_map, &part_id_generator]
      (std::pair<const Bitmap, std::vector<DUG::DUGid>> &pr) {
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
  std::for_each(graph.part_begin(), graph.part_end(),
      [this, &graph, &ssa, &node_to_partition]
      (const std::pair<const DUG::PartID, std::vector<DUG::DUGid>> &pr) {
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

    // FIXME: DEBUGGING -- remove
    dout << "part_graph contains cfg ids:";
    std::for_each(std::begin(part_graph), std::end(part_graph),
        [] (SEG<CFG::CFGid>::node_iter_type &pnode) {
      if (pnode != nullptr) {
        dout << " " << pnode->id();
      }
    });
    dout << "\n";

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
        (DUG::DUGid dug_id) {
      // Get graph DUGid from ObjID
      ObjectMap::ObjID obj_id = graph.getNode(dug_id).extId();
      // Get the CFGid associated with this object:
      auto type = ssa.getType(obj_id);

      // Okay, now that we have the CFGid, update its info:
      // If this is a load:
      if (type == ConstraintType::Load) {
        dout << "Getting cfg node for obj_id: " << obj_id << "\n";
        auto cfg_id = ssa.getCFGid(obj_id);
        dout << "Got node: " << cfg_id << "\n";
        auto &node = part_graph.getNode<CFG::Node>(cfg_id);
        // Set R
        node.setR();

        // Denote this CFG node maps to this DUG node
        part_uses[cfg_id].push_back(dug_id);

        // Denote that this DUG node is part of this partition
        node_to_partition[dug_id].push_back(part_id);
      // If its a store:
      } else if (type == ConstraintType::Store) {
        auto cfg_id = ssa.getCFGid(obj_id);
        auto &node = part_graph.getNode<CFG::Node>(cfg_id);
        // Set M
        node.setM();

        // Possibly set C
        if (ssa.isStrong(obj_id)) {
          node.setC();
        }

        // Denote this CFGid references this DUG entry
        assert(part_defs.find(cfg_id) == std::end(part_defs));
        part_defs[cfg_id] = dug_id;

        node_to_partition[dug_id].push_back(part_id);
      }
    });

    // Now, calculate ssa form for this graph:
    auto part_ssa = computeSSA(part_graph);

    // Here we group the partSSA info, indicating which DUG nodes are affected
    //   by this partition
    // We add the computed partiton info into the part for each node
    // NOTE: We'll need to add some PHI nodes
    std::for_each(part_ssa.topo_begin(), part_ssa.topo_end(),
        [&graph, &part_ssa, &part_rep,
            &part_uses, &part_defs, &part_id]
        (const CFG::NodeID node_id) {
      // Get the CFGid of this node:
      auto &part_node = part_ssa.getNode(node_id);
      auto cfg_id = part_node.extId();

      // Now, for this CFGid, get all associated DUG Nodes in this partition:
      // There may be many if its a load (use)
      auto ld_it = part_uses.find(cfg_id);

      auto dug_id = DUG::DUGid();

      // There is only one if its a store (def)
      auto st_it = part_defs.find(cfg_id);

      bool have_ld = ld_it == std::end(part_uses);
      bool have_st = st_it == std::end(part_defs);

      // Elect a "leader" id for each part
      if (have_st) {
        dug_id = st_it->second;
      } else if (have_ld) {
        dug_id = ld_it->second.front();
      // There may also be none (in this case its an phi node)
      } else {
        dug_id = graph.addPhi();
      }

      // Update our part_rep map, so we can fill in preds later
      part_rep[cfg_id] = dug_id;

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

      auto &node = part_ssa.getNode<CFG::Node>(cfg_id);
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
    std::vector<DUG::DUGid> vars;

    std::for_each(std::begin(parts), std::end(parts),
        [&graph, &vars] (DUG::PartID part_id) {
      auto &objs = graph.getObjs(part_id);
      vars.insert(vars.end(), std::begin(objs), std::end(objs));
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

