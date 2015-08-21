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


  // Now calculate our "access equivalence sets" for defs and uses
  std::map<ObjectMap::ObjID, Bitmap> AE;
  auto calc_ae = [&cfg, &aux, &omap, &AE]
      (const std::pair<const CFG::CFGid, std::vector<ObjectMap::ObjID>> &pr) {
    // For each instruction within that group
    std::for_each(std::begin(pr.second), std::end(pr.second),
        [&cfg, &aux, &omap, &AE]
        (ObjectMap::ObjID obj_id) {
      // Get the actual instruction
      const llvm::Value *val = omap.valueAtID(obj_id);
      auto old_val = val;

      if (auto pld = llvm::dyn_cast<const llvm::LoadInst>(val)) {
        val = pld->getPointerOperand();
      } else {
        auto pst = llvm::cast<const llvm::StoreInst>(val);
        val = pst->getOperand(1);
      }

      // Now get the objects pointed to by it:
      auto &ptsto = aux.getPointsTo(val);

      dout << "AE: Adding obj_id: " << obj_id << " for val: " <<
          *old_val << "\n";
      dout << "  ptsto is:";
      for (auto id : ptsto) {
        dout << " " << id;
      }
      dout << "\n";

      auto &ae_set = AE[obj_id];
      // Say we do not contain a global initializer for this variable...
      //    That will be handled later

      // Now, add those to our access equivalence set:
      ae_set |= ptsto;
    });
  };

  // Calculate the Access elquivalencies:
  //   For each store
  std::for_each(cfg.defs_begin(), cfg.defs_end(), calc_ae);

  //   And for each load
  std::for_each(cfg.uses_begin(), cfg.uses_end(), calc_ae);

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

  // Now create partitions
  // Do this by iterating each access equivalent group, and grouping all
  //   nodes in it to a parttion
  llvm::dbgs() << "Doing part creation loop!\n";
  std::for_each(std::begin(AE), std::end(AE),
      [&part_finder, &dug](std::pair<const ObjectMap::ObjID, Bitmap> &pr) {
    llvm::dbgs() << "  For obj_id: " << pr.first << "\n";
    auto node_set = dug.getNodes(pr.first);
    // We should have found at least 1 node....
    assert(std::distance(node_set.first, node_set.second) != 0);

    bool found_node = false;
    std::for_each(node_set.first, node_set.second,
        [&dug, &part_finder, &pr, &found_node]
        (std::pair<const ObjectMap::ObjID, DUG::DUGid> &node_pair) {
      extern ObjectMap &g_omap;
      llvm::dbgs() << "Looking at obj: " <<
        *g_omap.valueAtID(node_pair.first) << "\n";
      DUG::DUGid dug_id = node_pair.second;
      auto &nd = dug.getNode(dug_id);
      llvm::dbgs() << "    got dug_id: " << node_pair.second << "\n";
      // Since we may have multiple mappings from an external id, we filter out
      //   any non-load/store nodes
      if (llvm::isa<DUG::StoreNode>(nd) || llvm::isa<DUG::LoadNode>(nd)) {
        found_node = true;
        part_finder[pr.second].push_back(std::make_pair(dug_id, pr.first));
      }
    });
    assert(found_node);
  });

  // Assign ID's to the partitons:
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
    // Remove duplicate dugids:
    std::sort(std::begin(pr.second), std::end(pr.second));
    auto dug_id_it = std::unique(std::begin(pr.second), std::end(pr.second));
    pr.second.erase(dug_id_it, std::end(pr.second));
    auto part_id = part_id_generator.next();

    auto val = omap.valueAtID(pr.second.front().second);
    llvm::dbgs() << "Considering value: " << *val << " for part_id: " <<
        part_id << "\n";
    if (auto pld = llvm::dyn_cast<const llvm::LoadInst>(val)) {
      val = pld->getPointerOperand();
    }

    auto consider_node =
      [&aux, &dug, &cfg, &relevant_node_map, &omap, &part_id, &val]
      (const std::pair<const CFG::CFGid, std::vector<ObjectMap::ObjID>> &pr) {
        // For each node, get the ptsto:
        std::for_each(std::begin(pr.second), std::end(pr.second),
          [&val, &aux, &omap, &cfg, &part_id, &dug, &relevant_node_map]
          (ObjectMap::ObjID obj_id) {
          auto test_val = omap.valueAtID(obj_id);
          if (auto pld = llvm::dyn_cast<const llvm::LoadInst>(test_val)) {
            test_val = pld->getPointerOperand();
          }
          if (aux.alias(AliasAnalysis::Location(val),
              AliasAnalysis::Location(test_val)) != AliasResult::NoAlias) {
            auto nodes = dug.getNodes(obj_id);
            std::for_each(nodes.first, nodes.second,
                [&relevant_node_map, &part_id, &dug, &obj_id]
                (std::pair<const DUG::ObjID, DUG::DUGid> &pr) {
              auto &node = dug.getNode(pr.second);

              if (llvm::isa<DUG::LoadNode>(node) ||
                  llvm::isa<DUG::StoreNode>(node)) {
                relevant_node_map[part_id].push_back(
                  std::make_pair(node.id(), obj_id));
              }
            });
          }
        });
      };

    // FIXME: The first relevant node for this partiton should be a node in the
    //   partition?
    relevant_node_map[part_id].push_back(pr.second.front());

    std::for_each(cfg.uses_begin(), cfg.uses_end(), consider_node);
    std::for_each(cfg.defs_begin(), cfg.defs_end(), consider_node);

    rev_part_map.emplace(std::piecewise_construct,
          std::make_tuple(part_id),
          std::make_tuple(std::move(pr.second)));
  });

  dout << "Running computePartitions\n";
  std::map<DUG::DUGid, DUG::PartID> part_map;
  std::for_each(std::begin(rev_part_map), std::end(rev_part_map),
      [&part_map] (std::pair<const DUG::PartID, std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>>> &pr) {  // NOLINT
    // Okay... here we go
    // First deduplicate rev_part_map:
    std::sort(std::begin(pr.second), std::end(pr.second));
    auto it = std::unique(std::begin(pr.second), std::end(pr.second));
    pr.second.erase(it, std::end(pr.second));

    // Now, create mapping
    std::for_each(std::begin(pr.second), std::end(pr.second),
        [&pr, &part_map] (std::pair<DUG::DUGid, ObjectMap::ObjID> &id_pr) {
      part_map[id_pr.first] = pr.first;
    });
  });

  // Clean up duplicated nodes in relevant_node_map
  std::for_each(std::begin(relevant_node_map), std::end(relevant_node_map),
      []
      (std::pair<const DUG::PartID, std::vector<std::pair<DUG::DUGid, ObjectMap::ObjID>>> &pr) {  // NOLINT
    std::sort(std::begin(pr.second), std::end(pr.second));
    auto it = std::unique(std::begin(pr.second), std::end(pr.second));
    pr.second.erase(it, std::end(pr.second));
  });

  dug.setNodeToPartition(std::move(part_map));
  dug.setPartitionToNodes(std::move(rev_part_map));
  dug.setRelevantNodes(std::move(relevant_node_map));

  // We now have our PartID to DUG::ObjID mapping in part_map
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
    });

    std::map<CFG::CFGid, std::vector<DUG::DUGid>> part_defs;
    std::map<CFG::CFGid, std::vector<DUG::DUGid>> part_uses;

    // Now calculate and fill in the info for each object
    //   in this partition
    const auto &part_id = pr.first;

    auto &rel_map = graph.getRelevantNodes();
    llvm::dbgs() << "Getting rel_map for: " << part_id << "\n";
    auto &rel_vec = rel_map[part_id];

    // We iterate over each object which may be accessed by this partition,
    //   using our rel_vec
    std::for_each(std::begin(rel_vec), std::end(rel_vec),
        [&ssa, &graph, &part_defs, &part_uses, &part_id, &omap,
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
        auto &node = part_graph.getNode<CFG::Node>(node_set.first->second);

        // Set R
        node.setR();

        // Force M for part nodes?
        if (graph.getPart(dug_id) == part_id) {
          node.setM();
        }

        // Denote this CFG node maps to this DUG node
        part_uses[cfg_id].push_back(dug_id);

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
        auto ret = part_defs.emplace(cfg_id, std::vector<DUG::DUGid>({dug_id}));
        assert(ret.second);

        node_to_partition[dug_id].push_back(part_id);
      } else {
        llvm_unreachable("Have non-load/store node?");
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

    // Here we group the partSSA info, indicating which DUG nodes are affected
    //   by this partition
    // We add the computed partiton info into the part for each node
    // NOTE: We'll need to add some PHI nodes
    std::vector<std::tuple<CFG::NodeID, DUG::DUGid, DUG::PartID>> delayed_edges;
    std::for_each(part_ssa.topo_begin(), part_ssa.topo_end(),
        [&graph, &part_ssa, &cfg_node_rep, &cfg_to_node,
            &delayed_edges, &part_uses, &part_defs, &part_id]
        (const CFG::NodeID node_id) {
      // Get the CFGid of this node:
      auto cfg_id_it = cfg_to_node.find(node_id);
      if (cfg_id_it == std::end(cfg_to_node)) {
        auto new_cfg_id = part_ssa.getNode(node_id).extId();
        auto ret = cfg_to_node.emplace(node_id, new_cfg_id);
        assert(ret.second);
        llvm::dbgs() << "Mapping node_id for: " << node_id << " to " <<
            new_cfg_id << "\n";
        cfg_id_it = ret.first;
      }
      auto cfg_id = cfg_id_it->second;
      llvm::dbgs() << "Visiting cfg_id of: " << cfg_id << "\n";

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
        dug_id = st_it->second.front();
        llvm::dbgs() << "  Got st of: " << dug_id << "\n";
        assert(llvm::isa<DUG::StoreNode>(graph.getNode(dug_id)));
      } else if (have_ld) {
        dug_id = ld_it->second.front();
        llvm::dbgs() << "  Got ld of: " << dug_id << "\n";
        llvm::dbgs() << "  ld size is: " << ld_it->second.size() << "\n";
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
      cfg_node_rep[cfg_id] = dug_id;

      // Put an edge from the part's "leader" to its members
      if (have_st) {
        bool first = true;
        auto &st_list = st_it->second;

        for (auto &st_id : st_list) {
          if (first) {
            first = false;
            continue;
          }

          dout << "  --Adding rep-st edge {" << dug_id << " -(" << part_id <<
              ")-> " << st_id << "}\n";
          graph.addEdge(dug_id, st_id, part_id);
        }
      }

      if (have_ld) {
        auto &ld_list = ld_it->second;
        bool first = true;
        bool skip_first = !have_st;
        for (auto &ld_id : ld_list) {
          // Skip the first entry if we have already accounted for it (our rep
          //    is a load)
          if (first && skip_first) {
            first = false;
            continue;
          }

          dout << "  --Adding rep-ld edge {" << dug_id << " -(" << part_id <<
              ")-> " << ld_id << "}\n";
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
          [&graph, &delayed_edges, &cfg_node_rep, &dug_id, &part_id, &part_ssa,
            &cfg_to_node]
          (const CFG::EdgeID pred_edge_id) {
        auto pred_node_id = part_ssa.getEdge(pred_edge_id).src();
        // auto pred_cfg_id = part_ssa.getNode<CFG::Node>(pred_node_id).extId();
        // llvm::dbgs() << "have pred_node_id of: " << pred_node_id << "\n";
        auto pred_cfg_id_it = cfg_to_node.find(pred_node_id);
        // This happens if its a phi node that hasn't been visited yet!
        if (pred_cfg_id_it == std::end(cfg_to_node)) {
          delayed_edges.emplace_back(pred_node_id, dug_id, part_id);
        } else {
          auto pred_cfg_id = pred_cfg_id_it->second;

          // NOTE: if we were not doing a topo order we may have to evaluate the
          //   pred here
          // dout << "Finding cfg_node_rep at: " << pred_cfg_id << "\n";
          auto pred_rep_it = cfg_node_rep.find(pred_cfg_id);
          if (pred_rep_it == std::end(cfg_node_rep)) {
            // Delay our rep resolving until after we've visited all nodes
            dout << "  ||Delaying cfg edge (pred id: " << pred_cfg_id << ") {"
                << "??" << " -(" << part_id << ")-> " << dug_id << "}\n";
            delayed_edges.emplace_back(pred_node_id, dug_id, part_id);
          } else {
            DUG::DUGid &pred_rep_id = pred_rep_it->second;

            dout << "  --Adding cfg edge {" << pred_rep_id << " -(" <<
              part_id << ")-> " << dug_id << "}\n";
            graph.addEdge(pred_rep_id, dug_id, part_id);
          }
        }
      });
    });

    std::vector<std::tuple<CFG::CFGid, DUG::DUGid, DUG::PartID>>
      delayed_dedup_edges;

    std::for_each(std::begin(delayed_edges), std::end(delayed_edges),
        [&graph, &cfg_node_rep, &cfg_to_node, &delayed_dedup_edges]
        (std::tuple<CFG::NodeID, DUG::DUGid, DUG::PartID> &tup) {
      auto pred_cfg_id = cfg_to_node.at(std::get<0>(tup));
      delayed_dedup_edges.emplace_back(pred_cfg_id, std::get<1>(tup),
        std::get<2>(tup));
    });

    std::sort(std::begin(delayed_dedup_edges), std::end(delayed_dedup_edges));
    auto dedup_it = std::unique(std::begin(delayed_dedup_edges),
        std::end(delayed_dedup_edges));
    delayed_dedup_edges.erase(dedup_it, std::end(delayed_dedup_edges));

    std::for_each(std::begin(delayed_dedup_edges),
        std::end(delayed_dedup_edges),
          [&graph, &cfg_node_rep, &cfg_to_node]
          (std::tuple<CFG::CFGid, DUG::DUGid, DUG::PartID> &tup) {
        auto pred_cfg_id = std::get<0>(tup);
        auto pred_rep_it = cfg_node_rep.find(pred_cfg_id);
        assert(pred_rep_it != std::end(cfg_node_rep));

        auto pred_rep_id = pred_rep_it->second;

        dout << "  --Adding delayed-cfg edge {" << pred_rep_id << " -(" <<
            std::get<2>(tup) << ")-> " << std::get<1>(tup) << "}\n";
        graph.addEdge(pred_rep_id, std::get<1>(tup), std::get<2>(tup));
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

