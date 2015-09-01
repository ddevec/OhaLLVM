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
#include "include/SolveHelpers.h"
#include "include/Andersens.h"
#include "include/ObjectMap.h"


#define SPECSFS_DEBUG
#include "include/Debug.h"

#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

// Anon namespace...
namespace {
__attribute__((unused))
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

  // Converting from aux_id to obj_ids
  std::map<int, ObjectMap::ObjID> aux_to_obj;
  // For each pointer value we care about:
  llvm::dbgs() << "Filling aux_to_obj:\n";
  auto &aux_val_nodes = aux.getObjectMap();

  aux_to_obj.emplace(Andersens::NullPtr, ObjectMap::NullValue);
  aux_to_obj.emplace(Andersens::NullObject, ObjectMap::NullObjectValue);
  aux_to_obj.emplace(aux.IntNode, ObjectMap::IntValue);
  aux_to_obj.emplace(Andersens::UniversalSet, ObjectMap::UniversalValue);
  aux_to_obj.emplace(aux.PthreadSpecificNode, ObjectMap::PthreadSpecificValue);

  std::for_each(std::begin(aux_val_nodes), std::end(aux_val_nodes),
      [&aux, &aux_to_obj, &omap, &dug]
      (const std::pair<const llvm::Value *, uint32_t> &pr) {
    auto obj_id = omap.getValue(pr.first);
    auto aux_val_id = pr.second;

    llvm::dbgs() << "  " << aux_val_id << "->" << obj_id <<
      "\n";
    auto ret = aux_to_obj.emplace(aux_val_id, obj_id);
    assert(ret.second);
  });


  llvm::dbgs() << "Doing AE creation loop\n";

  // This map holds the conservative "Access Equivalence"
  //   sets for each pointer analyzed
  std::map<DUG::ObjID, Bitmap> AE;
  std::map<ObjectMap::ObjID, std::vector<DUG::DUGid>> part_nodes;

  // Group nodes based on relevant obj_id
  std::for_each(cfg.obj_to_cfg_begin(), cfg.obj_to_cfg_end(),
      [&aux, &omap, &dug, &part_nodes]
      (const std::pair<const ObjectMap::ObjID, CFG::CFGid> &pr) {
    // Get info about this node
    auto &node = dug.getNode(pr.first);

    ObjectMap::ObjID val;
    /*
    llvm::dbgs() << "Creating part_nodes for obj_id " << pr.first << " : " <<
        ValPrint(pr.first) << "\n";;
    */
    if (llvm::isa<DUG::StoreNode>(node)) {
      // val is dest for stores...
      val = node.dest();
      /*
      llvm::dbgs() << "  Have store node: " << node.rep() << " : " <<
        ValPrint(node.rep()) << "\n";;
      llvm::dbgs() << "    store dest: " << node.dest() << " : " <<
        ValPrint(node.dest()) << "\n";;
      llvm::dbgs() << "    store src: " << node.src() << " : " <<
        ValPrint(node.src()) << "\n";;
      */
    } else {
      assert(llvm::isa<DUG::LoadNode>(node) ||
        llvm::isa<DUG::GlobalInitNode>(node));
      // val is src for gv and loads
      val = node.src();
    }

    llvm::dbgs() << "  Adding part_node for obj: " << val << " : " <<
        ValPrint(val) << "->" << node.id() << "\n";;

    part_nodes[val].push_back(node.id());
  });

  // Now, create a grouping of each relevant obj_id for a given DUGid
  std::for_each(part_nodes.cbegin(), part_nodes.cend(),
      [&AE, &omap, &dug, &aux_to_obj, &aux]
      (const std::pair<const ObjectMap::ObjID, std::vector<DUG::DUGid>> &pr) {
    auto obj_id = pr.first;

    // Actually, should be: for each pts_id in aux(omap[obj_id])... ugh
    auto val = omap.valueAtID(obj_id);
    if (val == nullptr) {
      auto &nd = dug.getNode(obj_id);

      val = omap.valueAtID(nd.dest());
    }
    auto aux_ptsto = aux.getPointsTo(val);
    llvm::dbgs() << "aux ptsto for: " << obj_id << " : " << ValPrint(obj_id)
        << " is:";
    for (auto id : aux_ptsto) {
      llvm::dbgs() << " " << id;
    }
    llvm::dbgs() << "\n";
    std::for_each(std::begin(aux_ptsto), std::end(aux_ptsto),
        [&AE, &obj_id, &aux_to_obj] (uint32_t ptsto_id) {
      auto aux_obj_id = aux_to_obj.at(ptsto_id);
      AE[aux_obj_id].set(obj_id.val());
    });
  });

  // Okay, I now have a populated AE, fill out our parts
  // Create a partition ID generatior
  IDGenerator<DUG::PartID> part_id_generator;

  // Create a map to identify when I have a new part
  std::map<Bitmap, DUG::PartID, BitmapLT> equiv_map;

  std::map<DUG::PartID, std::vector<ObjectMap::ObjID>> rev_part_map;

  // Now, for each relevant DUGid, create an AE mapping
  std::for_each(AE.cbegin(), AE.cend(),
      [&AE, &rev_part_map, &equiv_map, &part_id_generator]
      (const std::pair<const ObjectMap::ObjID, Bitmap> &pr) {
    auto equiv_it = equiv_map.find(pr.second);

    // I haven't encountered this mapping yet, add a new one
    if (equiv_it == std::end(equiv_map)) {
      auto equiv_ret = equiv_map.emplace(pr.second,
          part_id_generator.next());
      assert(equiv_ret.second);

      equiv_it = equiv_ret.first;
    }

    auto part_id = equiv_it->second;

    // Set the object for this part into pr.first
    rev_part_map[part_id].emplace_back(pr.first);
  });

  // Create the node to partition mapping
  // To do this, we basically just reverse the part to node mapping
  // NOTE: We also deduplicate the node to part mapping here -- Is this needed?
  std::map<ObjectMap::ObjID, DUG::PartID> part_map;
  std::for_each(std::begin(rev_part_map), std::end(rev_part_map),
      [&part_map, &omap]
      (std::pair<const DUG::PartID, std::vector<ObjectMap::ObjID>> &pr) {
    // Okay... here we go
    // First deduplicate rev_part_map:
    std::sort(std::begin(pr.second), std::end(pr.second));
    auto it = std::unique(std::begin(pr.second), std::end(pr.second));
    pr.second.erase(it, std::end(pr.second));

    // Now, create mapping
    std::for_each(std::begin(pr.second), std::end(pr.second),
        [&pr, &part_map, &omap]
        (ObjectMap::ObjID &obj_id) {
      part_map[obj_id] = pr.first;
    });
  });

  llvm::dbgs() << "End partitionToNode map is:\n";
  std::for_each(std::begin(rev_part_map), std::end(rev_part_map),
      [] (std::pair<const DUG::PartID, std::vector<ObjectMap::ObjID>> &pr) {
    llvm::dbgs() << "  Have part_id: " << pr.first << "\n";
    std::for_each(std::begin(pr.second), std::end(pr.second),
        [] (ObjectMap::ObjID obj_id) {
      llvm::dbgs() << "    obj_id: " << obj_id <<
          " : " << ValPrint(obj_id) << "\n";
    });
  });

  // We now have our mappings, and we transfer them to the DUG
  dug.setNodeToPartition(std::move(part_map));
  dug.setPartitionToNodes(std::move(rev_part_map));
  dug.setRelevantNodes(std::move(AE));
  dug.setPartNodes(std::move(part_nodes));

  return false;
}


bool SpecSFS::addPartitionsToDUG(DUG &graph, const CFG &ssa,
    const ObjectMap &omap) {
  // Map to track which partitions use each DUG node
  std::map<DUG::DUGid, std::vector<DUG::PartID>> node_to_partition;

  // For each partition, calculate the SSA of any nodes in that partiton
  std::for_each(graph.part_cbegin(), graph.part_cend(),
      [this, &graph, &ssa, &node_to_partition, &omap]
      (const std::pair<const DUG::PartID, std::vector<ObjectMap::ObjID>> &pr) {
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

    // We choose one arbitrary representative node from the AE set
    // Its properties hold for all AE nodes, by the nature of AE
    auto obj_id = pr.second.front();

    auto &rel_map = graph.getRelevantNodes();
    llvm::dbgs() << "Getting rel_map for: " << obj_id << "\n";
    auto &rel_bitmap = rel_map[obj_id];

    // We iterate over each object which may be accessed by this partition,
    //   using our rel_vec
    std::for_each(std::begin(rel_bitmap), std::end(rel_bitmap),
        [&ssa, &graph, &part_id, &omap,
            &part_graph, &node_to_partition]
        (uint32_t obj_id_val) {
      ObjectMap::ObjID obj_id = ObjectMap::ObjID(obj_id_val);

      auto &dug_ids = graph.getPartNodes(obj_id);

      for (auto dug_id : dug_ids) {
        llvm::dbgs() << "part: " << part_id <<
            ": Getting obj_id: " << obj_id << " for dug_id: " << dug_id << "\n";
        llvm::dbgs() << "  that's value: " << *omap.valueAtID(obj_id) << "\n";

        auto &node = graph.getNode(dug_id);

        // Okay, now that we have the CFGid, update its info:
        // If this is a load:
        if (llvm::isa<DUG::LoadNode>(node)) {
          auto cfg_id = ssa.getCFGid(node.extId());
          auto node_set = part_graph.getNodes(cfg_id);
          assert(std::distance(node_set.first, node_set.second) == 1);
          // Ooops, I aliased a variable... shame on me
          // auto &ld_node = node;
          auto &node = part_graph.getNode<CFG::Node>(node_set.first->second);

          // Set R
          node.setR();

          // Force M for part nodes?
          /*
          if (graph.getPart(ld_node.src()) == part_id) {
            node.setM();
          }
          */

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
          auto cfg_id = ssa.getCFGid(node.extId());

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
          // FIXME:
          // Similar to other FIXME's above, its hacky and bad, etc etc, fix
          //   when I have time
          cfg_node.addGlobalInit(ObjectMap::ObjID(dug_id.val()));
          node_to_partition[dug_id].push_back(part_id);
        } else {
          llvm_unreachable("Unrecognized node type!");
        }
      }
    });

    // Now, calculate ssa form for this graph:
    auto part_ssa = computeSSA(part_graph);

    part_ssa.printDotFile("part_ssa.dot", *g_omap);

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
          [&graph, &vars] (ObjectMap::ObjID &obj_id) {
        llvm::dbgs() << "      Adding var: " << obj_id << "\n";
        vars.emplace_back(obj_id);
      });
    });

    part_node.setupPartGraph(vars);
  });

  return false;
}

