/*
 * Copyright (C) 2015 David Devecsery
 */

// #define SPECSFS_DEBUG
// #define DO_SEG_PRINT

#include <algorithm>
#include <functional>
#include <map>
#include <string>
#include <tuple>
#include <utility>
#include <list>
#include <vector>

#include "include/SpecSFS.h"

#include "include/util.h"
#include "include/SolveHelpers.h"
#include "include/Andersens.h"
#include "include/ObjectMap.h"


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
  } else if (auto pld = dyn_cast<const llvm::LoadInst>(src)) {
    src = pld->getPointerOperand();
    dest = src;
  } else if (auto pst = dyn_cast<const llvm::StoreInst>(src)) {
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
    ObjectMap &omap) {
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
  dout("Running computePartitions\n");


  dout("Doing AE creation loop\n");

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

    ObjectMap::ObjID val_id;
    dout("Creating part_nodes for obj_id " << pr.first << " : " <<
        ValPrint(pr.first) << "\n");;
    if (llvm::isa<DUG::StoreNode>(node)) {
      // val is dest for stores...
      val_id = node.dest();
      dout("  Have store node: " << node.rep() << " : " <<
        ValPrint(node.rep()) << "\n");
      dout("    dest: " << node.dest() << " : " <<
        ValPrint(node.dest()) << "\n");
      dout("    src: " << node.src() << " : " <<
        ValPrint(node.src()) << "\n");
    } else {
      dout("    node_id is: " << node.id() << "\n");
      assert(llvm::isa<DUG::LoadNode>(node) ||
          llvm::isa<DUG::ConstPartNode>(node));

      // val is src for gv and loads
      val_id = node.src();
    }
    /*
    auto val = omap.valueAtID(val_id);
    auto obj_id = omap.getObject(val);
    */
    // We use the value to label which part nodes are associated with which
    //   obj_ids
    auto obj_id = val_id;
    dout("  Adding part_node for obj: " << obj_id << " : " <<
        ValPrint(obj_id) << "->" << node.id() << "\n");;

    part_nodes[obj_id].push_back(node.id());
  });

  // Now, create a grouping of each relevant obj_id for a given DUGid
  std::for_each(part_nodes.cbegin(), part_nodes.cend(),
      [this, &AE, &omap, &dug, &aux]
      (const std::pair<const ObjectMap::ObjID, std::vector<DUG::DUGid>> &pr) {
    auto obj_id = pr.first;

    const llvm::SparseBitVector<> *paux_ptsto;
    // Specially handle our special object ids...
    if (omap.isSpecial(obj_id)) {
      auto aux_obj = special_aux_.at(obj_id);
      paux_ptsto = &aux.getPointsTo(aux_obj);
      dout("Got Special ptsto: " << obj_id << "\n");
    } else {
      // If not special, just get the pointsto
      auto val = omap.valueAtID(obj_id);
      if (val == nullptr) {
        auto &nd = dug.getNode(obj_id);

        val = omap.valueAtID(nd.dest());
      }

      paux_ptsto = &aux.getPointsTo(val);
    }
    auto aux_ptsto = *paux_ptsto;

    if_debug(
      dout("aux ptsto for: " << obj_id << " : " << ValPrint(obj_id)
          << " is:");
      for (auto id : aux_ptsto) {
        dout(" " << id);
      }
      dout("\n"));

    std::for_each(std::begin(aux_ptsto), std::end(aux_ptsto),
        [this, &AE, &obj_id] (uint32_t ptsto_id) {
      auto aux_it = aux_to_obj_.find(ptsto_id);
      dout("  Checking aux_to_obj[" << ptsto_id << "]\n");
      // If I have a value in aux, but not in my object set, ignore it, its an
      //   aux internal node which I've already accounted for
      if (aux_it != std::end(aux_to_obj_)) {
        dout("  aux_to_obj[" << ptsto_id << "] is: " <<
            aux_it->second << "\n");
        auto aux_obj_id = aux_it->second;
        AE[aux_obj_id].set(obj_id.val());
      }
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
      [&AE, &omap, &rev_part_map, &equiv_map, &part_id_generator]
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

    auto field_pr = omap.findObjAliases(pr.first);

    if (field_pr.first) {
      auto &field_vec = field_pr.second;
      std::for_each(std::begin(field_vec), std::end(field_vec),
          [&rev_part_map, &part_id] (ObjectMap::ObjID id) {
        rev_part_map[part_id].emplace_back(id);
      });
    }
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
      // Check to see if this is an internal alias I introduced...
      //    An example of this would be structure fields
      //    Or allocations from indirect pointers
      /*
      auto field_pr = omap.findObjAliases(obj_id);

      // If so, add each field to the part map
      if (field_pr.first) {
        auto &field_vec = field_pr.second;
        std::for_each(std::begin(field_vec), std::end(field_vec),
            [&pr, &part_map] (ObjectMap::ObjID id) {
          part_map[id] = pr.first;
        });
      }
      */

      // Now, just add the obj
      part_map[obj_id] = pr.first;
    });
  });

  if_debug(
    dout("End partitionToNode map is:\n");
    std::for_each(std::begin(rev_part_map), std::end(rev_part_map),
        [] (std::pair<const DUG::PartID, std::vector<ObjectMap::ObjID>> &pr) {
      dout("  Have part_id: " << pr.first << "\n");
      std::for_each(std::begin(pr.second), std::end(pr.second),
          [] (ObjectMap::ObjID obj_id) {
        dout("    obj_id: " << obj_id <<
            " : " << ValPrint(obj_id) << "\n");
      });
    }));

  // We now have our mappings, and we transfer them to the DUG
  dug.setNodeToPartition(std::move(part_map));
  dug.setPartitionToNodes(std::move(rev_part_map));
  dug.setRelevantNodes(std::move(AE));
  dug.setPartNodes(std::move(part_nodes));

  return false;
}


bool SpecSFS::addPartitionsToDUG(DUG &graph, CFG &ssa,
    const ObjectMap &omap) {
  // Map to track which partitions use each DUG node
  std::map<DUG::DUGid, std::vector<DUG::PartID>> node_to_partition;

  SEG ssa_seg;
  {
    PerfTimerPrinter tmr(llvm::dbgs(), "setupssa");
    // Okay, now clear out any r, p, or c info for the nodes in that graph
    ssa_seg = ssa.getSEG().clone<CFG::Node>();
    std::for_each(std::begin(ssa_seg), std::end(ssa_seg),
        [] (CFG::ControlFlowGraph::node_iter_type &pnode) {
      auto &node = cast<CFG::Node>(*pnode);

      node.clearM();
      node.clearR();
      node.clearC();

      node.clearDefs();
      node.clearUses();

      // SEG assumes succs are clear when it starts...
      node.succs().clear();
    });
  }

  // For each partition, calculate the SSA of any nodes in that partiton
  {
    PerfTimerPrinter tmr(llvm::dbgs(), "calcParts");
    std::for_each(graph.part_cbegin(), graph.part_cend(),
        [this, &graph, &ssa, &ssa_seg, &node_to_partition, &omap]
        (const std::pair<const DUG::PartID, std::vector<ObjectMap::ObjID>> &pr) {  // NOLINT
      std::map<CFG::CFGid, DUG::DUGid> cfg_node_rep;

      // Create a clone of the ControlFlowGraph for this partition's ssa
      CFG::ControlFlowGraph part_graph =
        ssa_seg.clone<CFG::Node>();

      // Now calculate and fill in the info for each object
      //   in this partition
      const auto &part_id = pr.first;

      // We choose one arbitrary representative node from the AE set
      // Its properties hold for all AE nodes, by the nature of AE
      auto obj_id = pr.second.front();

      auto &rel_map = graph.getRelevantNodes();
      dout("Getting rel_map for: " << obj_id << "\n");
      auto &rel_bitmap = rel_map[obj_id];

      int num_loads = 0;
      int num_stores = 0;

      std::list<DUG::DUGid> part_load;
      std::list<DUG::DUGid> part_store;

      // We iterate over each object which may be accessed by this partition,
      //   using our rel_vec
      std::for_each(std::begin(rel_bitmap), std::end(rel_bitmap),
          [&ssa, &graph, &part_id, &omap, &part_load, &num_loads,
              &part_store, &num_stores, &part_graph,
              &node_to_partition]
          (uint32_t obj_id_val) {
        ObjectMap::ObjID obj_id = ObjectMap::ObjID(obj_id_val);

        auto &dug_ids = graph.getPartNodes(obj_id);

        for (auto dug_id : dug_ids) {
          dout("part: " << part_id <<
              ": Getting obj_id: " << obj_id << " for dug_id: " << dug_id <<
              "\n");
          dout("  that's value: " << *omap.valueAtID(obj_id) << "\n");

          auto &node = graph.getNode(dug_id);

          // Okay, now that we have the CFGid, update its info:
          // If this is a load:
          if (llvm::isa<DUG::LoadNode>(node) ||
              llvm::isa<DUG::ConstPartNode>(node)) {
            auto cfg_id = ssa.getCFGid(node.rep());

            // Ooops, I aliased a variable... shame on me
            auto &node = part_graph.getNode<CFG::Node>(cfg_id);

            // Set R
            node.setR();

            // Denote this CFG node maps to this DUG node
            // FIXME:
            // MAHHHH this is the wrong type of ID... so I'm forcing it...
            //   because I'm ticked off!
            dout("Adding use to node: " << node.id() << "\n");
            node.addUse(ObjectMap::ObjID(dug_id.val()));

            // Denote that this DUG node is part of this partition
            node_to_partition[dug_id].push_back(part_id);

            part_load.push_back(dug_id);
            num_loads++;
          // If its a store:
          } else if (llvm::isa<DUG::StoreNode>(node)) {
            // Get the cfg_id of this node
            auto cfg_id = ssa.getCFGid(node.rep());

            // Get the node in the CFG
            auto &node = part_graph.getNode<CFG::Node>(cfg_id);

            // Set M and R
            node.setM();
            node.setR();

            // Possibly set C
            if (ssa.isStrong(obj_id)) {
              node.setC();
            }

            // Denote this CFGid references this DUG entry
            // FIXME:
            // MAHHHH this is the wrong type of ID... so I'm forcing it...
            //   because I'm ticked off!
            dout("Adding def to node: " << node.id() << "\n");
            node.addDef(ObjectMap::ObjID(dug_id.val()));

            node_to_partition[dug_id].push_back(part_id);

            part_store.push_back(dug_id);
            num_stores++;
          }  else {
            llvm_unreachable("Unrecognized node type!");
          }
        }
      });

      // If this is a simple graph, I can manually add dependencies
      //   (no need to run ramalingams/compute SSA)
      if (num_loads <= 1 || num_stores <= 1) {
        dout("Have simple CFG, skipping SSA calc\n");
        // This graph has only one store:
        if (num_stores == 1 && num_loads > 0) {
          dout("Have 1 load, adding edges that way\n");
          auto st_id = part_store.front();

          std::for_each(std::begin(part_load), std::end(part_load),
              [&graph, &part_id, &st_id] (DUG::DUGid load_id) {
            graph.addEdge(st_id, load_id, part_id);
          });
        // This graph has only 1 load
        } else if (num_stores >= 0 && num_loads == 1) {
          dout("Have 1 load, adding edges that way\n");
          auto load_id = part_load.front();

          std::for_each(std::begin(part_store), std::end(part_store),
              [&graph, &part_id, &load_id] (DUG::DUGid st_id) {
            graph.addEdge(st_id, load_id, part_id);
          });
        }
        // NOTE: It's possible that we fell through here (if we have 0
        // loads or 0 stores).  In that case, I don't need to add any edges...

      // This isn't a simple graph, I need to calculate full SSA
      } else {
#ifdef DO_SEG_PRINT
        {
          std::string part_file("part_graph");
          part_file += std::to_string(part_id.val());
          part_file += ".dot";
          part_graph.printDotFile(part_file, *g_omap);
        }
#endif
        // Now, calculate ssa form for this graph:
        computeSSA(part_graph);

        auto &part_ssa = part_graph;

        /* -- ddevec - Dot file debugging... I'm disabling due to the insane number
         * of files/time it takes
        */
#ifdef DO_SEG_PRINT
        {
          std::string part_file("part_ssa");
          part_file += std::to_string(part_id.val());
          part_file += ".dot";
          part_ssa.printDotFile(part_file, *g_omap);
        }
#endif

        // Here we group the partSSA info, indicating which DUG nodes
        //   are affected by this partition
        // We add the computed partiton info into the part for each node
        // NOTE: We'll need to add some PHI nodes
        std::vector<std::tuple<CFG::NodeID, DUG::DUGid, DUG::PartID>>
          delayed_edges;
        std::for_each(part_ssa.topo_begin(), part_ssa.topo_end(),
            [&graph, &part_ssa, &cfg_node_rep,
                &delayed_edges, &part_id, &node_to_partition]
            (const CFG::NodeID node_id) {
          auto &ssa_node = part_ssa.getNode<CFG::Node>(node_id);

          auto cfg_id = ssa_node.id();
          dout("Visiting cfg_id of: " << cfg_id << "\n");

          // The DUG rep of this id
          auto dug_id = DUG::DUGid();

          // If this node has a use, it is a ld node
          auto ld_it = ssa_node.uses_begin();
          // There is only one if its a store (def)
          auto st_it = ssa_node.defs_begin();

          bool have_ld = ld_it != ssa_node.uses_end();
          bool have_st = st_it != ssa_node.defs_end();

          // Elect a "leader" id for each basic block
          if (have_st) {
            dug_id = DUG::DUGid(st_it->val());
            dout("  Got st of: " << dug_id << "\n");
            assert(llvm::isa<DUG::StoreNode>(graph.getNode(dug_id)));
          } else if (have_ld) {
            dug_id = DUG::DUGid(ld_it->val());
            dout("  Got ld of: " << dug_id << "\n");
            dout("  ld size is: " <<
              std::distance(ssa_node.uses_begin(), ssa_node.uses_end())
              << "\n");
            assert(llvm::isa<DUG::LoadNode>(graph.getNode(dug_id)) ||
                   llvm::isa<DUG::ConstPartNode>(graph.getNode(dug_id)));
          // There may also be none (in this case its an phi node)
          } else {
            dug_id = graph.addPhi();
            // Add the phi node to the partition
            node_to_partition[dug_id].push_back(part_id);
            dout("  Got phi of: " << dug_id << "\n");
            assert(llvm::isa<DUG::PhiNode>(graph.getNode(dug_id)));
          }

          // Update our cfg_node_rep map, so we can fill in preds later
          dout("  Setting cfg_node_rep for " << cfg_id << " to: "
              << dug_id << "\n");
          assert(cfg_node_rep.find(cfg_id) == std::end(cfg_node_rep));
          cfg_node_rep.emplace(cfg_id, dug_id);

          // Put an edge from the basic block's "leader" to its members
          if (have_st) {
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

              // Since global nodes are separated now, this should be
              // impossible...
              assert(0);

              // When any store is updated, all stores must be updated.... meh
              dout("  --Adding rep-st edge {" << dug_id << " -(" <<
                  part_id << ")-> " << st_id << "}\n");
              graph.addEdge(dug_id, st_id, part_id);
            });
          }

          if (have_ld) {
            bool first = true;
            bool skip_first = !have_st;

            std::for_each(ssa_node.uses_begin(), ssa_node.uses_end(),
                [&graph, &dug_id, &part_id, &first, &skip_first]
                (ObjectMap::ObjID obj_id) {
              // FIXME: This is a really hacky thing...
              DUG::DUGid ld_id = DUG::DUGid(obj_id.val());
              // Skip the first entry if we have already accounted for it
              //   (our rep is a load)
              if (first && skip_first) {
                first = false;
                return;
              }

              dout("  --Adding rep-ld edge {" << dug_id << " -(" <<
                  part_id << ")-> " << ld_id << "}\n");
              graph.addEdge(dug_id, ld_id, part_id);
            });
          }

          /*
          auto node_set = part_ssa.getNodes(cfg_cfg_id);
          assert(std::distance(node_set.first, node_set.second) == 1);
          */
          auto &node = part_ssa.getNode<CFG::Node>(node_id);
          const auto &preds = node.preds();

          // Assert says if this node is a phi node, it must have at least
          //   one pred
          // NOTE: Ramalingam's algorithm can create a phi node with no
          //   predecessors!
          /*
          assert(
              // Is not a phi
              !(!have_ld && !have_st) ||
              // If it is a phi, it must have at least one pred
              !preds.empty());
          */

          // Put an edge from each pred in G to the part leader
          std::for_each(std::begin(preds), std::end(preds),
              [&graph, &delayed_edges, &cfg_node_rep, &dug_id,
                &part_id, &part_ssa]
              (const CFG::NodeID pred_id) {
            auto pred_node_id = pred_id;

            auto pred_cfg_id = part_ssa.getNode<CFG::Node>(pred_node_id).id();
            dout("    have pred_node_id of: " << pred_cfg_id << "\n");

            // NOTE: if we were not doing a topo order we may have to
            //   evaluate the pred here
            // dout("Finding cfg_node_rep at: " << pred_cfg_id << "\n");
            auto pred_rep_it = cfg_node_rep.find(pred_cfg_id);
            if (pred_rep_it == std::end(cfg_node_rep)) {
              // Delay our rep resolving until after we've visited all nodes
              dout("    ||Delaying cfg edge (pred id: " << pred_cfg_id
                  << ") {" << "??" << " -(" << part_id << ")-> " << dug_id <<
                  "}\n");
              delayed_edges.emplace_back(pred_node_id, dug_id, part_id);
            } else {
              DUG::DUGid &pred_rep_id = pred_rep_it->second;

              dout("    --Adding cfg edge {" << pred_rep_id << " -(" <<
                part_id << ")-> " << dug_id << "}\n");
              graph.addEdge(pred_rep_id, dug_id, part_id);
            }
          });
        });

        std::vector<std::tuple<CFG::CFGid, DUG::DUGid, DUG::PartID>>
          delayed_dedup_edges;

        std::for_each(std::begin(delayed_edges), std::end(delayed_edges),
            [&graph, &part_ssa, &cfg_node_rep, &delayed_dedup_edges]
            (std::tuple<CFG::NodeID, DUG::DUGid, DUG::PartID> &tup) {
          auto pred_cfg_id = part_ssa.getNode(std::get<0>(tup)).id();
          delayed_dedup_edges.emplace_back(pred_cfg_id, std::get<1>(tup),
            std::get<2>(tup));
        });

        std::sort(std::begin(delayed_dedup_edges),
            std::end(delayed_dedup_edges));
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

            dout("  --Adding delayed-cfg edge {" << pred_rep_id <<
                " -(" << std::get<2>(tup) << ")-> " << std::get<1>(tup)
                << "}\n");
            graph.addEdge(pred_rep_id, std::get<1>(tup), std::get<2>(tup));
        });
      }
    });
  }

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
  dout("Setting up partGraph for each node!\n");
  {
    PerfTimer inner_loop;
    PerfTimer part_node_setup;
    PerfTimerPrinter tmr(llvm::dbgs(), "Setup nodes");
    std::for_each(node_to_partition.cbegin(), node_to_partition.cend(),
        [&graph, &omap, &inner_loop, &part_node_setup]
        (const std::pair<const DUG::DUGid, std::vector<DUG::PartID>> &pr) {
      auto &part_node = cast<DUG::PartNode>(graph.getNode(pr.first));
      auto &parts = pr.second;
      std::vector<ObjectMap::ObjID> vars;

      dout("  Looking at ID: " << part_node.id() << "\n");

      {
        PerfTimerTick tick(inner_loop);
        std::for_each(std::begin(parts), std::end(parts),
            [&graph, &vars, &omap] (const DUG::PartID &part_id) {
          auto &objs = graph.getObjs(part_id);
          dout("    Checking part_id: " << part_id << "\n");
          std::for_each(std::begin(objs), std::end(objs),
              [&graph, &vars, &omap] (ObjectMap::ObjID &obj_id) {
            // We're going to try converting these to objects instead
            //   of values...
            // Also adding pointers for aliased objects
            auto field_pr = omap.findObjAliases(obj_id);
            if (field_pr.first) {
              auto &field_vec = field_pr.second;
              vars.insert(std::end(vars), std::begin(field_vec),
                std::end(field_vec));
            }

            vars.emplace_back(obj_id);
          });
        });
      }

      /*
      if_debug(
        dout("  Setting up vars as:");
        for (auto &obj : vars) {
          dout(" " << obj);
        }
        dout("\n"));
      */
      /*
      llvm::dbgs() << "  (" << pr.first << ")Setting up vars as:";
      for (auto &obj : vars) {
        llvm::dbgs() << " " << obj;
      }
      llvm::dbgs() << "\n";
      */

      std::sort(std::begin(vars), std::end(vars));
      auto it = std::unique(std::begin(vars), std::end(vars));
      vars.erase(it, std::end(vars));

      {
        PerfTimerTick tick(part_node_setup);
        part_node.setupPartGraph(vars);
      }
    });


    llvm::dbgs() << "inner_loop: timer duration: " <<
      inner_loop.totalElapsed().count() <<  "\n";
    llvm::dbgs() << "part_node_setup: timer duration: "
      << part_node_setup.totalElapsed().count() <<  "\n";
  }

  return false;
}

