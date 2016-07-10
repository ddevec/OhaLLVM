/*
 * Copyright (C) 2016 David Devecsery
 */

// #define SPECANDERS_DEBUG

#ifdef SPECANDERS_DEBUG
#  define adout(...) llvm::dbgs() << __VA_ARGS__
#else
#  define adout(...)
#endif

#include <algorithm>
#include <limits>
#include <map>
#include <set>
#include <stack>
#include <utility>
#include <vector>

#include "include/AndersGraph.h"
#include "include/Debug.h"
#include "include/SpecAnders.h"

static llvm::cl::opt<int32_t> //  NOLINT
  solve_debug_id("anders-solve-id", llvm::cl::init(-1),
      llvm::cl::value_desc("int"),
      llvm::cl::desc("Specifies IDs to trace in the anders-solve process"));

// Number of edges/number of processed nodes before we allow LCD to run
#define LCD_SIZE 600
#define LCD_PERIOD std::numeric_limits<int32_t>::max()

static size_t lcd_merge_count = 0;

typedef AndersGraph::Id Id;

// SCC Helpers (For anders) {{{
class RunNuutila {
 public:
  static const int32_t IndexInvalid = -1;

  RunNuutila(AndersGraph &g, const std::unordered_set<Id> &nodes,
      Worklist<AndersGraph::Id> &wl, const std::vector<uint32_t> &priority) :
      graph_(g), wl_(wl), priority_(priority) {
    // For each candidate node, visit it if it hasn't been visited, and compute
    //   SCCs, as dicated by Nuutila's Tarjan variant
    nodeData_.resize(graph_.size());
    // llvm::dbgs() << "START NUUTILA\n";
    for (auto pnode_id : nodes) {
      auto pnode = &g.getNode(pnode_id);
      // llvm::dbgs() << "  ITER NUUTILA: " << nodeStack_.size() <<  "\n";
      auto &node_data = getData(pnode->id());
      if (g.isRep(*pnode) && node_data.root == IndexInvalid) {
        visit2(pnode->id());
      }
    }
    // llvm::dbgs() << "END NUUTILA\n";

    assert(nodeStack_.empty());
  }

 private:
  struct TarjanData {
    int32_t root = IndexInvalid;
  };

  struct TarjanData &getData(Id id) {
    assert(id != Id::invalid());
    assert(id.val() >= 0);
    assert(static_cast<size_t>(id.val()) < nodeData_.size());
    return nodeData_.at(id.val());
  }

  struct TarjanData &getRepData(Id id) {
    return getData(graph_.getRep(id));
  }

  void visit2(Id node_id) {
    assert(merged_.find(node_id) == std::end(merged_));
    assert(graph_.isRep(node_id));
    auto &node_data = getRepData(node_id);

    /*
    llvm::dbgs() << "Visit: " << node_id << ": dfs = " << nextIndex_ << "\n";
    */
    node_data.root = nextIndex_;
    auto dfs_idx = nextIndex_;
    nextIndex_++;

    auto &start_node = graph_.getNode(node_id);
    for (auto succ_val : start_node.copySuccs()) {
      auto succ_id = Id(succ_val);

      auto dest_id = graph_.getRep(succ_id);
      auto dest_data = &getRepData(dest_id);

      // FIXME: Edge cleanup here?

      // Ignore merged successors
      if (merged_.find(dest_id) == std::end(merged_)) {
        /*
        llvm::dbgs() << "      " << node_id << " succ: " << dest_id << "\n";
        */
        if (dest_data->root == IndexInvalid) {
          visit2(graph_.getRep(dest_id));

          // Need to get new node_data, as we have have merged it in the prior
          //   loop
          dest_id = graph_.getRep(dest_id);
          dest_data = &getRepData(dest_id);
        }

        if (dest_data->root < node_data.root) {
          /*
          llvm::dbgs() << "  node < dest: " << node_id
            << " (" << node_data.root << ") <= " << dest_id <<
            " (" << dest_data->root << ")\n";
          */
          node_data.root = dest_data->root;
        }
      }
    }

    // FIXME: Finish edge cleanup here?
    assert(graph_.isRep(node_id));

    /*
    llvm::dbgs() << "    " << node_id << " root: " << node_data.root <<
      ", dfs: " << dfs_idx << "\n";
    */
    if (node_data.root == dfs_idx) {
      bool ch = false;

      while (!nodeStack_.empty()) {
        auto next_id = nodeStack_.top();
        auto &next_data = getData(next_id);
        if (next_data.root < dfs_idx) {
          break;
        }
        // llvm::dbgs() << "  --Stack popping: " << next_id << "\n";
        nodeStack_.pop();

        auto rep_next_id = graph_.getRep(next_id);
        auto &node_rep = graph_.getNode(node_id);

        // If we weren't already merged (HCD can cause this)
        if (rep_next_id != node_rep.id()) {
          lcd_merge_count++;
          auto &nd = graph_.getNode(rep_next_id);
          /*
          if (node_id == ObjectMap::NullValue ||
              nd.id() == ObjectMap::NullValue) {
            llvm::dbgs() << "Nuutilia merge null: " << node_id << " : " <<
              nd.id() << "\n";
          }
          */
          graph_.merge(node_rep, nd);
        }

        ch = true;
      }

      auto node_rep_id = graph_.getRep(node_id);
      // llvm::dbgs() << "  ~~merged_.insert(" << node_id << ")\n";
      merged_.insert(node_rep_id);

      if (ch) {
        if_debug_enabled(auto &node = graph_.getNode(node_rep_id));
        assert(node.id() == node_rep_id);
        wl_.push(node_rep_id, priority_[static_cast<size_t>(node_rep_id)]);
      }
    } else {
      // llvm::dbgs() << "  ++Stack pushing: " << node_id << "\n";
      assert(graph_.isRep(node_id));
      nodeStack_.push(node_id);
    }
  }

  int32_t nextIndex_ = 1;
  std::stack<Id> nodeStack_;
  std::vector<TarjanData> nodeData_;
  std::set<Id> merged_;

  AndersGraph &graph_;
  Worklist<AndersGraph::Id> &wl_;
  const std::vector<uint32_t> &priority_;
};
//}}}

// Anders Solve {{{
bool SpecAnders::solve() {
  // We're initially given a graph of nodes, with constraints representing the
  //   information flow relations within the nodes.
  // Create a worklist
  // Also, create the priority list for the worklist
  std::vector<uint32_t> priority;
  Worklist<AndersGraph::Id> work;

  logout("SOLVE\n");

  // Populate the worklist with any node with a non-empty ptsto set
  adout("init solve:\n");
  for (auto &node : graph_) {
    if (!node.ptsto().empty()) {
      adout("  " << node.id() << "\n");
      work.push(node.id(), 0);
    }
  }

  priority.assign(graph_.size(), 0);

  int32_t vtime = 1;
  uint32_t prio = 0;

  size_t hcd_merge_count = 0;
  size_t lcd_check_count = 0;
  size_t hcd_merge_last = 0;
  size_t lcd_merge_last = 0;
  size_t lcd_check_last = 0;

  int32_t lcd_last_time = 1;
  struct lcd_edge_hash {
    size_t operator()(const std::pair<Id, Id>
        &pr) const {
      size_t ret = Id::hasher()(pr.first);
      ret <<= 1;
      ret ^= Id::hasher()(pr.second);
      return ret;
    }
  };
  std::unordered_set<std::pair<Id, Id>,
    lcd_edge_hash> lcd_edges;
  std::unordered_set<Id> lcd_nodes;
  // While the worklist has work
  // Pop the next node from the worklist

  while (!work.empty()) {
    auto id = work.pop(prio);
    auto pnd = &graph_.getNode(id);
    // Don't process the node if we've processed it this round
    if (prio < priority[pnd->id().val()]) {
      continue;
    }

    if (!graph_.isRep(*pnd)) {
      continue;
    }

    if (lcd_merge_last + 1000 <= lcd_merge_count) {
      llvm::dbgs() << "LCD Merge Count: " << lcd_merge_count << "\n";
      lcd_merge_last = lcd_merge_count;
    }

    if (lcd_check_last + 1000 <= lcd_check_count) {
      llvm::dbgs() << "LCD check count: " << lcd_check_count << "\n";
      lcd_check_last = lcd_check_count;
    }

    if (hcd_merge_last + 1000 <= hcd_merge_count) {
      llvm::dbgs() << "HCD Merge Count: " << hcd_merge_count << "\n";
      hcd_merge_last = hcd_merge_count;
    }

    priority[pnd->id().val()] = vtime;
    vtime++;

    // If we're near the point of infinite loop:
    /*
    if (lcd_check_count > 5000) {
      anders_do_debug = true;
    }
    */

    // If this node is part of HCD:
    /*
    auto hcd_itr = hcdPairs_.find(pnd->id());
    if (hcd_itr != std::end(hcdPairs_)) {
      // For each ptsto in this node:
      bool did_merge = false;
      for (auto dest_id : pnd->ptsto()) {
        // Collapse (pointed-to-node, rep)
        // Add rep to worklist
        auto &dest_node = graph_.getNode(dest_id);
        auto &rep_node = graph_.getNode(hcd_itr->second);

        // Don't merge w/ self, or with the int value or null value
        if (dest_node.id() != rep_node.id() &&
            dest_node.id() != ValueMap::IntValue &&
            rep_node.id() != ValueMap::NullValue &&
            dest_node.id() != ValueMap::NullValue) {
          graph_.merge(rep_node, dest_node);
          did_merge = true;

          hcd_merge_count++;
        }
      }

      if (did_merge) {
        auto &rep_node = graph_.getNode(hcd_itr->second);
        work.push(rep_node.id(), priority[rep_node.id().val()]);
      }

      // The merge may have caused us to no longer be a rep, in which case, we
      //   shouldn't analyze this node any further
      if (!graph_.isRep(*pnd)) {
        continue;
      }
    }
    */

    adout("Node: " << pnd->id() << "\n");

    // llvm::dbgs() << "Processing node: " << pnd->id() << "\n";
    // For each constraint in this node
    // Note: getUpdateSet also resets the update set
    auto update_set = pnd->getUpdateSet();
    if (!update_set.empty()) {
      auto &cons_list = pnd->constraints();

      // This is only safe because I guarantee that once a cons goes into the
      // set I will never change its index
      auto cons_eq = [this, &cons_list] (size_t lhs_idx, size_t rhs_idx) {
        auto &plhs = cons_list[lhs_idx];
        auto &prhs = cons_list[rhs_idx];

        auto lhs_src = graph_.getNode(plhs.src()).id();
        auto rhs_src = graph_.getNode(prhs.src()).id();

        auto lhs_dest = plhs.dest();
        if (lhs_dest != AndersCons::Id::invalid()) {
          lhs_dest = graph_.getNode(lhs_dest).id();
        }

        auto rhs_dest = prhs.dest();
        if (rhs_dest != AndersCons::Id::invalid()) {
          rhs_dest = graph_.getNode(rhs_dest).id();
        }

        auto lhs_offs = plhs.offs();
        auto rhs_offs = prhs.offs();

        return plhs.type() == prhs.type() && lhs_src == rhs_src &&
          lhs_dest == rhs_dest && lhs_offs == rhs_offs;
      };

      auto cons_hash = [this, &cons_list] (size_t idx) {
        assert(idx < cons_list.size());

        auto &pcons = cons_list[idx];

        assert(pcons.src() != AndersCons::Id::invalid());
        auto src = graph_.getNode(pcons.src()).id();

        // Invalid can happen for indirect constraints
        auto dest = pcons.dest();
        if (dest != AndersCons::Id::invalid()) {
          dest = graph_.getNode(dest).id();
        }
        // llvm::dbgs() << "  dest: " << dest << "\n";
        auto kind = pcons.type();
        auto offs = pcons.offs();

        auto ret = AndersCons::Id::hasher()(src);
        ret <<= 1;
        ret ^= AndersCons::Id::hasher()(dest);
        ret <<= 1;
        ret ^= std::hash<int32_t>()(offs);
        ret <<= 1;
        ret ^= std::hash<int32_t>()(static_cast<int32_t>(kind));

        return ret;
      };
      std::unordered_set<size_t, decltype(cons_hash), decltype(cons_eq)>
        cons_set(cons_list.size() * 2 , cons_hash, cons_eq);

      for (size_t idx = 0; idx < cons_list.size();) {
        auto &cons = cons_list[idx];

        // Don't remove indir call constraints
        auto rc = cons_set.emplace(idx);
        if (!rc.second) {
          cons_list[idx] = std::move(cons_list.back());
          cons_list.pop_back();
          continue;
        }
        ++idx;

        // Process the constraint
        cons.process(graph_, work, priority, update_set);
      }

      // This is only safe to put inside of the updated() conditional because
      // GEP edges cannot be added by constraints in my current implementation
      auto &edges = pnd->gepSuccs();
      std::set<std::pair<ValueMap::Id, int32_t>> seen_edges;
      // for (auto succ_pr : pnd->succs())
      for (size_t idx = 0; idx < edges.size();) {
        auto &succ_pr = edges[idx];
        auto succ_id = succ_pr.first;
        auto succ_offs = succ_pr.second;

        auto &succ_node = graph_.getNode(succ_id);

        // Dedup the edges
        auto rc = seen_edges.emplace(succ_node.id(), succ_offs);
        if (!rc.second) {
          edges[idx] = std::move(edges.back());
          edges.pop_back();
          continue;
        }
        idx++;


        adout("  GEPsucc: " << succ_node.id() << "\n");

        /*
        llvm::dbgs() << "Unioning succ: " << succ_node.id() << " and " <<
          pnd->id() << "\n";
        */
        auto &succ_pts = succ_node.ptsto();

        adout("  f: " << succ_offs << "\n");
        // adout("  i: " << pnd->ptsto() << "\n");
        adout("  u: " << update_set << "\n");
        adout("  o: " << succ_node.id() << ": " << succ_pts << "\n");
        // Don't gep with intvalue:
        auto update_set_clean = pnd->ptsto();

        update_set_clean.reset(ValueMap::IntValue);
        update_set_clean.reset(ValueMap::NullValue);

        bool ch = succ_pts.orOffs(update_set_clean, succ_offs);

        adout("  ch: " << ch << "\n");
        adout("  O: " << succ_node.id() << ": " << succ_pts << "\n");

        auto edge = std::make_pair(pnd->id(), succ_node.id());
        // If we haven't run LCD on this edge before, the points-to sets are not
        //   empty, and the two points-to sets are equal
        if (lcd_edges.find(edge) == std::end(lcd_edges) &&
            !pnd->ptsto().empty() &&
            pnd->ptsto() == succ_pts) {
          lcd_check_count++;
          lcd_nodes.insert(pnd->id());
          lcd_edges.insert(edge);
        }

        if (ch) {
          adout("    pnd: " << pnd->id() << ": gep push: " <<
            succ_node.id() << "\n");
          work.push(succ_node.id(), priority[succ_node.id().val()]);
        }
      }

      // Handle indirect calls....
      for (auto &tup : pnd->indirCalls()) {
        auto &ci = std::get<0>(tup);
        auto &cfg_id = std::get<1>(tup);
        auto &pts = std::get<2>(tup);
        auto pts_diff = update_set - pts;
        addIndirCall(pts_diff, ci, cfg_id, work, priority);
        pts |= update_set;

        // If we updated an indir call, update pnd, otherwise we'll crash
        pnd = &graph_.getNode(id);
      }
    }

    auto &copy_edges = pnd->copySuccs();
    Bitmap new_copy_edges;
    for (auto succ_val : copy_edges) {
      auto succ_id = ValueMap::Id(succ_val);
      // Nothing should write to null value ever ever ever
      assert(succ_id != ValueMap::NullValue);

      auto &succ_node = graph_.getNode(succ_id);

      // If we've already analyzed this node...
      if (new_copy_edges.test(succ_node.id().val())) {
        continue;
      }

      new_copy_edges.set(succ_node.id().val());

      adout(" succ: " << succ_node.id() << "\n");

      /*
      llvm::dbgs() << "Unioning succ: " << succ_node.id() << " and " <<
        pnd->id() << "\n";
      */
      auto &succ_pts = succ_node.ptsto();

      adout("  f: 0\n");
      // adout("  i: " << pnd->ptsto() << "\n");
      adout("  u: " << update_set << "\n");
      adout("  p: " << pnd->ptsto() << "\n");
      adout("  o: " << succ_node.id() << ": " << succ_pts << "\n");

      /*
      if (solve_debug_id > 0 &&
          pnd->ptsto().test(ObjectMap::ObjID(solve_debug_id)) &&
          !succ_pts.test(ObjectMap::ObjID(solve_debug_id))) {
        llvm::dbgs() << "  Node: " << succ_node.id() << " |= " << pnd->id() <<
          " gaining id: " << solve_debug_id << "\n";
      }
      */

      bool ch = succ_pts |= pnd->ptsto();

      adout("  ch: " << ch << "\n");
      adout("  O: " << succ_node.id() << ": " << succ_pts << "\n");

      auto edge = std::make_pair(pnd->id(), succ_node.id());
      // If we haven't run LCD on this edge before, the points-to sets are not
      //   empty, and the two points-to sets are equal
      if (lcd_edges.find(edge) == std::end(lcd_edges) &&
          !update_set.empty() &&
          pnd->ptsto() == succ_pts) {
        lcd_check_count++;
        lcd_nodes.insert(pnd->id());
        lcd_edges.insert(edge);
      }

      if (ch) {
        adout("    pnd: " << pnd->id() << ": copy push: " <<
          succ_node.id() << "\n");
        work.push(succ_node.id(), priority[succ_node.id().val()]);
      }
    }
    pnd->setCopySuccs(std::move(new_copy_edges));


    // llvm::dbgs() << "lcd_nodes.size(): " << lcd_nodes.size() << "\n";
    if (lcd_nodes.size() > LCD_SIZE ||
        (vtime - lcd_last_time) > LCD_PERIOD) {
      // llvm::dbgs() << " !! Running lcd\n";
      // Do lcd
      RunNuutila(graph_, lcd_nodes, work, priority);
      // Clear lcd_nodes
      lcd_nodes.clear();
      lcd_last_time = vtime;
    }
  }

  llvm::dbgs() << "Final hcd_merge_count: " << hcd_merge_count << "\n";
  llvm::dbgs() << "Final lcd_check_count: " << lcd_check_count << "\n";
  llvm::dbgs() << "Final lcd_merge_count: " << lcd_merge_count << "\n";

  return false;
}

void AndersCons::process(AndersGraph &graph, Worklist<AndersGraph::Id> &wl,
    const std::vector<uint32_t> &priority,
    const PtstoSet &update_dest) const {

  switch (type_) {
    case ConstraintType::Store:
    {
      // This is a store:
      // *n < b
      // For each points-to in dest
      bool ch = false;
      // auto &dest_pts = update_dest;
      /*
      auto &dest_pts = dest_node.ptsto();
      */

      auto &dest_pts = update_dest;
      auto &src_node = graph.getNode(src());

      if (src_node.id() == ValueMap::IntValue ||
          src_node.id() == ValueMap::NullValue) {
        return;
      }

      adout("    storecons add edges: " << dest_pts << " to " << src_node.id()
          << "\n");
      ch = src_node.addCopyEdges(dest_pts);
      /*
      for (auto dest_id : dest_pts) {
        auto &pt_node = graph.getNode(dest_id);
        adout("      pts_node: " << pt_node.id() << "\n");
        if (pt_node.id() != src_node.id() &&
            pt_node.id() != ObjectMap::IntValue &&
            pt_node.id() != ObjectMap::NullValue) {
          ch |= src_node.addCopyEdge(pt_node.id());
          adout("      " << src_node.id() << " <- edge - " <<
             pt_node.id() << "\n");
        }
      }
      */

      if (ch) {
        adout("  StoreCons: added: " << src_node.id() << " to WL\n");
        wl.push(src_node.id(), priority[src_node.id().val()]);
      }
      break;
    }
    case ConstraintType::Load:
    {
      // This is a store:
      // a < *n
      // For each points-to in src
      // auto &src_pts = update_src;
      // auto &src_pts = graph.getNode(src()).ptsto();
      auto &src_pts = update_dest;
      auto &dest_node = graph.getNode(dest());
      assert(dest_node.id() != ValueMap::IntValue);
      assert(dest_node.id() != ValueMap::NullValue);

      for (auto pts_id : src_pts) {
        auto &pt_node = graph.getNode(pts_id);
        // Don't add ptr to yourself, or null
        if (pt_node.id() != dest_node.id() &&
            pt_node.id() != ValueMap::IntValue &&
            pt_node.id() != ValueMap::NullValue) {
          adout("    loadcons (" << *this << ") add edges: "
              << dest_node.id() << " to " <<
              pt_node.id() << "\n");
          bool ch = pt_node.addCopyEdge(dest_node.id());

          if (ch) {
            adout("  LoadCons: added: " << pt_node.id() << " to WL\n");
            wl.push(pt_node.id(), priority[pt_node.id().val()]);
          }
        }
      }
      break;
    }
    default:
      llvm_unreachable("Shouldn't have addrof or copy cons?");
  }
}

void SpecAnders::handleGraphChange(
    size_t old_size,
    Worklist<AndersGraph::Id> &wl,
    std::vector<uint32_t> &priority) {
  // And grow our priority list now...
  priority.resize(graph_.size(), 0);

  // Finally, add any node with a non-zero ptsto to our graph...
  for (Id node_id(old_size); node_id < Id(graph_.size()); ++node_id) {
    auto &node = graph_.getNode(node_id);

    if (!node.ptsto().empty()) {
      wl.push(node.id(), 0);
    }
  }
}

// Handles constraints related to indirect functions
void SpecAnders::addIndirCall(const PtstoSet &fcn_pts,
    const CallInfo &caller_ci,
    CsFcnCFG::Id,
    Worklist<AndersGraph::Id> &wl,
    std::vector<uint32_t> &priority) {
  // First thing's first, add any needed nodes to our static CFG
  auto &cg = graph_.cg();
  auto &map = cg.vals();
  auto &used_info = dynInfo_->used_info;

  // Then, iterate each function in our pts set
  for (auto id : fcn_pts) {
    auto callee_fcn = dyn_cast_or_null<llvm::Function>(map.getValue(id));

    if (callee_fcn != nullptr) {
      if (callee_fcn->isDeclaration()) {
        // Okay, we have an external call, that's ugly.
        // Add constraints to cg_
        // Add nodes to graph as appropriate...
        auto old_size = graph_.size();
        llvm::ImmutableCallSite cs(caller_ci.ci());
        auto fill_vec = graph_.addExternalCall(cs, callee_fcn, caller_ci);
        for (auto id : fill_vec) {
          auto &node = graph_.getNode(id);
          node.clearOldPtsto();
          wl.push(id, priority[static_cast<size_t>(id)]);
        }
        handleGraphChange(old_size, wl, priority);
      } else {
        if (!used_info.isUsed(callee_fcn)) {
          continue;
        }

        // Find the call dest in my cg's callInfo_ selection
        // Add edges between the two call nodes
        auto &callee_ci = cg.getCallInfo(callee_fcn);
        llvm::dbgs() << "Mapping in call to: " << callee_fcn->getName() << "\n";
        addIndirEdges(caller_ci, callee_ci, wl, priority);

        /* FIXME: remove eventually -- dont need this graph in non-cs anders
        // Also map the call edge into our main CFG
        auto callee_id = callee_it->second.second;
        auto &callee_node = cg.localCFG().getNode(callee_id);
        callee_node.addPred(cur_graph_node);
        */
      }
    }
  }
}

void SpecAnders::addIndirEdges(const CallInfo &caller_ci,
    const CallInfo &callee_ci,
    Worklist<AndersGraph::Id> &wl,
    const std::vector<uint32_t> &priority) {

  // First handle args
  auto &callee_args = callee_ci.args();
  auto &caller_args = caller_ci.args();

  auto callee_arg_it = std::begin(callee_args);
  auto callee_arg_en = std::end(callee_args);

  auto caller_arg_it = std::begin(caller_args);
  auto caller_arg_en = std::end(caller_args);

  for (; caller_arg_it != caller_arg_en && callee_arg_it != callee_arg_en;
      ++callee_arg_it, ++caller_arg_it) {
    auto callee_arg_id = *callee_arg_it;
    auto caller_arg_id = *caller_arg_it;

    llvm::dbgs() << "got callee_arg: " << callee_arg_id << "\n";
    llvm::dbgs() << "got caller_arg: " << caller_arg_id << "\n";
    llvm::dbgs() << "graph size: " << graph_.size() << "\n";
    auto &callee_arg_node = graph_.getNode(callee_arg_id);
    auto &caller_arg_node = graph_.getNode(caller_arg_id);

    bool ch;
    if (caller_arg_node.id() == ValueMap::NullValue) {
      ch = callee_arg_node.ptsto().set(ValueMap::NullValue);
    } else if (caller_arg_node.id() == ValueMap::IntValue) {
      ch = callee_arg_node.ptsto().set(ValueMap::IntValue);
    } else {
      ch = caller_arg_node.addCopyEdge(callee_arg_node.id());
    }

    // Also add all of those nodes to our worklist
    if (ch) {
      wl.push(caller_arg_node.id(),
          priority[static_cast<size_t>(caller_arg_node.id())]);
    }
  }

  // Then handle rets
  auto callee_ret = callee_ci.ret();
  // If we have a return site
  if (callee_ret != ValueMap::Id::invalid()) {
    // Create an edge from their ret to our ret (if we have a ret)
    // ... and push that node to our worklist
    auto caller_ret = caller_ci.ret();

    // Copy data in...
    auto &callee_ret_node = graph_.getNode(callee_ret);
    auto &caller_ret_node = graph_.getNode(caller_ret);
    assert(caller_ret != ValueMap::NullValue);
    // Don't add edges to int or null..
    /*
    llvm::dbgs() << "Adding ret copy edge: " << callee_ret_node.id() <<
      " -> " << caller_ret_node.id() << "\n";
    */
    bool ch = callee_ret_node.addCopyEdge(caller_ret_node.id());

    if (ch) {
      wl.push(callee_ret_node.id(),
          priority[static_cast<size_t>(callee_ret_node.id())]);
    }
  }
}

//}}}

