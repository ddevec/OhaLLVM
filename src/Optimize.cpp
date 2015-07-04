/*
 * Copyright (C) 2015 David Devecsery
 */

#include <cassert>
#include <cstdint>

#include <limits>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "include/SpecSFS.h"
#include "include/id.h"

#include "llvm/ADT/SparseBitVector.h"

using namespace llvm;  // NOLINT

namespace {

// Forward decl for map typedef
class HUNode;

typedef SparseBitVector<> Bitmap;
typedef std::map<DUG::ObjID, HUNode> NodeMapping;

// Debugging fcns {{{
template<typename idT>
static std::string idToString(idT id) {
  auto val = id.val();

  if (val == 0) {
    return "a";
  }

  int len = 0;

  auto val_bkp = val;
  while (val_bkp != 0) {
    ++len;
    val_bkp /= 10;
  }

  std::string ret(len, 'a');

  for (int i = 0; i < len; i++) {
    char digit = val % 10;
    val /= 10;

    ret.replace(i, 1, 1, 'a' + digit);
  }

  return ret;
}
//}}}


// Okay, we're going to need a graph of some kind...
// Unique ID maintainers {{{
static int32_t nextHuNodeNum = 0;
static int32_t nextDfsNum = 0;
static int32_t nextPENum = 0;

static DUG::PEid getNextPE() {
  return DUG::PEid(nextPENum++);
}

static int32_t getNextDfsNum() {
  return nextDfsNum++;
}

static int32_t getNextHuNodeNum() {
  return nextHuNodeNum++;
}

//}}}

class HUNode {
  //{{{
 public:
    static const int32_t DfsNumInvalid = std::numeric_limits<int32_t>::max();
    static const int32_t RepNumInvalid = -1;

    // Constructor
    HUNode() : nodenum_(getNextHuNodeNum()) { }

    // No move/copy {{{
    HUNode(HUNode &&) = delete;
    HUNode(const HUNode &) = delete;

    HUNode &operator=(const HUNode &) = delete;
    HUNode &operator=(HUNode &&) = delete;
    //}}}

    // Equality stuffs {{{
    bool operator==(const HUNode &n) {
      return nodenum_ == n.nodenum_;
    }

    bool operator<(const HUNode &n) {
      return nodenum_ < n.nodenum_;
    }
    //}}}

    // Setting up graph {{{
    void addPred(HUNode &n) {
      preds_.insert(&n);
    }

    void addPtsTo(DUG::ObjID id) {
      ptsto_.set(id.val());
    }

    const Bitmap &ptsto() const {
      return ptsto_;
    }

    bool indirect() const {
      return indirect_;
    }

    void setIndirect() {
      indirect_ = true;
    }

    HUNode &rep() {
      return *findRep(this);
    }

    bool isRep() {
      return rep_ != nullptr;
    }

    void setObj(DUG::ObjID obj) {
      // Our obj should either be invalid, or this should be resetting it
      assert(!obj_.valid() || obj_ == obj);
      obj_ = obj;
    }

    DUG::ObjID obj() const {
      return obj_;
    }
    //}}}



    // Actual HU algorithm {{{
    void visitHU() {
      visitHU(0);
    }

    void unite(HUNode &node) {
      assert(ptsto_ == node.ptsto_);
      assert(&node != this);

      // Collapse the reps on find
      auto &rep_node1 = *findRep(&node);
      auto &rep_node2 = *findRep(this);

      // If the two are already in the same rep, ignore
      if (rep_node1 == rep_node2) {
        return;
      }

      assert(rep_node2.ptsto_ == rep_node1.ptsto_);

      // Now, combine the preds
      rep_node2.preds_.insert(std::begin(rep_node1.preds_),
          std::end(rep_node1.preds_));

      // Clear out node1
      rep_node1.preds_.clear();
      rep_node1.ptsto_.clear();

      // Update the rep info
      assert(&rep_node2 != &rep_node1);
      rep_node1.rep_ = &rep_node2;
    }
    //}}}

 private:
    // Private fields {{{
    HUNode *rep_ = nullptr;
    int32_t nodenum_;
    int32_t dfsNum_ = DfsNumInvalid;
    bool indirect_ = false;

    DUG::ObjID obj_;

    Bitmap ptsto_;

    std::set<HUNode *> preds_;
    //}}}

    // Internal helpers {{{
    // Acutal HU visit impl
    void visitHU(int32_t dfs) {
      // If we haven't actually been visited, do the visit
      if (dfsNum_ > dfs) {
        dbgs() << "Visiting " << idToString(obj_) << "\n";
        dfsNum_ = dfs;

        // Union our past ptsto sets
        for (auto pnode : preds_) {
          auto &node = *pnode;

          node.visitHU(dfs + 1);

          ptsto_ |= node.ptsto_;
        }
      }
    }

    static HUNode *findRep(HUNode *node) {
      if (node->rep_ == nullptr) {
        return node;
      } else {
        assert(node->rep_ != node);
        node->rep_ = findRep(node->rep_);
        return node->rep_;
      }
    }
    //}}}
  //}}}
};

// Helper Functions {{{
static int getIdx(DUG::ObjID id) {
  return id.val();
}

static HUNode &getNode(DUG::ObjID id, NodeMapping &nodes) {
  return nodes[id];
}

static int createGraph(const Constraint &con,
    NodeMapping &nodes, const ObjectMap &omap) {
  HUNode &src = getNode(con.src(), nodes);
  HUNode &dest = getNode(con.dest(), nodes);

  src.setObj(con.src());
  dest.setObj(con.dest());

  /*
  dbgs() << "createGraph src: " << idToString(con.src()) << "\n";
  dbgs() << "createGraph dest: " << idToString(con.src()) << "\n";
  */

  switch (con.type()) {
    case Constraint::Type::Store:
      // I think we just ignore stores
      break;
    case Constraint::Type::Load:
      // Add its own indirect ptsto
      if (con.offs() == 0) {
        dbgs() << "Adding edge: " << idToString(con.src()) << " -> " <<
          idToString(con.dest()) << "\n";
        dest.addPred(src);
      } else {
        dbgs() << "Seting: " << idToString(con.src()) << " to indirect\n";
        dest.setIndirect();
      }
      break;
    case Constraint::Type::AddressOf:
      dbgs() << "Seting: " << idToString(con.dest()) << "to indirect\n";
      dbgs() << "Adding ptsto: " << idToString(con.src()) << " to ptsto of: "
        << idToString(con.dest()) << "\n";
      dest.setIndirect();
      dest.addPtsTo(con.src());
      if (omap.isObject(con.src())) {
        src.setIndirect();
      }
      break;
    case Constraint::Type::Copy:
      dbgs() << "Adding edge: " << idToString(con.src()) << " -> " <<
        idToString(con.dest()) << "\n";
      dest.addPred(src);
      break;
    default:
      llvm_unreachable("Should never get here!\n");
  }
}
//}}}

}  // End anon namespace

bool SpecSFS::optimizeConstraints(DUG &graph, const ObjectMap &omap) {
  // Okay, we run HU here, over the constraints
  //
  // The algorithm is listed as:
  //  1) Create initial ptsto set for each node
  //  2) In topological order (depth first) for each node:
  //          S = {y:y->x} U {x}. then
  //          pts(x) = for all y in S: U pts(y)
  //  3) Assign labels, s.t.:
  //      for all x,y in V:
  //        pts(x) == pts(y) <-> pe(x) = pe(y)
  //  where pts is the ptsto set for a variable
  //  pe is the pointer equivalence
  //  V is the set of vertecies in the graph

  // The offline graph for optimizations
  NodeMapping nodes;

  // Populate the constraint graph
  std::for_each(graph.constraint_cbegin(), graph.constraint_cend(),
      [&nodes, &omap](const Constraint &con) {
    // Okay, now we create a graph node for each
    createGraph(con, nodes, omap);
  });

  for (auto &pair : nodes) {
    dbgs() << "initial ptsto for node " << idToString(pair.second.obj()) <<
      " is:";
    for (auto int_id : pair.second.ptsto()) {
      dbgs() << " " << idToString(DUG::ObjID(int_id));
    }
    dbgs() << "\n";
  }

  // Okay, now that we made the graph, do a dfs visit
  for (auto &pair : nodes) {
    pair.second.visitHU();
  }

  for (auto &pair : nodes) {
    dbgs() << "ptsto after HU for node " << idToString(pair.second.obj()) <<
      "is:";
    for (auto int_id : pair.second.ptsto()) {
      dbgs() << " " << idToString(DUG::ObjID(int_id));
    }
    dbgs() << "\n";
  }

  auto bitmap_lt = [](const Bitmap &b1, const Bitmap &b2) {
    auto it1 = std::begin(b1);
    auto it2 = std::begin(b2);
    auto en1 = std::end(b1);
    auto en2 = std::end(b2);

    // True if any element b1 < b2
    for (; it1 != en1 && it2 != en2; ++it1, ++it2) {
      // if it1 < it2 : b1 < b2
      if (*it1 < *it2) {
        return true;
      // If it1 > it2 : b1 > b2
      } else if (*it1 > *it2) {
        return false;
      }
      // Otherwise, they are equal, try the next element
    }

    // If they are equivalent but b1 is longer b1 is less than it b2
    if (it1 != en1) {
      return true;
    }

    return false;
  };

  std::map<DUG::ObjID, DUG::PEid> obj_to_pe;
  std::map<Bitmap, DUG::PEid, decltype(bitmap_lt)> pts_to_pe(bitmap_lt);

  // Now create the pointer equivalency ids
  for (auto &pair : nodes) {
    auto &node = pair.second;

    auto it = pts_to_pe.find(node.ptsto());

    DUG::PEid pe;
    if (node.indirect()) {
      pe = getNextPE();
      dbgs() << "pe for indirect node: " << pe.val() << "\n";
    } else if (it == std::end(pts_to_pe)) {
      pe = getNextPE();
      pts_to_pe.insert(std::make_pair(node.ptsto(), pe));
      dbgs() << "pe for ptsto: " << pe.val() << "\n";
    } else {
      pe = it->second;
      dbgs() << "pe gathered: " << pe.val() << "\n";
    }

    obj_to_pe.insert(std::make_pair(pair.first, pe));
  }

  std::map<DUG::PEid, std::vector<DUG::ObjID>> pe_to_obj;
  for (auto &pair : obj_to_pe) {
    pe_to_obj[pair.second].push_back(pair.first);
  }

  for (auto &pair : pe_to_obj) {
    dbgs() << "id remapping is now PE (" << pair.first.val() << "): "
      << idToString((pair.first)) << "is:";
    for (auto obj_id : pair.second) {
      dbgs() << " " << idToString(obj_id);
    }
    dbgs() << "\n";
  }

  graph.setupPE(obj_to_pe);

  return false;
}

