/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_ANDERSHELPERS_H_
#define INCLUDE_ANDERSHELPERS_H_

#include "include/ConstraintGraph.h"
#include "include/ObjectMap.h"
#include "include/SolveHelpers.h"

#include <memory>

class AndersGraph;
class AndersNode;
class AndersCons {
  //{{{
 public:
  typedef ObjectMap::ObjID ObjID;

  enum class Kind {
    Store,
    Load,
    IndirCall,
    Copy,
    Alloc
  };

  // Accessors {{{
  ObjID src() const {
    return src_;
  }

  ObjID dest() const {
    return dest_;
  }

  int32_t offs() const {
    return offs_;
  }

  Kind getKind() const {
    return kind_;
  }
  //}}}
  
  virtual void process(AndersGraph &graph, Worklist<AndersNode> &wl,
      const std::vector<uint32_t> &priority) const;
 
 protected:
  // Constructor {{{
  AndersCons(Kind kind, ObjID src, ObjID dest) : AndersCons(kind, src, dest, 0) { }
  AndersCons(Kind kind, ObjID src, ObjID dest, int32_t offs) :
    kind_(kind), src_(src), dest_(dest), offs_(offs) { }

  AndersCons(AndersCons &&) = default;
  AndersCons(const AndersCons &) = default;

  AndersCons &operator=(AndersCons &&) = default;
  AndersCons &operator=(const AndersCons &) = default;
  //}}}

 private:
  const Kind kind_;

  const ObjID src_;
  const ObjID dest_;
  const int32_t offs_;
  //}}}
};

class AndersStoreCons : public AndersCons {
 public:
  typedef ObjectMap::ObjID ObjID;

  AndersStoreCons(ObjID src, ObjID dest) :
      AndersCons(AndersCons::Kind::Store, src, dest, 0) { }

  void process(AndersGraph &graph, Worklist<AndersNode> &wl,
      const std::vector<uint32_t> &priority) const override;
};

class AndersLoadCons : public AndersCons {
 public:
  typedef ObjectMap::ObjID ObjID;

  AndersLoadCons(ObjID src, ObjID dest) :
      AndersCons(AndersCons::Kind::Load, src, dest, 0) { }

  void process(AndersGraph &graph, Worklist<AndersNode> &wl,
      const std::vector<uint32_t> &priority) const override;
};

class AndersIndirCallCons : public AndersCons {
 public:
  typedef ObjectMap::ObjID ObjID;

  // src is called pointer, dest is ret
  template <typename input_iterator>
  AndersIndirCallCons(ObjID src, ObjID dest,
      input_iterator arg_begin, input_iterator arg_end) :
      AndersCons(AndersCons::Kind::IndirCall, src, dest, 0),
      args_(arg_begin, arg_end) { }

  const std::vector<ObjID> &args() const {
    return args_;
  }

  ObjID ret() const {
    return dest();
  }

  ObjID callee() const {
    return src();
  }

  void process(AndersGraph &graph, Worklist<AndersNode> &wl,
      const std::vector<uint32_t> &priority) const override;

 private:
  const std::vector<ObjID> args_;
  const ObjID ret_;
};

class AndersNode {
  //{{{
 public:
  typedef ObjectMap::ObjID ObjID;

  // Internal types {{{
  class EdgeSet {
    //{{{
   public:
    EdgeSet() = default;

    bool insert(ObjID id) {
      edges_.push_back(id);
      return true;
    }

    bool insert(const EdgeSet &rhs) {
      edges_.insert(std::end(edges_),
          std::begin(rhs), std::end(rhs));
      return true;
    }

    // Returns true on success
    bool erase(ObjID id) {
      bool ret = false;
      auto it = std::find(std::begin(edges_), std::end(edges_), id);
      if (it != std::end(edges_)) {
        *it = edges_.back();
        edges_.pop_back();
        ret = true;
      }
      return ret;
    }

    void clear() {
      edges_.clear();
    }

    bool empty() const {
      return edges_.empty();
    }

    size_t size() const {
      return edges_.size();
    }

    void unique(AndersGraph &graph);

    bool operator==(const EdgeSet &rhs) const {
      return (edges_ == rhs.edges_);
    }

    bool operator|=(const EdgeSet &rhs) {
      bool ret = false;

      ret = insert(rhs);
      return ret;
    }

    typedef std::vector<ObjID>::iterator iterator;
    typedef std::vector<ObjID>::const_iterator const_iterator;

    iterator begin() {
      return std::begin(edges_);
    }

    iterator end() {
      return std::end(edges_);
    }

    const_iterator begin() const {
      return std::begin(edges_);
    }

    const_iterator end() const {
      return std::end(edges_);
    }

    const_iterator cbegin() const {
      return std::begin(edges_);
    }

    const_iterator cend() const {
      return std::end(edges_);
    }

   private:
    std::vector<ObjID> edges_;
    //}}}
  };
  //}}}

  // Constructors {{{
  //explicit AndersNode(Kind kind);
  AndersNode(ObjID id) : id_(id), rep_(id) { }

  AndersNode(const AndersNode &) = delete;
  AndersNode(AndersNode &&) = default;

  AndersNode &operator=(const AndersNode &) = delete;
  AndersNode &operator=(AndersNode &&) = delete;
  //}}}

  // Accessors {{{
  bool isRep() const {
    return rep_ == id();
  }

  ObjID rep() const {
    return rep_;
  }

  ObjID id() const {
    return id_;
  }

  PtstoSet &ptsto() {
    return ptsto_;
  }

  EdgeSet &succs() {
    return succs_;
  }

  std::vector<std::unique_ptr<AndersCons>> &constraints() {
    return constraints_;
  }
  //}}}

  // Modifiers {{{
  void setRep(ObjID new_rep) {
    rep_ = new_rep;
  }
  
  void addCons(std::unique_ptr<AndersCons> cons) {
    constraints_.emplace_back(std::move(cons));
  }
  //}}}

  void merge(AndersNode *rhs) {
    rhs->setRep(rep());

    succs_ |= rhs->succs_;
    strong_ &= rhs->strong_;
    ptsto_ |= rhs->ptsto_;
    oldPtsto_.clear();
  }

  // And the visit function!
  void visit(AndersGraph &graph, Worklist<AndersNode> &wl,
      const std::vector<uint32_t> &prioirty);

 private:
  // Private Data {{{
  const ObjID id_;

  // Used for node representatives...
  //   (for cycle removal)
  ObjID rep_;

  std::vector<std::unique_ptr<AndersCons>> constraints_;

  bool strong_;

  // Edges:
  EdgeSet succs_;

  PtstoSet ptsto_;
  PtstoSet oldPtsto_;
  //}}}

  //}}}
};

// Graph containing a node per ObjID (value)
class AndersGraph {
 public:
  typedef ObjectMap::ObjID ObjID;

  AndersGraph() = default;

  AndersGraph(const AndersGraph &) = delete;
  AndersGraph(AndersGraph &&) = delete;

  AndersGraph &operator=(const AndersGraph &) = delete;
  AndersGraph &operator=(AndersGraph &&) = delete;

  ObjID getRep(ObjID id) {
    auto ret = id;
    /*
    llvm::dbgs() << "id is: " << id << "\n";
    llvm::dbgs() << "nodes.size() is: " << nodes_.size() << "\n";
    */
    assert(static_cast<size_t>(id.val()) < nodes_.size());
    auto &nd = nodes_[id.val()];

    if (!nd.isRep()) {
      ret = getRep(nd.rep());
      nd.setRep(ret);
    }

    return ret;
  }
  
  AndersNode &getNode(ObjID id) {
    auto rep = getRep(id);

    return nodes_[rep.val()];
  }

  size_t size() const {
    return nodes_.size();
  }

  void fill(const ConstraintGraph &cg, ObjectMap &omap, llvm::Module &m) {
    // For each constraint destination, make a node.
    ObjID max_id(0);

    // Add indirect function argument locations to graph -- for use w/ indir
    //   callsite info
    // For each function object (not value)
    for (auto &fcn : m) {
      auto obj_id = omap.getObject(&fcn);
      auto ret_id = omap.getReturn(&fcn);
      // Generate an array containing all of that function's arguments
      std::vector<ObjID> args;
      std::for_each(fcn.arg_begin(), fcn.arg_end(),
          [&args, &omap, &max_id] (const llvm::Argument &arg) {
        auto arg_id = omap.getValue(&arg);

        args.push_back(arg_id);

        if (arg_id > max_id) {
          max_id = arg_id;
        }
      });
      // + ret ids
      // Add to fcns_ map
      fcns_.emplace(std::piecewise_construct,
          std::forward_as_tuple(obj_id),
          std::forward_as_tuple(ret_id, std::move(args)));
    }

    std::for_each(cg.indir_begin(), cg.indir_end(),
        [&max_id]
        (const std::pair<const ObjID, ConstraintGraph::IndirectCallInfo> &pr) {
      // Create an indir call cons
      // Populate w/ callsite info
      auto callinst = pr.first;
      auto &call_info = pr.second;

      // Setup ret if we return a pointer
      if (call_info.isPointer()) {
        if (callinst > max_id) {
          max_id = callinst;
        }
      }

      for (auto arg_id : call_info) {
        if (arg_id > max_id) {
          max_id = arg_id;
        }
      }
    });

    for (auto &pcons : cg) {
      if (pcons->dest() > max_id) {
        max_id = pcons->dest();
      }

      if (pcons->src() > max_id) {
        max_id = pcons->src();
      }
    }

    assert(nodes_.size() == 0);
    for (ObjID i(0); i <= max_id; i++) {
      nodes_.emplace_back(ObjID(i));
    }

    // Sanity check, there are no sources greater than max_id?
    if_debug_enabled(
      for (auto &pcons : cg) {
        assert(pcons->src() <= max_id);
      });

    // For each constraint, add it to the node associated with its source
    for (auto &pcons : cg) {
      auto &cons = *pcons;
      switch (cons.type()) {
        case ConstraintType::Load:
          {
            auto &node = getNode(cons.src());
            node.addCons(std::unique_ptr<AndersCons>(
                  new AndersLoadCons(cons.src(), cons.dest())));
            break;
          }
        case ConstraintType::Store:
          {
            // We add store constraints to the dest, as they are evaluated when
            //   the dest value changes
            auto &st_node = getNode(cons.dest());
            st_node.addCons(
                std14::make_unique<AndersStoreCons>(cons.src(), cons.dest()));
            break;
          }
        // Alloc constraints are added as initial points-to data
        case ConstraintType::AddressOf:
          {
            auto &node = getNode(cons.dest());
            node.ptsto().set(cons.src());
            break;
          }
        // Copy constraints are added as edges
        case ConstraintType::Copy:
          {
            auto &node = getNode(cons.src());
            node.succs().insert(cons.dest());
            break;
          }
        default:
          llvm_unreachable("Invalid cons type");
      }
    }

    // Add constraints for indirect function calls:
    // For each indirect callsite (in cg)
    std::for_each(cg.indir_begin(), cg.indir_end(),
        [this, &omap]
        (const std::pair<const ObjID, ConstraintGraph::IndirectCallInfo> &pr) {
      // Create an indir call cons
      // Populate w/ callsite info
      auto callinst = pr.first;
      auto &call_info = pr.second;

      // Defaults to invalid
      ObjID ret_id;

      // Setup ret if we return a pointer
      if (call_info.isPointer()) {
        ret_id = callinst;
      }

      auto arg_begin = std::begin(call_info); 
      auto arg_end = std::end(call_info); 

      auto callee = call_info.callee();

      auto &node = getNode(callee);

      node.addCons(
          std14::make_unique<AndersIndirCallCons>(callee, ret_id,
            arg_begin, arg_end));
    });
  }

  const std::pair<ObjID, std::vector<ObjID>> &
  getFcnInfo(ObjID fcn_obj_id) const {
    return fcns_.at(fcn_obj_id);
  }

  typedef std::vector<AndersNode>::iterator iterator;

  iterator begin() {
    return std::begin(nodes_);
  }

  iterator end() {
    return std::end(nodes_);
  }

 private:
   // Nodes in the graph, one per object
   std::vector<AndersNode> nodes_;

   std::map<ObjID, std::pair<ObjID, std::vector<ObjID>>> fcns_;
};

#endif  // INCLUDE_ANDERSHELPERS_H_
