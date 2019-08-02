/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_CONSTRAINTGRAPH_H_
#define INCLUDE_CONSTRAINTGRAPH_H_

#include "include/ObjectMap.h"

#include "include/SEG.h"
#include "include/Debug.h"

#include <utility>

enum class ConstraintType { Copy = 0, Load = 1, Store = 2, AddressOf = 3 };
class Constraint {
  //{{{
 public:
    typedef typename ObjectMap::ObjID ObjID;

    struct SrcDestCmp {
      bool operator()(const Constraint &lhs, const Constraint &rhs) const {
        if (lhs.src() == rhs.src()) {
          return lhs.dest() < rhs.dest();
        }

        return lhs.src() < rhs.src();
      }
    };

    // Constructors {{{
    Constraint(ObjID s, ObjID d, ConstraintType t) :
        Constraint(s, d, t, 0) {
    }

    Constraint(ObjID s, ObjID d,
          ConstraintType t, int32_t o) :
        // Note, when rep not specified, rep is dest
        Constraint(t, s, d, d, o) {
      assert(t != ConstraintType::Load && t != ConstraintType::Store);
    }

    Constraint(ConstraintType type, ObjID src, ObjID dest, ObjID rep) :
          Constraint(type, src, dest, rep, 0) { }

    Constraint(ConstraintType type, ObjID src, ObjID dest, ObjID rep,
        int32_t offs) :
        src_(src), dest_(dest), rep_(rep), type_(type), offs_(offs) {

      // assert(rep.val() != 191751);

      /*
      if (dest.val() == 2822 || src.val() == 2822) {
        llvm::dbgs() << "!!Have 2822 cons: " << *this << "\n";
      }
      */

      /*
      if (dest == ObjectMap::NullValue) {
        llvm::dbgs() << "Have dest of null in cons: " << *this << "\n";
      }

      if (src == ObjectMap::NullValue) {
        llvm::dbgs() << "Have src of null in cons: " << *this << "\n";
      }
      */

      /*
      if (dest == ObjectMap::IntValue) {
        llvm::dbgs() << "Have dest of intval in cons: " << *this << "\n";
      }

      if (dest == ObjectMap::UniversalValue) {
        llvm::dbgs() << "Have dest of UniveralVal in cons: " << *this << "\n";
      }

      if (src == ObjectMap::IntValue) {
        llvm::dbgs() << "Have src of intval in cons: " << *this << "\n";
      }
      */

      if (src == ObjectMap::UniversalValue) {
        /*
        static size_t cnt = 0;
        cnt++;
        */
        llvm::dbgs() << "Have src of UniveralVal in cons: " << *this << "\n";
        // assert(cnt != 2);
      }

      /*
      if (dest == ObjectMap::ObjID(4957) || dest == ObjectMap::ObjID(3441) ||
         dest == ObjectMap::ObjID(3446)) {
        llvm::dbgs() << "!!!  Have edge to " << dest << " !!!\n";
        llvm::dbgs() << "   src is: " << src << "\n";
        llvm::dbgs() << "   type is: " << static_cast<int32_t>(type) << "\n";
      }

      if (src == ObjectMap::ObjID(1819)) {
        llvm::dbgs() << "!!!  Have edge FROM " << dest << " !!!\n";
        llvm::dbgs() << "   dest is: " << dest << "\n";
        llvm::dbgs() << "   type is: " << static_cast<int32_t>(type) << "\n";
      }
      */

      // We shouldn't copy from the UV to null val... its bad
      assert(!(type == ConstraintType::Copy &&
          src == ObjectMap::UniversalValue &&
          dest == ObjectMap::NullValue));
    }
      

    // copy / moves {{{
    Constraint(const Constraint &) = default;
    Constraint &operator=(const Constraint &) = default;

    Constraint(Constraint &&) = default;
    Constraint &operator=(Constraint&&) = default;
    //}}}
    //}}}

    // Accessors {{{
    ObjID src() const {
      return src_;
    }

    ObjID offsSrc() const {
      return ObjectMap::getOffsID(src(), offs());
    }

    ObjID dest() const {
      return dest_;
    }

    ObjID rep() const {
      return rep_;
    }
    
    void updateRep(ObjID new_rep) {
      rep_ = new_rep;
    }

    void retarget(ObjID src, ObjID dest) {
      src_ = src;
      dest_ = dest;
    }

    ConstraintType type() const {
      return type_;
    }

    int32_t offs() const {
      return offs_;
    }

    bool operator<(const Constraint &cons_rhs) const {
      if (type() != cons_rhs.type()) {
        return type() < cons_rhs.type();
      }

      if (dest() != cons_rhs.dest()) {
        return dest() < cons_rhs.dest();
      }

      if (src() != cons_rhs.src()) {
        return src() < cons_rhs.src();
      }

      if (offs() != cons_rhs.offs()) {
        return offs() < cons_rhs.offs();
      }

      return false;
    }

    // For LLVM RTTI {{{
    static bool classof(const Constraint *) {
      return true;
    }
    //}}}
    //}}}

    // Remap {{{
    void remap(const util::ObjectRemap<ObjID> &remap) {
      src_ = remap[src_];
      dest_ = remap[dest_];
      if (remap[rep_] == ObjID(210796)) {
        llvm::dbgs() << "cg Remapping: " << rep_ << " to " << remap[rep_] <<
          "\n";
      }
      
      if (rep_ == ObjID(210796)) {
        llvm::dbgs() << "??cg Remapping: " << rep_ << " to " << remap[rep_] <<
          "\n";
      }

      if (rep_ == ObjID(87170)) {
        llvm::dbgs() << "cg Remapping: " << rep_ << " to " << remap[rep_] <<
          "\n";
      }
      rep_ = remap[rep_];
    }
    // }}}

    // Print helper {{{
    void print_label(dbg_ostream &ofil, const ObjectMap &) const {
      switch (type()) {
        case ConstraintType::Copy:
          ofil << "copy";
          break;
        case ConstraintType::AddressOf:
          ofil << "addr_of";
          break;
        case ConstraintType::Load:
          ofil << "load";
          break;
        case ConstraintType::Store:
          ofil << "store";
          break;
        default:
          unreachable("Constraint with unexpected type!");
          ofil << "BLEH";
      }
    }

    static constexpr const char *getTypeName(ConstraintType t) {
      return (t == ConstraintType::Copy) ? "copy" :
             (t == ConstraintType::AddressOf) ? "address_of" :
             (t == ConstraintType::Load) ? "load" :
             (t == ConstraintType::Store) ?  "store" :
             "ERROR UNKNOWN CONST EXPR";
    }

    friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
        const Constraint &cons) {
      o << cons.rep() << ": " << getTypeName(cons.type()) << ", (" <<
          cons.src() << ", " << cons.dest() << ") + " << cons.offs();
      return o;
    }
    //}}}

 private:
    // Private Data {{{
    ObjID src_;
    ObjID dest_;
    ObjID rep_;

    ConstraintType type_;

    int32_t offs_ = 0;
    //}}}
  //}}}
};

class ConstraintGraph {
  //{{{
 public:
    // Typedefs {{{
    // ObjIDs
    typedef ObjectMap::ObjID ObjID;

    struct cons_id { };
    typedef util::ID<cons_id, int32_t>  ConsID;
    //}}}

    ConstraintGraph() = default;
    ConstraintGraph(const ConstraintGraph &cg) :
        P2ICast_(cg.P2ICast_),
        indirectCalls_(cg.indirectCalls_) {
      constraints_.reserve(cg.constraints_.size());
      for (auto &pcons : cg.constraints_) {
        constraints_.emplace_back(new Constraint(*pcons));
      }
    }

    class IndirectCallInfo {
      //{{{
     public:
       IndirectCallInfo(bool is_pointer, ObjID callee, std::vector<ObjID> args) :
           isPointer_(is_pointer), callee_(callee), args_(std::move(args)) { }

       bool isPointer() const {
         return isPointer_;
       }

       void setCallee(ObjID callee) {
         callee_ = callee;
       }

       ObjID callee() const {
         return callee_;
       }

       size_t args_size() const {
         return args_.size();
       }

       typedef std::vector<ObjID>::const_iterator const_iterator;
       typedef std::vector<ObjID>::iterator iterator;

       iterator begin() {
         return std::begin(args_);
       }

       iterator end() {
         return std::end(args_);
       }

       const_iterator begin() const {
         return std::begin(args_);
       }

       const_iterator end() const {
         return std::end(args_);
       }

       void remap(const util::ObjectRemap<ObjID> &remap) {
         callee_ = remap[callee_];
         std::transform(std::begin(args_), std::end(args_), std::begin(args_),
             [&remap] (ObjID id) { return remap[id]; });
       }

     private:
      const bool isPointer_;
      ObjID callee_;
      std::vector<ObjID> args_;
      //}}}
    };

    // Modifiers {{{
    ConsID add(ConstraintType type, ObjID d, ObjID s) {
      return add(type, d, s, 0);
    }

    ConsID add(ConstraintType type, ObjID d, ObjID s, int o) {
      /*
      dbg << "Adding edge: (" << s << ", " << d <<
        ") with type: " << static_cast<int32_t>(type) << "\n";
        */
      // assert(!(s == ObjectMap::ObjID(20852) && d == ObjectMap::ObjID(3167)));
      // assert(!(s == ObjectMap::ObjID(72) && d == ObjectMap::ObjID(28)));
      if (s == ObjectMap::NullValue || d == ObjectMap::NullValue ||
          s == ObjectMap::NullObjectValue || d == ObjectMap::NullObjectValue) {
        // llvm::dbgs() << "Skipping null constraint....\n";
        return ConsID();
      } else {
        assert(!(type == ConstraintType::Copy &&
            s == ObjectMap::UniversalValue &&
            d == ObjectMap::NullValue));
        constraints_.emplace_back(new Constraint(s, d, type, o));

        auto id = ConsID(constraints_.size()-1);

        return id;
      }
    }

    ConsID add(ConstraintType type, ObjID nd, ObjID s, ObjID d) {
      constraints_.emplace_back(new Constraint(type, s, d, nd));

      auto id = ConsID(constraints_.size()-1);
      return id;
    }

    void addIndirectCall(ObjID call_id, bool is_pointer, ObjID callee,
        std::vector<ObjID> args) {
      indirectCalls_.emplace(std::piecewise_construct,
          std::forward_as_tuple(call_id),
          std::forward_as_tuple(is_pointer, callee, std::move(args)));
    }

    void updateIndirectCalls(std::map<ObjID, IndirectCallInfo> indirect_calls) {
      indirectCalls_ = std::move(indirect_calls);
    }

    bool isIndirCall(ObjectMap::ObjID id) const {
      return indirectCalls_.find(id) != std::end(indirectCalls_);
    }

    void removeConstraint(std::unique_ptr<Constraint> &pcons) {
      if (pcons->rep() == ObjID(210796)) {
        llvm::dbgs() << "Removing cons: " << *pcons << "\n";
        assert(0);
      }
      pcons.reset(nullptr);
    }

    void removeConstraint(ConsID id) {
      // Reset the ptr to nullptr
      removeConstraint(constraints_.at(static_cast<size_t>(id)));
    }

    void updateObjIDs(const util::ObjectRemap<ObjID> &remap) {
      // First constraints
      for (auto &pcons : constraints_) {
        // Remap the rep dest and src of the constraint
        if (pcons != nullptr) {
          pcons->remap(remap);
        }
      }

      // Then P2I
      for (auto &pr : P2ICast_) {
        pr.second = remap[pr.second];
      }

      // Finally indir calls
      std::map<ObjID, IndirectCallInfo> new_indir;
      for (auto &pr : indirectCalls_) {
        pr.second.remap(remap);
        new_indir.emplace(remap[pr.first], std::move(pr.second));
      }

      indirectCalls_ = std::move(new_indir);
    }
    //}}}

    // Accessors {{{
    Constraint *tryGetConstraint(ConsID id) {
      return constraints_.at(id.val()).get();
    }

    Constraint  &getConstraint(ConsID id) {
      return *constraints_.at(id.val());
    }

    const Constraint  &getConstraint(ConsID id) const {
      return *constraints_.at(id.val());
    }

    size_t getNumConstraints() const {
      size_t num_cons = 0;

      for (auto &pcons : constraints_) {
        if (pcons != nullptr) {
          num_cons++;
        }
      }

      return num_cons;
    }

    size_t constraintSize() const {
      return constraints_.size();
    }

    typedef std::map<const llvm::Value *, ObjID>::const_iterator
      p2icast_iterator;

    p2icast_iterator findP2ICast(const llvm::Value *i_val) const {
      return P2ICast_.find(i_val);
    }

    bool addP2ICast(const llvm::Value *i_val, ObjID p_val) {
      auto ret = P2ICast_.emplace(i_val, p_val);
      assert(ret.second);
      return ret.second;
    }

    ObjID getMaxID() const {
      ObjectMap::ObjID max_src_dest_id = ObjectMap::ObjID(-1);
      for (const auto &pcons : *this) {
        if (pcons == nullptr) {
          continue;
        }
        // Store constraints don't define nodes!
        auto dest = pcons->dest();
        auto src = pcons->src();
        auto rep = pcons->rep();

        if (dest > max_src_dest_id) {
          max_src_dest_id = dest;
        }

        if (src > max_src_dest_id) {
          max_src_dest_id = src;
        }

        if (rep > max_src_dest_id) {
          max_src_dest_id = rep;
        }
      }

      return max_src_dest_id;
    }

    p2icast_iterator p2icast_end() const {
      return std::end(P2ICast_);
    }

    p2icast_iterator p2icast_begin() const {
      return std::begin(P2ICast_);
    }
    //}}}

    // Graph print debugging {{{
    void printDotConstraintGraph(const std::string &graphname,
        const ObjectMap &omap) const;

    void countConstraints(const ObjectMap &omap) const {
      size_t num_alloc = 0;
      size_t num_gep = 0;
      size_t num_copy = 0;
      size_t num_load = 0;
      size_t num_store = 0;
      size_t total_cons = 0;
      for (auto &pcons : *this) {
        if (pcons == nullptr) {
          continue;
        }
        total_cons++;

        switch (pcons->type()) {
          case ConstraintType::AddressOf:
            num_alloc++;
            break;
          case ConstraintType::Copy:
            if (pcons->offs() != 0) {
              num_gep++;
            } else {
              num_copy++;
            }
            break;
          case ConstraintType::Store:
            num_store++;
            break;
          case ConstraintType::Load:
            num_load++;
            break;
        }
      }

      llvm::dbgs() << "  num_objs: " << omap.getNumObjs() << "\n";

      llvm::dbgs() << "  Total number of constraints: " << total_cons << "\n";
      llvm::dbgs() << "  num_alloc: " << num_alloc << "\n";
      llvm::dbgs() << "  num_gep: " << num_gep << "\n";
      llvm::dbgs() << "  num_copy: " << num_copy << "\n";
      llvm::dbgs() << "  num_load: " << num_load << "\n";
      llvm::dbgs() << "  num_store: " << num_store << "\n";

      util::SparseBitmap<> nodes;
      for (auto &pcons : *this) {
        if (pcons == nullptr) {
          continue;
        }

        // Ignore address of destinations?
        if (pcons->type() == ConstraintType::AddressOf) {
          // Add dest only for addressof
          nodes.set(pcons->dest().val());
          continue;
        }

        nodes.set(pcons->dest().val());
        nodes.set(pcons->src().val());
      }

      llvm::dbgs() << "  num_nodes: " << nodes.count() << "\n";
    }
    //}}}

    // Iteration {{{
    typedef std::vector<std::unique_ptr<Constraint>>::iterator iterator;
    typedef std::vector<std::unique_ptr<Constraint>>::const_iterator const_iterator;
    typedef std::unique_ptr<Constraint> iter_type;

    iterator begin() {
      return std::begin(constraints_);
    }

    iterator end() {
      return std::end(constraints_);
    }

    const_iterator begin() const {
      return std::begin(constraints_);
    }

    const_iterator end() const {
      return std::end(constraints_);
    }

    const_iterator cbegin() const {
      return std::begin(constraints_);
    }

    const_iterator cend() const {
      return std::end(constraints_);
    }

    typedef std::map<ObjID, IndirectCallInfo>::iterator indir_iterator;
    typedef std::map<ObjID, IndirectCallInfo>::const_iterator const_indir_iterator;

    indir_iterator indir_begin() {
      return std::begin(indirectCalls_);
    }

    indir_iterator indir_end() {
      return std::end(indirectCalls_);
    }

    llvm::iterator_range<indir_iterator> indirs() {
      return llvm::iterator_range<indir_iterator>(indirectCalls_);
    }

    const_indir_iterator indir_begin() const {
      return std::begin(indirectCalls_);
    }

    const_indir_iterator indir_end() const {
      return std::end(indirectCalls_);
    }

    const_indir_iterator indir_cbegin() const {
      return std::begin(indirectCalls_);
    }

    const_indir_iterator indir_cend() const {
      return std::end(indirectCalls_);
    }

    llvm::iterator_range<const_indir_iterator> indirs() const {
      return llvm::iterator_range<const_indir_iterator>(indirectCalls_);
    }

    //}}}

 private:
    // Private data {{{
    std::vector<std::unique_ptr<Constraint>> constraints_;

    // Tracks casts from pointers to integers, to help improve the accuracy of
    //   I2P casts
    std::map<const llvm::Value *, ObjID> P2ICast_;

    // ID of the call inst -> ret id
    std::map<ObjID, IndirectCallInfo> indirectCalls_;
    //}}}
  //}}}
};

#endif  // INCLUDE_CONSTRAINTGRAPH_H_
