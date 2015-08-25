/*
 * Copyright (C) 2015 David Devecsery
 *
 * FIXME: SHould have same header as Andersens.cpp
 *
 */

#ifndef INCLUDE_ANDERSENS_H_
#define INCLUDE_ANDERSENS_H_

#include <algorithm>
#include <list>
#include <map>
#include <set>
#include <queue>
#include <stack>
#include <utility>
#include <vector>

#define __STDC_LIMIT_MACROS
#define __STDC_CONSTANT_MACROS
#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Instructions.h"
#include "llvm/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/InstVisitor.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Support/Debug.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SparseBitVector.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/IntrinsicInst.h"

static const unsigned SelfRep = (unsigned)-1;
static const unsigned Unvisited = (unsigned)-1;
// Position of the function return node relative to the function node.
static const unsigned CallReturnPos = 1;
// Position of the function call node relative to the function node.
static const unsigned CallFirstArgPos = 2;

struct BitmapKeyInfo {
  static inline llvm::SparseBitVector<> *getEmptyKey() {
    return reinterpret_cast<llvm::SparseBitVector<> *>(-1);
  }
  static inline llvm::SparseBitVector<> *getTombstoneKey() {
    return reinterpret_cast<llvm::SparseBitVector<> *>(-2);
  }
  static unsigned getHashValue(const llvm::SparseBitVector<> *) {
    return 0;
  }
  static bool isEqual(const llvm::SparseBitVector<> *LHS,
                      const llvm::SparseBitVector<> *RHS) {
    if (LHS == RHS)
      return true;
    else if (LHS == getEmptyKey() || RHS == getEmptyKey()
             || LHS == getTombstoneKey() || RHS == getTombstoneKey())
      return false;

    return *LHS == *RHS;
  }

  static bool isPod() { return true; }
};

class Andersens : public llvm::ModulePass,
                  public llvm::AliasAnalysis,
                  private llvm::InstVisitor<Andersens> {
  struct Node;

  /// Constraint - Objects of this structure are used to represent the various
  /// constraints identified by the algorithm.  The constraints are 'copy',
  /// for statements like "A = B", 'load' for statements like "A = *B",
  /// 'store' for statements like "*A = B", and AddressOf for statements like
  /// A = alloca;  The Offset is applied as *(A + K) = B for stores,
  /// A = *(B + K) for loads, and A = B + K for copies.  It is
  /// illegal on addressof constraints (because it is statically
  /// resolvable to A = &C where C = B + K)

  struct Constraint {
    enum ConstraintType { Copy, Load, Store, AddressOf } Type;
    unsigned Dest;
    unsigned Src;
    unsigned Offset;

    Constraint(ConstraintType Ty, unsigned D, unsigned S, unsigned O = 0)
        : Type(Ty), Dest(D), Src(S), Offset(O) {
          assert((Offset == 0 || Ty != AddressOf) &&
                 "Offset is illegal on addressof constraints");
        }

    bool operator==(const Constraint &RHS) const {
      return RHS.Type == Type
          && RHS.Dest == Dest
          && RHS.Src == Src
          && RHS.Offset == Offset;
    }

    bool operator!=(const Constraint &RHS) const {
      return !(*this == RHS);
    }

    bool operator<(const Constraint &RHS) const {
      if (RHS.Type != Type)
        return RHS.Type < Type;
      else if (RHS.Dest != Dest)
        return RHS.Dest < Dest;
      else if (RHS.Src != Src)
        return RHS.Src < Src;
      return RHS.Offset < Offset;
    }
  };

  // Information DenseSet requires implemented in order to be able to do
  // it's thing
  struct PairKeyInfo {
    static inline std::pair<unsigned, unsigned> getEmptyKey() {
      return std::make_pair(~0U, ~0U);
    }
    static inline std::pair<unsigned, unsigned> getTombstoneKey() {
      return std::make_pair(~0U - 1, ~0U - 1);
    }
    static unsigned getHashValue(const std::pair<unsigned, unsigned> &P) {
      return P.first ^ P.second;
    }
    static unsigned isEqual(const std::pair<unsigned, unsigned> &LHS,
                            const std::pair<unsigned, unsigned> &RHS) {
      return LHS == RHS;
    }
  };

  struct ConstraintKeyInfo {
    static inline Constraint getEmptyKey() {
      return Constraint(Constraint::Copy, ~0U, ~0U, ~0U);
    }
    static inline Constraint getTombstoneKey() {
      return Constraint(Constraint::Copy, ~0U - 1, ~0U - 1, ~0U - 1);
    }
    static unsigned getHashValue(const Constraint &C) {
      return C.Src ^ C.Dest ^ C.Type ^ C.Offset;
    }
    static bool isEqual(const Constraint &LHS,
                        const Constraint &RHS) {
      return LHS.Type == RHS.Type && LHS.Dest == RHS.Dest
          && LHS.Src == RHS.Src && LHS.Offset == RHS.Offset;
    }
  };

  // Node class - This class is used to represent a node in the constraint
  // graph.  Due to various optimizations, it is not always the case that
  // there is a mapping from a Node to a Value.  In particular, we add
  // artificial Node's that represent the set of pointed-to variables shared
  // for each location equivalent Node.
  struct Node {
   private:
    static volatile llvm::sys::cas_flag Counter;

   public:
    llvm::Value *Val;
    llvm::SparseBitVector<> *Edges;
    llvm::SparseBitVector<> *PointsTo;
    llvm::SparseBitVector<> *OldPointsTo;
    std::list<Constraint> Constraints;

    // Pointer and location equivalence labels
    unsigned PointerEquivLabel;
    unsigned LocationEquivLabel;
    // Predecessor edges, both real and implicit
    llvm::SparseBitVector<> *PredEdges;
    llvm::SparseBitVector<> *ImplicitPredEdges;
    // Set of nodes that point to us, only use for location equivalence.
    llvm::SparseBitVector<> *PointedToBy;
    // Number of incoming edges, used during variable substitution to early
    // free the points-to sets
    unsigned NumInEdges;
    // True if our points-to set is in the Set2PEClass map
    bool StoredInHash;
    // True if our node has no indirect constraints (complex or otherwise)
    bool Direct;
    // True if the node is address taken, *or* it is part of a group of nodes
    // that must be kept together.  This is set to true for functions and
    // their arg nodes, which must be kept at the same position relative to
    // their base function node.
    bool AddressTaken;

    // Nodes in cycles (or in equivalence classes) are united together using a
    // standard union-find representation with path compression.  NodeRep
    // gives the index into GraphNodes for the representative Node.
    unsigned NodeRep;

    // Modification timestamp.  Assigned from Counter.
    // Used for work list prioritization.
    unsigned Timestamp;

    explicit Node(bool direct = true) :
        Val(0), Edges(0), PointsTo(0), OldPointsTo(0),
        PointerEquivLabel(0), LocationEquivLabel(0), PredEdges(0),
        ImplicitPredEdges(0), PointedToBy(0), NumInEdges(0),
        StoredInHash(false), Direct(direct), AddressTaken(false),
        NodeRep(SelfRep), Timestamp(0) { }

    Node *setValue(llvm::Value *V) {
      assert(Val == 0 && "Value already set for this node!");
      Val = V;
      return this;
    }

    /// getValue - Return the LLVM value corresponding to this node.
    ///
    llvm::Value *getValue() const { return Val; }

    /// addPointerTo - Add a pointer to the list of pointees of this node,
    /// returning true if this caused a new pointer to be added, or false if
    /// we already knew about the points-to relation.
    bool addPointerTo(unsigned Node) {
      return PointsTo->test_and_set(Node);
    }

    /// intersects - Return true if the points-to set of this node intersects
    /// with the points-to set of the specified node.
    bool intersects(Node *N) const;

    /// intersectsIgnoring - Return true if the points-to set of this node
    /// intersects with the points-to set of the specified node on any nodes
    /// except for the specified node to ignore.
    bool intersectsIgnoring(Node *N, unsigned) const;

    // Timestamp a node (used for work list prioritization)
    void Stamp() {
      Timestamp = llvm::sys::AtomicIncrement(&Counter);
      --Timestamp;
    }

    bool isRep() const {
      return (static_cast<int>(NodeRep) < 0);
    }
  };

  struct WorkListElement {
    Node* node;
    unsigned Timestamp;
    WorkListElement(Node* n, unsigned t) : node(n), Timestamp(t) {}

    // Note that we reverse the sense of the comparison because we
    // actually want to give low timestamps the priority over high,
    // whereas priority is typically interpreted as a greater value is
    // given high priority.
    bool operator<(const WorkListElement& that) const {
      return( this->Timestamp > that.Timestamp );
    }
  };

  // Priority-queue based work list specialized for Nodes.
  class WorkList {
    std::priority_queue<WorkListElement> Q;

   public:
    void insert(Node* n) {
      Q.push(WorkListElement(n, n->Timestamp));
    }

    // We automatically discard non-representative nodes and nodes
    // that were in the work list twice (we keep a copy of the
    // timestamp in the work list so we can detect this situation by
    // comparing against the node's current timestamp).
    Node* pop() {
      while (!Q.empty()) {
        WorkListElement x = Q.top(); Q.pop();
        Node* INode = x.node;

        if (INode->isRep() &&
           INode->Timestamp == x.Timestamp) {
          return(x.node);
        }
      }
      return 0;
    }

    bool empty() {
      return Q.empty();
    }
  };

  /// GraphNodes - This vector is populated as part of the object
  /// identification stage of the analysis, which populates this vector with a
  /// node for each memory object and fills in the ValueNodes map.
  std::vector<Node> GraphNodes;

  /// ValueNodes - This map indicates the Node that a particular Value* is
  /// represented by.  This contains entries for all pointers.
  llvm::DenseMap<llvm::Value*, unsigned> ValueNodes;

  /// ObjectNodes - This map contains entries for each memory object in the
  /// program: globals, alloca's and mallocs.
  llvm::DenseMap<llvm::Value*, unsigned> ObjectNodes;

  /// ReturnNodes - This map contains an entry for each function in the
  /// program that returns a value.
  llvm::DenseMap<llvm::Function*, unsigned> ReturnNodes;

  /// VarargNodes - This map contains the entry used to represent all pointers
  /// passed through the varargs portion of a function call for a particular
  /// function.  An entry is not present in this map for functions that do not
  /// take variable arguments.
  llvm::DenseMap<llvm::Function*, unsigned> VarargNodes;


  /// Constraints - This vector contains a list of all of the constraints
  /// identified by the program.
  std::vector<Constraint> Constraints;

  // Map from graph node to maximum K value that is allowed (for functions,
  // this is equivalent to the number of arguments + CallFirstArgPos)
  std::map<unsigned, unsigned> MaxK;

  /// This enum defines the GraphNodes indices that correspond to important
  /// fixed sets.
  enum {
    UniversalSet = 0,
    NullPtr      = 1,
    NullObject   = 2,
    NumberSpecialNodes
  };

  unsigned IntNode;
  unsigned AggregateNode;  // for extractvalue and insertvalue
  unsigned PthreadSpecificNode;
  // Stack for Tarjan's
  std::stack<unsigned> SCCStack;
  // Map from Graph Node to DFS number
  std::vector<unsigned> Node2DFS;
  // Map from Graph Node to Deleted from graph.
  std::vector<bool> Node2Deleted;
  // Same as Node Maps, but implemented as std::map because it is faster to
  // clear
  std::map<unsigned, unsigned> Tarjan2DFS;
  std::map<unsigned, bool> Tarjan2Deleted;
  // Current DFS number
  unsigned DFSNumber;

  // Work lists.
  WorkList w1, w2;
  WorkList *CurrWL, *NextWL;  // "current" and "next" work lists

  // Offline variable substitution related things

  // Temporary rep storage, used because we can't collapse SCC's in the
  // predecessor graph by uniting the variables permanently, we can only do so
  // for the successor graph.
  std::vector<unsigned> VSSCCRep;
  // Mapping from node to whether we have visited it during SCC finding yet.
  std::vector<bool> Node2Visited;
  std::vector<bool> Node3Visited;
  // During variable substitution, we create unknowns to represent the unknown
  // value that is a dereference of a variable.  These nodes are known as
  // "ref" nodes (since they represent the value of dereferences).
  unsigned FirstRefNode;
  // During HVN, we create represent address taken nodes as if they were
  // unknown (since HVN, unlike HU, does not evaluate unions).
  unsigned FirstAdrNode;
  // Current pointer equivalence class number
  unsigned PEClass;
  // Mapping from points-to sets to equivalence classes
  typedef llvm::DenseMap<llvm::SparseBitVector<> *, unsigned, BitmapKeyInfo>
    BitVectorMap;
  BitVectorMap Set2PEClass;
  // Mapping from pointer equivalences to the representative node.  -1 if we
  // have no representative node for this pointer equivalence class yet.
  std::vector<int> PEClass2Node;
  // Mapping from pointer equivalences to representative node.  This includes
  // pointer equivalent but not location equivalent variables. -1 if we have
  // no representative node for this pointer equivalence class yet.
  std::vector<int> PENLEClass2Node;
  // Union/Find for HCD
  std::vector<unsigned> HCDSCCRep;
  // HCD's offline-detected cycles; "Statically DeTected"
  // -1 if not part of such a cycle, otherwise a representative node.
  std::vector<int> SDT;
  // Whether to use SDT (UniteNodes can use it during solving, but not before)
  bool SDTActive;

 public:
  static char ID;
  Andersens() : ModulePass(ID) {}

  virtual void *getAdjustedAnalysisPointer(llvm::AnalysisID PI) {
    if (PI == &AliasAnalysis::ID) {
      return reinterpret_cast<llvm::AliasAnalysis *>(this);
    }
    return this;
  }

  static bool isMallocCall(const llvm::Value *V) {
    const llvm::CallInst *CI = llvm::dyn_cast<llvm::CallInst>(V);
    if (!CI) {
      return false;
    }

    llvm::Function *Callee = CI->getCalledFunction();
    if (Callee == 0 || !Callee->isDeclaration()) {
      return false;
    }

    if (Callee->getName() != "malloc" &&
        Callee->getName() != "calloc" &&
        Callee->getName() != "valloc" &&
        Callee->getName() != "realloc" &&
        Callee->getName() != "memalign" &&
        Callee->getName() != "fopen" &&
        Callee->getName() != "_Znwj" &&  // operator new(unsigned int)
        Callee->getName() != "_Znwm" &&  // operator new(unsigned long)
        Callee->getName() != "_Znaj" &&  // operator new[](unsigned int)
        Callee->getName() != "_Znam") {  // operator new[](unsigned long)
      return false;
    }

    // ddevec (not really)  - TODO: check prototype
    return true;
  }

  bool runOnModule(llvm::Module &M) {
    // We don't run Andersens as a classic AA, so we disable this call
    // InitializeAliasAnalysis(this);
    IdentifyObjects(M);
    CollectConstraints(M);
#undef DEBUG_TYPE
#define DEBUG_TYPE "anders-aa-constraints"
    DEBUG(PrintConstraints());
#undef DEBUG_TYPE
#define DEBUG_TYPE "anders-aa"
    SolveConstraints();
    DEBUG(PrintPointsToGraph());

    // Free the constraints list, as we don't need it to respond to alias
    // requests.
    std::vector<Constraint>().swap(Constraints);
    // These are needed for Print() (-analyze in opt)
    // ObjectNodes.clear();
    // ReturnNodes.clear();
    // VarargNodes.clear();
    return false;
  }

  void releaseMemory() {
    // FIXME: Until we have transitively required passes working correctly,
    // this cannot be enabled!  Otherwise, using -count-aa with the pass
    // causes memory to be freed too early. :(
#if 0
    // The memory objects and ValueNodes data structures at the only ones that
    // are still live after construction.
    std::vector<Node>().swap(GraphNodes);
    ValueNodes.clear();
#endif
  }

  /*
  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AliasAnalysis::getAnalysisUsage(AU);
    AU.setPreservesAll();                         // Does not transform code
  }
  */

  //------------------------------------------------
  // Implement the AliasAnalysis API
  //
  AliasAnalysis::AliasResult alias(const AliasAnalysis::Location &L1,
      const AliasAnalysis::Location &L2);
  virtual AliasAnalysis::ModRefResult getModRefInfo(llvm::ImmutableCallSite CS,
                                     const llvm::AliasAnalysis::Location &Loc);
  virtual AliasAnalysis::ModRefResult getModRefInfo(llvm::ImmutableCallSite CS1,
                                     llvm::ImmutableCallSite CS2);
  void getMustAliases(llvm::Value *P, std::vector<llvm::Value*> &RetVals);
  // Do not use it.
  bool pointsToConstantMemory(const AliasAnalysis::Location &Loc,
      bool OrLocal = false);

  virtual void deleteValue(llvm::Value *V) {
    ValueNodes.erase(V);
    getAnalysis<AliasAnalysis>().deleteValue(V);
  }

  virtual void copyValue(llvm::Value *From, llvm::Value *To) {
    ValueNodes[To] = ValueNodes[From];
    getAnalysis<AliasAnalysis>().copyValue(From, To);
  }

  const llvm::SparseBitVector<> &getPointsTo(const llvm::Value *val) const {
    auto node = getNode(const_cast<llvm::Value*>(val));

    auto fnode = FindNode(node);

    return *GraphNodes[fnode].PointsTo;
  }

  unsigned valRep(const llvm::Value *val) const {
    return FindNode(getNode(const_cast<llvm::Value*>(val)));
  }

  unsigned val(const llvm::Value *val) const {
    return getNode(const_cast<llvm::Value*>(val));
  }

  unsigned obj(const llvm::Value *val) const {
    return getObject(const_cast<llvm::Value*>(val));
  }

  const llvm::DenseMap<llvm::Value *, unsigned int> &getObjectMap() const {
    return ObjectNodes;
  }

 private:
  /// getNode - Return the node corresponding to the specified pointer scalar.
  ///
  unsigned getNode(llvm::Value *V) const {
    if (llvm::Constant *C = llvm::dyn_cast<llvm::Constant>(V))
      if (!llvm::isa<llvm::GlobalValue>(C))
        return getNodeForConstantPointer(C);

    llvm::DenseMap<llvm::Value*, unsigned>::const_iterator I =
      ValueNodes.find(V);
    if (I == ValueNodes.end()) {
#ifndef NDEBUG
      V->dump();
#endif
      llvm_unreachable("Value does not have a node in the points-to graph!");
    }
    return I->second;
  }

  /// getObject - Return the node corresponding to the memory object for the
  /// specified global or allocation instruction.
  unsigned getObject(llvm::Value *V) const {
    llvm::DenseMap<llvm::Value*, unsigned>::const_iterator I =
      ObjectNodes.find(V);
    assert(I != ObjectNodes.end() &&
           "Value does not have an object in the points-to graph!");
    return I->second;
  }

  /// getReturnNode - Return the node representing the return value for the
  /// specified function.
  unsigned getReturnNode(llvm::Function *F) const {
    llvm::DenseMap<llvm::Function*, unsigned>::const_iterator I =
      ReturnNodes.find(F);
    assert(I != ReturnNodes.end() && "Function does not return a value!");
    return I->second;
  }

  /// getVarargNode - Return the node representing the variable arguments
  /// formal for the specified function.
  unsigned getVarargNode(llvm::Function *F) const {
    llvm::DenseMap<llvm::Function*, unsigned>::const_iterator I =
      VarargNodes.find(F);
    assert(I != VarargNodes.end() && "Function does not take var args!");
    return I->second;
  }

  /// getNodeValue - Get the node for the specified LLVM value and set the
  /// value for it to be the specified value.
  unsigned getNodeValue(llvm::Value &V) {
    unsigned Index = getNode(&V);
    GraphNodes[Index].setValue(&V);
    return Index;
  }

  unsigned UniteNodes(unsigned First, unsigned Second,
                      bool UnionByRank = true);
  unsigned FindNode(unsigned Node);
  unsigned FindNode(unsigned Node) const;

  void IdentifyObjects(llvm::Module &M);
  void CollectConstraints(llvm::Module &M);
  bool AnalyzeUsesOfFunction(llvm::Value *);
  void CreateConstraintGraph();
  void OptimizeConstraints();
  unsigned FindEquivalentNode(unsigned, unsigned);
  void ClumpAddressTaken();
  void RewriteConstraints();
  void HU();
  void HVN();
  void HCD();
  void Search(unsigned Node);
  void UnitePointerEquivalences();
  void SolveConstraints();
  bool QueryNode(unsigned Node);
  void Condense(unsigned Node);
  void HUValNum(unsigned Node);
  void HVNValNum(unsigned Node);
  unsigned getNodeForConstantPointer(llvm::Constant *C) const;
  unsigned getNodeForConstantPointerTarget(llvm::Constant *C);
  void AddGlobalInitializerConstraints(unsigned, llvm::Constant *C);

  void AddConstraintsForNonInternalLinkage(llvm::Function *F);
  void AddConstraintsForCall(llvm::CallSite CS, llvm::Function *F);
  bool AddConstraintsForExternalCall(llvm::CallSite CS, llvm::Function *F);
  void AddConstraintForStruct(llvm::Value *V);
  void AddConstraintForConstantPointer(llvm::Value *V);


  void PrintNode(const Node *N) const;
  void PrintConstraints() const;
  void PrintConstraint(const Constraint &) const;
  void PrintLabels() const;
  void PrintPointsToGraph() const;

  //===------------------------------------------------------------------===//
  // Instruction visitation methods for adding constraints
  //
  friend class InstVisitor<Andersens>;
  void visitReturnInst(llvm::ReturnInst &RI);
  void visitInvokeInst(llvm::InvokeInst &II) {
    visitCallSite(llvm::CallSite(&II));
  }
  void visitCallInst(llvm::CallInst &CI) { visitCallSite(llvm::CallSite(&CI)); }
  void visitCallSite(llvm::CallSite CS);
  void visitAllocaInst(llvm::AllocaInst &AI);
  void visitLoadInst(llvm::LoadInst &LI);
  void visitStoreInst(llvm::StoreInst &SI);
  void visitGetElementPtrInst(llvm::GetElementPtrInst &GEP);
  void visitPHINode(llvm::PHINode &PN);
  void visitCastInst(llvm::CastInst &CI);
  void visitICmpInst(llvm::ICmpInst &) {}  // NOOP!
  void visitFCmpInst(llvm::FCmpInst &) {}  // NOOP!
  void visitSelectInst(llvm::SelectInst &SI);
  void visitVAArg(llvm::VAArgInst &I);
  void visitIntToPtrInst(llvm::IntToPtrInst &I);
  void visitPtrToIntInst(llvm::PtrToIntInst &I);
  void visitExtractValue(llvm::ExtractValueInst &I);
  void visitInsertValue(llvm::InsertValueInst &I);
  void visitInstruction(llvm::Instruction &I);

  //===------------------------------------------------------------------===//
  // Implement Analyize interface
  //
  void print(llvm::raw_ostream &, const llvm::Module *) const {
    PrintPointsToGraph();
  }
};

#endif  // INCLUDE_ANDERSENS_H_

