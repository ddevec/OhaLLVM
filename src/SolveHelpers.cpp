/*
 * Copyright (C) 2016 David Devecsery
 */

#include "include/SolveHelpers.h"

#include <algorithm>
#include <limits>
#include <map>
#include <set>
#include <utility>
#include <vector>

#include "include/lib/BddSet.h"

// BddPtstoSet statics {{{
bool BddPtstoSet::bddInitd_ = false;
std::vector<bdd> BddPtstoSet::geps_;
bddPair *BddPtstoSet::gepToPts_;
bdd BddPtstoSet::ptsDom_;
std::set<int32_t> BddPtstoSet::validOffs_;

size_t BddPtstoSet::consStartPos_ = 0;
int32_t BddPtstoSet::maxOffs_ = 0;
size_t BddPtstoSet::allocPos_ = 0;

std::vector<bdd> BddPtstoSet::fddCache_;

std::vector<ValueMap::Id> BddPtstoSet::uglyBddVec_;

std::map<uint32_t, std::pair<bool,
  std::shared_ptr<std::vector<ValueMap::Id>>>>
    BddPtstoSet::vecCache_;

// Init function
void BddPtstoSet::bddInit(const Cg &cg) {
  bddInitd_ = true;

  // First, lets run some bdd init functions...
  // We create 2 domains, 1 for the ptsto sets
  //   The other for our possible gep sets
  assert(cg.vals().getMaxAlloc() != ValueMap::Id::invalid());
  auto domain_size = static_cast<int32_t>(cg.vals().getMaxReservedAlloc()) + 1;
  int domain[2] = { domain_size, domain_size };
  llvm::dbgs() << "bdd domain size is: " << domain_size << "\n";

  // In lib/BddSet.cpp
  bdd_init_once(2);

  // We expand the domain to encompass our realm of possible object values
  fdd_extdomain(domain, 2);

  // Get our points to domain for later geps operations
  ptsDom_ = fdd_ithset(0);

  // Also, setup our gep2pts transformation
  gepToPts_ = bdd_newpair();
  fdd_setpair(gepToPts_, 1, 0);

  // Okay, we need to get our geps all ready...
  geps_.resize(domain_size, bddfalse);

  updateGeps(cg);
}

void BddPtstoSet::updateConstraints(const Cg &cg) {
  consStartPos_ = cg.constraints().size();
}

void BddPtstoSet::updateGeps(const Cg &cg) {
  assert(bddInitd_);
  auto &map = cg.vals();

  // Now, construct a mapping of objects to possible geps operations called
  //   on them:
  //
  // To do this, we create a set of valid offsets for each object
  //   (NOTE set held in vector)
  // We construct a set of offsets grabbed by constraints


  auto vpts = bvec_varfdd(0);
  auto vgep = bvec_varfdd(1);

  uint32_t pts_bits = vpts.bitnum();

  // Track max offs for off_to_obj vector size
  int32_t max_offs = 0;

  auto &constraints = cg.constraints();

  bool valid_offs_updated = false;
  for (auto i = consStartPos_; i < constraints.size();
      ++i) {
    auto &cons = constraints[i];
    if (cons.type() == ConstraintType::Copy &&
        cons.offs() != 0) {
      auto rc = validOffs_.emplace(cons.offs());
      if (rc.second) {
        valid_offs_updated = true;
      }

      if (cons.offs() > maxOffs_) {
        maxOffs_ = cons.offs();
      }
    }
  }

  consStartPos_ = constraints.size();

  std::vector<std::unordered_set<int32_t>> off_to_obj(max_offs+1);

  auto &alloc_sizes = map.allocSizes();

  auto alloc_start = allocPos_;
  if (valid_offs_updated) {
    alloc_start = 0;
  }

  // Now handle object sizes
  for (size_t i = alloc_start; i < alloc_sizes.size(); ++i) {
    auto &pr = alloc_sizes[i];
    // NOTE: We can have size 1 and 0 objects... although uncommon.  In that
    // case, ignore them!
    assert(pr.second < std::numeric_limits<int32_t>::max());
    auto size = (static_cast<int32_t>(pr.second));
    if (size < 0) {
      continue;
    }
    assert(size >= 0);
    auto id = pr.first.val();
    // llvm::dbgs() << "Alloc is: " << id << ", size is: " << size << "\n";
    assert(pr.first < map.getMaxAlloc());

    // If the size is not a valid offset (then that value can never be found),
    //   reduce the size.
    while (size > 0 && validOffs_.find(size) == std::end(validOffs_)) {
      size--;
    }

    if (size > 0) {
      if (static_cast<size_t>(size+1) > off_to_obj.size()) {
        off_to_obj.resize(size+1);
      }
      // llvm::dbgs() << "off_to_obj[" << size << "].insert(" << id << ")\n";
      off_to_obj[size].insert(id);

      /*
      size--;
      while (size > 0 && valid_offs.find(size) == std::end(valid_offs)) {
        size--;
      }
      */
    }
  }

  allocPos_ = alloc_sizes.size();

  // We then construct an iterable version of object offsets

  // Then, for each offset in that set, we iterate our object ids, and
  //   compute the valid offsets that could be used below that

  // We Make a set of valid offsets (from the CG)
  llvm::dbgs() << "offs size is: " << off_to_obj.size() << "\n";
  bdd off_mask = bddfalse;
  for (auto &offs : util::reverse(validOffs_)) {
    // assert(static_cast<size_t>(offs) < off_to_obj.size());
    if (static_cast<size_t>(offs) >= off_to_obj.size()) {
      continue;
    }
    // This can happen in the instance of something like an array offset...
    for (auto &off_obj : off_to_obj[offs]) {
      off_mask |= getFddVar(off_obj);
      /*
      if (off_obj == 457) {
        llvm::dbgs() << "off_mask is: ";
        for (auto elm : *getBddVec(off_mask)) {
          llvm::dbgs() << " " << elm;
        }
        llvm::dbgs() << "\n";
      }
      */
    }

    // bdd vector for pts + offs
    auto add = bvec_add(vpts, bvec_con(pts_bits, offs));

    // Map addr into gep domain
    bdd f = bvec_equ(vgep, add);

    geps_[offs] |= f & off_mask;
  }
  llvm::dbgs() << "geps_ loop done\n";
}

//}}}
