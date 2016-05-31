/*
 * Copyright (C) 2016 David Devecsery
 */

#include "include/SolveHelpers.h"

#include <algorithm>
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

std::vector<bdd> BddPtstoSet::fddCache_;

std::vector<ObjectMap::ObjID> BddPtstoSet::uglyBddVec_;

std::map<uint32_t, std::pair<bool,
  std::shared_ptr<std::vector<ObjectMap::ObjID>>>>
    BddPtstoSet::vecCache_;

// Init function
void BddPtstoSet::bddInit(ObjectMap &omap, const ConstraintGraph &cg) {
  bddInitd_ = true;

  // First, lets run some bdd init functions...
  // We create 2 domains, 1 for the ptsto sets
  //   The other for our possible gep sets
  int domain[2] = { static_cast<int>(omap.getNumObjs()+1),
    static_cast<int>(omap.getNumObjs()+1) };
  llvm::dbgs() << "bdd domain size is: " << omap.getNumObjs()+1 << "\n";

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
  geps_.resize(omap.getNumObjs()+1, bddfalse);

  auto vpts = bvec_varfdd(0);
  auto vgep = bvec_varfdd(1);

  uint32_t pts_bits = vpts.bitnum();
  // Now, construct a mapping of objects to possible geps operations called
  //   on them:
  //
  // To do this, we create a set of valid offsets for each object
  //   (NOTE set held in vector)
  // We construct a set of offsets grabbed by constraints

  // Track max offs for off_to_obj vector size
  std::set<int32_t> valid_offs;
  int32_t max_offs = 0;
  for (auto &pcons : cg) {
    if (pcons->type() == ConstraintType::Copy &&
        pcons->offs() != 0) {
      valid_offs.insert(pcons->offs());
      if (pcons->offs() > max_offs) {
        max_offs = pcons->offs();
      }
    }
  }

  std::vector<std::set<int32_t>> off_to_obj(max_offs+1);

  std::vector<std::pair<ObjectMap::ObjID, int32_t>> struct_sizes(
      std::begin(omap.getIsStructSet()), std::end(omap.getIsStructSet()));

  std::sort(std::begin(struct_sizes), std::end(struct_sizes),
      [] (const std::pair<ObjectMap::ObjID, int32_t> &lhs,
          const std::pair<ObjectMap::ObjID, int32_t> &rhs) {
        return lhs.first < rhs.first;
      });

  // Now handle object sizes
  for (auto &pr : struct_sizes) {
    // Actual size is pr.second - 1 -- pr.second is the object size, the
    // maximum offset is that value minus one
    // NOTE: We can have size 1 and 0 objects... although uncommon.  In that
    // case, ignore them!
    auto size = (pr.second - 1);
    if (size < 0) {
      continue;
    }
    assert(size >= 0);
    auto id = pr.first.val();
    assert(id < omap.getNumObjs());

    // If the size is not a valid offset (then that value can never be found),
    //   reduce the size.
    while (size > 0 && valid_offs.find(size) == std::end(valid_offs)) {
      size--;
    }

    // while (size > 0)
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

  // We then construct an iterable version of object offsets

  // Then, for each offset in that set, we iterate our object ids, and
  //   compute the valid offsets that could be used below that

  // We Make a set of valid offsets (from the CG)
  llvm::dbgs() << "offs size is: " << off_to_obj.size() << "\n";
  bdd off_mask = bddfalse;
  for (auto offs : util::reverse(valid_offs)) {
    assert(static_cast<size_t>(offs) < off_to_obj.size());
    // This can happen in the instance of something like an array offset...
    for (auto off_obj : off_to_obj[offs]) {
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

    geps_[offs] = f & off_mask;
  }
}

//}}}
