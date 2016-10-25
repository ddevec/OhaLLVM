/*
 * Copyright (C) 2016 David Devecsery
 *
 */

#ifndef INCLUDE_BLOOMHASH_H_
#define INCLUDE_BLOOMHASH_H_

// Bloom hashing:
//
// BloomHasher<num> -- Get hash_num
// BloomHashSet -- The set representing a valid bloom hash

#include <algorithm>
#include <array>
#include <functional>

// #include "include/util.h"

constexpr bool is_power_of_two(size_t x) {
  return x && ((x & (x-1)) == 0);
}

template <typename T>
constexpr size_t bit_sizeof() {
  return sizeof(T) * 8;
}

#ifndef IN_INS
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#endif

struct BloomHasher {
  // Changable
  static const size_t bits = 4096;
  static const size_t num_hashes = 4;

  // Don't change
  static_assert(is_power_of_two(bits), "bits should be power of two");
  static const uint64_t  bit_size = bit_sizeof<uint64_t>();
  static const size_t num_elms = bits / bit_size;

  typedef std::array<uint64_t, num_elms> BloomFilter;

  static const size_t shift_size = 16;
  static_assert(shift_size * num_hashes <= bit_size, "too many hashes");

  static uint64_t mix_hash(uint64_t stack_hash, uint64_t elm_hash) {
    return stack_hash ^= elm_hash + 0x9e3779b9 +
        (stack_hash << 6) + (stack_hash >> 2);
  }

  static void bloom_clear(BloomFilter &filt) {
    std::fill(std::begin(filt), std::end(filt), 0);
  }

  static void bloom_add(BloomFilter &filt, uint64_t hash) {
    for (size_t i = 0; i < num_hashes; i++) {
      auto hash_offs = get_hash_offs(hash, i);

      uint64_t shift = 1ULL << data_shift(hash_offs);
      size_t idx = data_idx(hash_offs);
      filt[idx] |= shift;
    }
  }

  static bool bloom_check(uint64_t data[], uint64_t hash) {
    for (size_t i = 0; i < num_hashes; i++) {
      auto hash_offs = get_hash_offs(hash, i);

      uint64_t elm = data[data_idx(hash_offs)];
      if (((elm >> data_shift(hash_offs)) & 1) == 0) {
        return false;
      }
    }

    return true;
  }


 private:
  static inline size_t data_idx(size_t offs) {
    return offs / bit_size;
  }

  static inline size_t data_shift(size_t offs) {
    return offs % bit_size;
  }

  static inline size_t get_hash_offs(uint64_t hash, size_t num) {
    return (hash >> (num * shift_size)) % bits;
  }

};

#endif  // INCLUDE_BLOOMHASH_H_
