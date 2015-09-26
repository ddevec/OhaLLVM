/*
 * Copyright (C) 2015 David Devecsery
 */

#include <cstdio>
#include <cassert>

#include <algorithm>
#include <iostream>
#include <set>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

extern int32_t __InstrIndirCalls_fcn_lookup_len;
extern void *__InstrIndirCalls_fcn_lookup_array[];

static std::unordered_multimap<void *, int32_t> addr_to_id_map;
static std::vector<std::set<int32_t>> called_fcns;

extern "C" {
void __InstrIndirCalls_init_inst(void) {
  for (int i = 0; i < __InstrIndirCalls_fcn_lookup_len; i++) {
    // NOTE: Apparently the compiler can map multiple fcn calls to one spot...
    addr_to_id_map.emplace(__InstrIndirCalls_fcn_lookup_array[i], i);
  }

  called_fcns.resize(__InstrIndirCalls_fcn_lookup_len);
}

void __InstrIndirCalls_finish_inst(void) {
  // Print out my stuff...
  // TODO(ddevec) -- Make this relocatable via env variable
  std::string outfilename("indir_fcns.log");
  FILE *out = fopen(outfilename.c_str(), "w");

  for (size_t i = 0; i < called_fcns.size(); i++) {
    auto &set = called_fcns[i];

    fprintf(out, "%zu:", i);

    for (int32_t id : set) {
      fprintf(out, " %d", id);
    }
    fprintf(out, "\n");
  }
  fclose(out);
}

void __InstrIndirCalls_fcn_call(int32_t id, void **addr) {
  auto res_set = addr_to_id_map.equal_range(addr);
  // assert(res_set.first != res_set.second);
  std::for_each(res_set.first, res_set.second,
      [&id] (std::pair<void *, int32_t> res_pr) {
    called_fcns[id].insert(res_pr.second);
  });
}

}
