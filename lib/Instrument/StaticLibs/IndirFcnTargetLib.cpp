/*
 * Copyright (C) 2015 David Devecsery
 */

#include <sys/types.h>
#include <unistd.h>

#include <cstdio>
#include <cassert>

#include <algorithm>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

extern int32_t __InstrIndirCalls_num_callsites;
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

  called_fcns.resize(__InstrIndirCalls_num_callsites);
}

void __InstrIndirCalls_finish_inst(void) {
  const char *logname = "profile.indir";

  char *envname = getenv("SFS_LOGFILE");
  if (envname != nullptr) {
    logname = envname;
  }

  std::ostringstream outfilename;

  outfilename << logname << "." << getpid();

  // Print out my stuff...
  /*
  // First open and read the file, if it exists
  {
    std::ifstream logfile(outfilename.str());
    if (logfile.is_open()) {
      for (std::string line; std::getline(logfile, line, ':'); ) {
        // First parse the first int till the :
        int32_t call_id = stoi(line);

        auto &fcn_set = called_fcns[call_id];

        std::getline(logfile, line);
        // Now split the line...
        std::stringstream converter(line);
        int32_t fcn_id;
        converter >> fcn_id;
        while (!converter.fail()) {
          fcn_set.insert(fcn_id);
          converter >> fcn_id;
        }
      }
    }
  }
  */

  // Now, create the outfile
  std::ofstream ofil(outfilename.str());

  // Write out counts:
  for (size_t i = 0; i < called_fcns.size(); i++) {
    auto &set = called_fcns[i];

    ofil << i << ":";

    for (int32_t id : set) {
      ofil << " " << id;
    }
    ofil << std::endl;
  }

  /*
  FILE *out = fopen(outfilename.str().c_str(), "w");

  for (size_t i = 0; i < called_fcns.size(); i++) {
    auto &set = called_fcns[i];

    fprintf(out, "%zu:", i);

    for (int32_t id : set) {
      fprintf(out, " %d", id);
    }
    fprintf(out, "\n");
  }
  fclose(out);
  */
}

void __InstrIndirCalls_fcn_call(int32_t id, void *addr) {
  auto res_set = addr_to_id_map.equal_range(addr);
  // assert(res_set.first != res_set.second);
  // std::cout << "array_size is: " << called_fcns.size() << std::endl;
  // std::cout << "id is: " << id << std::endl;
  /*
  if (id == 36) {
    std::cerr << "id: " << id << " addr: " << addr << std::endl;
  }
  */
  std::for_each(res_set.first, res_set.second,
      [&id] (std::pair<void *, int32_t> res_pr) {
    /*
    if (id == 36) {
      std::cerr << "  " << res_pr.second << "\n";
    }
    */
    called_fcns[id].insert(res_pr.second);
  });
}

}
