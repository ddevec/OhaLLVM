/*
 * Copyright (C) 2016 David Devecsery
 */

#include <sys/types.h>
#include <unistd.h>

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

#include <algorithm>
#include <fstream>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <mutex>
#include <thread>
#include <unordered_map>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

// We have a set of counter variables
static std::mutex count_lock;
static std::vector<size_t> counts;

extern "C" {

void __DynEdge_do_finish() {
  const char *logname = "profile.edge";

  char *envname = getenv("SFS_LOGFILE");
  if (envname != nullptr) {
    logname = envname;
  }

  std::ostringstream outfilename;

  outfilename << logname << "." << getpid();

  std::ofstream ofil(outfilename.str());

  std::unique_lock<std::mutex> lk(count_lock);

  // Write out counts:
  for (size_t i = 0; i < counts.size(); ++i) {
    ofil << i << " " << counts[i] << std::endl;
  }
}

void __DynEdge_do_init() {
}

void __DynEdge_do_visit(int32_t id) {
  // Thread safety n all
  std::unique_lock<std::mutex> lk(count_lock);
  assert(id >= 0);
  if (static_cast<size_t>(id) >= counts.size()) {
    counts.resize(id+1);
  }

  counts[id]++;
}

}
