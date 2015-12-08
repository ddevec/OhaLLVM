/*
 * Copyright (C) 2015 David Devecsery
 */

#include <cstdlib>
#include <cstdio>

#include <iostream>
#include <fstream>
#include <list>
#include <map>
#include <set>
#include <string>
#include <sstream>
#include <unordered_map>
#include <vector>

int main(int argc, char **argv) {
  if (argc == 0) {
    std::cerr << "ERROR: Usage: " << argv[0] << " <input files>" << std::endl;
  }

  std::unordered_map<int32_t, std::set<int32_t>> valid_to_objids;

  for (int i = 1; i < argc; i++) {
    std::string filename(argv[i]);

    std::ifstream logfile(filename);

    if (logfile.is_open()) {
      for (std::string line ; std::getline(logfile, line, ':'); ) {
        int32_t call_id = stoi(line);

        auto &fcn_set = valid_to_objids[call_id];

        std::getline(logfile, line);
        std::stringstream converter(line);

        int32_t fcn_id;
        converter >> fcn_id;
        while (!converter.fail()) {
          fcn_set.insert(fcn_id);
          converter >> fcn_id;
        }
      }
    } else {
      std::cerr << "Couldn't open input file: " << filename << std::endl;
      exit(EXIT_FAILURE);
    }
  }

  // Print to the logfile
  for (auto &val_pr : valid_to_objids) {
    std::cout << val_pr.first << ":";

    for (auto &obj_id : val_pr.second) {
      std::cout << " " << obj_id;
    }
    std::cout << std::endl;
  }
}

