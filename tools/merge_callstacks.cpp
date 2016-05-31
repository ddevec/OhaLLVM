/*
 * Copyright (C) 2015 David Devecsery
 */

#include <cstdlib>
#include <cstdio>

#include <fstream>
#include <iostream>
#include <iterator>
#include <list>
#include <map>
#include <set>
#include <string>
#include <sstream>
#include <unordered_map>
#include <vector>

int main(int argc, char **argv) {
  if (argc == 1) {
    std::cerr << "ERROR: Usage: " << argv[0] << " <input files>" << std::endl;
  }

  std::set<std::vector<int32_t>> stacks;

  // For each input file
  for (int i = 1; i < argc; i++) {
    std::string filename(argv[i]);

    std::ifstream logfile(filename);

    // Read in all inputs from that file
    if (logfile.is_open()) {
      for (std::string line; std::getline(logfile, line);) {
        std::stringstream converter(line);

        // Add the new elements to stacks
        stacks.emplace(
            std::istream_iterator<int32_t>(converter),
            std::istream_iterator<int32_t>());
      }
    } else {
      std::cerr << "Couldn't open input file: " << filename << std::endl;
      exit(EXIT_FAILURE);
    }
  }

  // Print to the logfile
  for (auto &stack : stacks) {
    auto it = std::begin(stack);
    auto en = std::end(stack);
    if (it == en) {
      continue;
    }

    std::cout << *it;
    ++it;

    for (; it != en; ++it) {
      std::cout << " " << *it;
    }
    std::cout << std::endl;
  }
}

