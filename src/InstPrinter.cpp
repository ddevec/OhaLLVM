/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/InstPrinter.h"

#include <map>
#include <string>

std::map<const llvm::Instruction *, std::string> InstPrinter::strs_;

