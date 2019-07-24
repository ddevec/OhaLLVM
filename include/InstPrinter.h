/*
 * Copyright (C) 2015 David Devecsery
 */

#ifndef INCLUDE_INSTPRINTER_H_
#define INCLUDE_INSTPRINTER_H_

#include <map>
#include <string>

#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

class FullInstPrinter;
class InstPrinter { //{{{
 public:
    InstPrinter(const llvm::Instruction *pinst) {
      auto it = strs_.find(pinst);
      if (it == std::end(strs_)) {
        std::string s;
        llvm::raw_string_ostream ss(s);

        ss << *pinst;

        auto rc = strs_.emplace(pinst, ss.str());

        assert(rc.second);
        it = rc.first;
      }

      str_ = &it->second;
    }

    operator std::string&() { return *str_; }

 private:
  friend class FullInstPrinter;

  std::string *str_;
  static std::map<const llvm::Instruction *, std::string> strs_;
};
//}}}

class FullInstPrinter { //{{{
 public:
    FullInstPrinter(const llvm::Instruction *pinst) {
      auto it = InstPrinter::strs_.find(pinst);
      if (it == std::end(InstPrinter::strs_)) {
        std::string s;
        llvm::raw_string_ostream ss(s);

        ss << *pinst;

        auto rc = InstPrinter::strs_.emplace(pinst, ss.str());

        assert(rc.second);
        it = rc.first;
      }

      auto bb = pinst->getParent();
      auto fcn = bb->getParent();
      str_ = fcn->getName().str() + ": " + bb->getName().str() + ":" + it->second;
    }

    operator std::string&() { return str_; }

 private:
  std::string str_;
};

#endif  // INCLUDE_INSTPRINTER_H_

