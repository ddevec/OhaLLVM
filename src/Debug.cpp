/*
 * Copyright (C) 2015 David Devecsery
 */

#include "include/Debug.h"

null_ostream null_ostream::nullstream_;

null_ostream &null_ostream::nullstream() {
  return nullstream_;
}

