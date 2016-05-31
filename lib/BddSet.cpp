/*
 * Copyright (C) 2015 David Devecsery
 */

#include "lib/BddSet.h"

#include <bdd.h>
#include <bvec.h>
#include <fdd.h>

static bool bdd_initd = false;

int32_t g_num_doms = 0;

void bdd_init_once(int num_doms) {
  g_num_doms += num_doms;
  if (bdd_initd) {
    return;
  }
  bdd_initd = true;

  // Now, we initialize the bdd library
  bdd_init((1<<23), 1000);

  // We set some performance variables
  bdd_setcacheratio(8);
  bdd_setminfreenodes(40);
  bdd_setmaxnodenum(0);
  bdd_gbc_hook(NULL);

  // We disable reordering, because we rely on ordering
  bdd_disable_reorder();
}
