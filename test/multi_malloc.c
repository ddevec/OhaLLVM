#include <stdlib.h>
#include <stdio.h>
#include <string.h>

// FIXME: My alias analysis doesn't liek mallocs without at least one struct
//     def...
struct bleh {
  int32_t a;
};

const char *g_str = "Hello";

void *do_alloc(size_t size) {
  return malloc(size);
}

int main(void) {
  char *chr1 = do_alloc(30);
  char *chr2 = do_alloc(30);
  struct bleh b1;
  b1.a = EXIT_SUCCESS;

  strcpy(chr1, "hello");
  strcpy(chr2, " world!");

  printf(chr1);
  printf(chr2);
  
  return b1.a;
}


