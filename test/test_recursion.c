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

int *do_fib1(int);

int *do_fib_m1(int count) {
  return do_fib1(count - 1);
}

int *do_fib_m2(int count) {
  return do_fib1(count - 2);
}

int *do_fib1(int count) {
  int *data = do_alloc(sizeof(int));

  if (count == 2) {
    *data = 1;
  }

  if (count == 1) {
    *data = 2;
  }

  int *res1 = do_fib_m1(count);
  int *res2 = do_fib_m2(count);

  *data = *res1 + *res2;

  free(res1);
  free(res2);

  return data;
}

int main(void) {
  struct bleh b1;
  b1.a = EXIT_SUCCESS;

  int *fib1 = do_fib1(1);
  int *fib2 = do_fib1(1000);
  
  return b1.a;
}


