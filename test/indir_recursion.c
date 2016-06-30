#include <stdlib.h>
#include <stdio.h>
#include <string.h>

// FIXME: My alias analysis doesn't liek mallocs without at least one struct
//     def...
struct bleh {
  int32_t a;
};

const char *g_str = "Hello";


char glbl_buffer[1000];
void *do_glbl_buffer(size_t size) {
  return (void *)glbl_buffer;
}

void *do_alloc(size_t size) {
  return malloc(size);
}

int *do_fib1(int, void *(*)(size_t));

int *do_fib_m1(int count, void *(*alloc)(size_t)) {
  return do_fib1(count - 1, alloc);
}

int *do_fib_m2(int count, void *(*alloc)(size_t)) {
  return do_fib1(count - 2, alloc);
}

int *(*ind_fib1)(int, void *(*)(size_t)) = do_fib_m1;
int *(*ind_fib2)(int, void *(*)(size_t)) = do_fib_m2;

int *do_fib1(int count, void *(*alloc)(size_t)) {
  int *data = alloc(sizeof(int));

  if (count == 2) {
    *data = 1;
  }

  if (count == 1) {
    *data = 2;
  }

  int *res1 = ind_fib1(count, alloc);
  int *res2 = ind_fib2(count, alloc);

  *data = *res1 + *res2;

  free(res1);
  free(res2);

  return data;
}

int main(void) {
  struct bleh b1;
  b1.a = EXIT_SUCCESS;

  int *glb_fib1 = do_fib1(1, do_glbl_buffer);
  int *glb_fib2 = do_fib1(1, do_glbl_buffer);
  int *mal_fib1 = do_fib1(1000, do_alloc);
  int *mal_fib2 = do_fib1(1000, do_alloc);
  
  return b1.a;
}


