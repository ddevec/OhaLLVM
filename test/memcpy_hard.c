#include <string.h>
#include <stdlib.h>
#include <stdio.h>

struct hello_world {
  char *str1;
  char *str2;
} g_hw;

void *my_alloc1(size_t size) {
  return malloc(size);
}

void *my_alloc2(size_t size) {
  void *ret = my_alloc1(size);
  if (ret == NULL) {
    exit(EXIT_FAILURE);
  }

  return ret;
}

void my_free1(void *ptr) {
  free(ptr);
}

void my_free2(void *ptr) {
  if (ptr == NULL) {
    exit(EXIT_FAILURE);
  }

  my_free1(ptr);
}

void *my_calloc1(size_t s1, size_t s2) {
  return calloc(s1, s2);
}

void *my_calloc2(size_t s1, size_t s2) {
  void *ret = my_calloc1(s1, s2);
  if (ret == NULL) {
    exit(EXIT_FAILURE);
  }

  return ret;
}

struct fcn_ptrs {
  const char *name;
  void *(*alloc)(size_t);
  void (*free)(void *);
  void *(*calloc)(size_t, size_t);
  int32_t bleh;
} my_fcn_ptrs[] = {
  { "libc", malloc, free, calloc, 0 },
  { "my1", my_alloc1, my_free1, my_calloc1, 0 },
  { "my2", my_alloc2, my_free2, my_calloc2, 0 }
};


char *g_str1 = "hello";
char *g_str2 = " world!\n";

int main(void) {
  
  struct fcn_ptrs *p = my_alloc2(sizeof(struct fcn_ptrs));

  memcpy(p, &my_fcn_ptrs[1], sizeof(*p));

  g_hw.str1 = g_str1;
  g_hw.str2 = g_str2;

  struct hello_world *g_hw_clone = p->calloc(1, sizeof(g_hw));

  memcpy(g_hw_clone, &g_hw, sizeof(g_hw));

  printf(g_hw_clone->str1);
  printf(g_hw_clone->str2);

  p->free(g_hw_clone);

  my_free2(p);

  return EXIT_SUCCESS;
}

