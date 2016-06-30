#include <stdlib.h>
#include <stdio.h>
#include <string.h>

const char *g_str = "Hello";

struct foo {
  const char *str;
  int ret;
};

void *do_malloc(size_t size) {
  return malloc(size);
}

void do_print(const char *str) {
  printf(str);
}

int main(void) {
  struct foo main_foo;
  main_foo.str = g_str;
  main_foo.ret = EXIT_SUCCESS;

  void *(*my_malloc)(size_t) = do_malloc;
  void *(*my_malloc2)(size_t) = malloc;
  void (*my_print)(const char *) = do_print;

  const char *a = g_str;
  do_print(a);

  char *b = my_malloc(strlen(g_str));
  strcpy(b, a);
  
  my_print(b);

  char *b2 = my_malloc(strlen(g_str));
  strcpy(b2, a);
  
  my_print(b2);

  char *c = my_malloc2(strlen(g_str));
  strcpy(c, a);
  my_print(c);
  

  
  return main_foo.ret;
}


