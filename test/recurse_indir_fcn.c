#include <stdlib.h>
#include <stdio.h>
#include <string.h>

const char *g_str = "Hello";
char glbl_mem[1000];

struct foo {
  const char *str;
  int ret;
};

void *glbl_malloc(size_t size) {
  return (void *)glbl_mem;
}

void *fib1() {
}

int main(int argc, char **argv) {
  struct foo main_foo;
  main_foo.str = g_str;
  main_foo.ret = EXIT_SUCCESS;

  void *(*my_malloc)(size_t);
  if (argv[1] == "malloc") {
    my_malloc = malloc;
  } else {
    my_malloc = glbl_malloc;
  }

  const char *a = g_str;
  do_print(a);

  char *b = my_malloc(strlen(g_str));
  strcpy(b, a);
  
  do_print(b);
  
  return main_foo.ret;
}


