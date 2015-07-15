#include <stdlib.h>
#include <stdio.h>

const char *g_str = "Hello";

void print(const char *str) {
  printf(str);
}

int main(void) {
  const char *a = g_str;
  const char *b = " world!";

  const char *c = a;
  const char *d = c;

  const char *e = b;

  void (*do_pr)(const char *);

  int i;

  do_pr = print;

  for (i = 0; i < 3; i++) {
    do_pr(d);
    d = b;
    do_pr(e);
    e = a;
    do_pr("\n");
    do_pr(a);
    do_pr(d);
    do_pr("\n");
  }
  
  return EXIT_SUCCESS;
}


