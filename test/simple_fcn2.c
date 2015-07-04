#include <stdlib.h>
#include <stdio.h>

const char *g_str = "Hello";

int main(void) {
  const char *a = g_str;
  const char *b = " world!";

  const char *c = a;
  const char *d = c;

  const char *e = b;

  printf(d);
  d = b;
  printf(e);
  e = a;
  printf("\n");
  printf(a);
  printf(d);
  printf("\n");
  
  return EXIT_SUCCESS;
}


