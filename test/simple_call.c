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

  print(d);
  d = b;
  print(e);
  e = a;
  print("\n");
  print(a);
  print(d);
  print("\n");
  
  return EXIT_SUCCESS;
}


