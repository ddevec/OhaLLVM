#include <stdlib.h>
#include <stdio.h>

char *g_str1 = "hello";
char *g_str2 = " world!\n";

int main(void) {
  char *a = g_str1;

  char *b = g_str2;

  // pab should allow strong updates
  char **pab;

  // Malloc forces weak updates
  char **m = malloc(sizeof(char *));

  // Will cause pts(m) = { &a }
  *m = a;
  // Will cause pts(pab) = { &b }
  pab = &b;

  printf(*m);
  printf(*pab);

  // Will cause pts(m) = { &a, &b } -- Due to weak updates
  *m = b;
  // Will cause pts(pab) = { &a } -- Due to strong udpates
  pab = &a;

  printf(*pab);
  printf(*m);

  return EXIT_SUCCESS;
}
