#include <stdlib.h>
#include <stdio.h>

struct hello_world {
  char *str1;
  char *str2;
} g_hw;

char *g_str1 = "hello";
char *g_str2 = " world!\n";

int main(void) {
  struct hello_world *hw = malloc(sizeof(struct hello_world));

  hw->str1 = g_str1;
  hw->str2 = g_str2;

  g_hw.str1 = g_str1;
  g_hw.str2 = g_str2;

  char *a = hw->str1;
  char *b = hw->str2;

  // pab should allow strong updates
  char **pab;

  // Malloc forces weak updates
  char **m = malloc(sizeof(char *));

  // Will cause pts(m) = { &a }
  *m = hw->str1;
  // Will cause pts(pab) = { &b }
  pab = &g_hw.str2;

  printf(*m);
  printf(*pab);

  // Will cause pts(m) = { &a, &b } -- Due to weak updates
  *m = hw->str2;
  // Will cause pts(pab) = { &a } -- Due to strong udpates
  pab = &g_hw.str1;

  printf(*pab);
  printf(*m);

  return EXIT_SUCCESS;
}
