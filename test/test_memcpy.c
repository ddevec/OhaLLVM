#include <string.h>
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

  memcpy(&g_hw, hw, sizeof(g_hw));

  // Should point to g_str1
  printf(g_hw.str1);
  // Should point to g_str2
  printf(g_hw.str2);

  char *tmp_str;

  memcpy(&tmp_str, &g_str2, sizeof(tmp_str));

  printf(tmp_str);

  return EXIT_SUCCESS;
}
