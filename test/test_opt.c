
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>

int *g_jptr;

void fixup_j(int val) {
  while (val > 0) {
    *g_jptr *= val;
    val--;
  }
}

int main(void) {
  int j[10];
  int i;
  g_jptr = &j[0];
  for (i = 0; i < 100; i++) {
    *g_jptr += i;

    fixup_j(i);

    g_jptr += i % 10;
  }

  return EXIT_SUCCESS;
}


