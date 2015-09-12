#include <string.h>
#include <stdlib.h>
#include <stdio.h>

int main(void) {
  char *homedir;

  homedir = getenv("HOME");

  printf(homedir);

  return EXIT_SUCCESS;
}
