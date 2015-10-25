#include <string.h>
#include <stdlib.h>
#include <stdio.h>

char *g_str1 = "hello";
char *g_str2 = " world!\n";

int main(int argc, char **argv) {

  char *progname = argv[0];
  char *arg1 = argv[1];

  if (strcmp(argv[0], argv[1])) {
    printf("You didn't input the argname");
  }

  return EXIT_SUCCESS;
}
