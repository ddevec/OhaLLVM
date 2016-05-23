#include <fcntl.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

uint64_t glbl_int = 8;

int main(int argc, char **argv) {
  uint64_t i = 4;
  uint64_t *local_pint = &i;
  // First, run a conditional statement that will fail...
  if (argc == 2 && !strcmp(argv[1], "full")) {
    // Setup global alias
    local_pint = &glbl_int;
  }

  {
    int j;
    for (j = 0; j < (1<<30); j++) {
      *local_pint += j;
    }
  }

  printf("local is: %" PRIu64 "\n", *local_pint);

  return EXIT_SUCCESS;
}
