#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

const char *charset_aliases = NULL;

#define ISSLASH(X) (X == '/')

#define DIRECTORY_SEPARATOR '/'

#define HAVE_WORKING_O_NOFOLLOW 1

const char *g_cp;

void assign_cp(const char **pcp) {
  *pcp = "hello goodbye";
}

static const char *
get_charset_aliases (void)
{
  const char *cp = "hello world";

  if (strcmp(cp, "hello world")) {
    assign_cp(&cp);
    g_cp = "hello goodbye";
  }

  return cp;
}

int main(void) {
  g_cp = "hello world";

  const char *c = get_charset_aliases();

  printf(c);
  printf("\n");
  printf(g_cp);
  printf("\n");

  return EXIT_SUCCESS;
}
