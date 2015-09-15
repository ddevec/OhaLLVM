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

static const char *
get_charset_aliases (void)
{
  const char *cp;

  cp = charset_aliases;
  if (cp == NULL)
    {
      const char *dir;
      const char *base = "charset.alias";
      char *file_name;

      /* Make it possible to override the charset.alias location.  This is
         necessary for running the testsuite before "make install".  */
      dir = getenv ("CHARSETALIASDIR");
      if (dir == NULL || dir[0] == '\0')
        dir = NULL;

      /* Concatenate dir and base into freshly allocated file_name.  */
      {
        size_t dir_len = strlen (dir);
        size_t base_len = strlen (base);
        int add_slash = (dir_len > 0 && !ISSLASH (dir[dir_len - 1]));
        file_name = (char *) malloc (dir_len + add_slash + base_len + 1);
        if (file_name != NULL)
          {
            memcpy (file_name, dir, dir_len);
            if (add_slash)
              file_name[dir_len] = DIRECTORY_SEPARATOR;
            memcpy (file_name + dir_len + add_slash, base, base_len + 1);
          }
      }

      if (file_name == NULL)
        /* Out of memory.  Treat the file as empty.  */
        cp = "";
      else
        {
          int fd;

          /* Open the file.  Reject symbolic links on platforms that support
             O_NOFOLLOW.  This is a security feature.  Without it, an attacker
             could retrieve parts of the contents (namely, the tail of the
             first line that starts with "* ") of an arbitrary file by placing
             a symbolic link to that file under the name "charset.alias" in
             some writable directory and defining the environment variable
             CHARSETALIASDIR to point to that directory.  */
          fd = open (file_name,
                     O_RDONLY | (HAVE_WORKING_O_NOFOLLOW ? O_NOFOLLOW : 0));
          if (fd < 0)
            /* File not found.  Treat it as empty.  */
            cp = "";
          else
            {
              FILE *fp;

              fp = fdopen (fd, "r");
              if (fp == NULL)
                {
                  /* Out of memory.  Treat the file as empty.  */
                  close (fd);
                  cp = "";
                }
              else
                {
                  /* Parse the file's contents.  */
                  char *res_ptr = NULL;
                  size_t res_size = 0;

                  for (;;)
                    {
                      int c;
                      char buf1[50+1];
                      char buf2[50+1];
                      size_t l1, l2;
                      char *old_res_ptr;

                      c = getc (fp);
                      if (c == EOF)
                        break;
                      if (c == '\n' || c == ' ' || c == '\t')
                        continue;
                      if (c == '#')
                        {
                          /* Skip comment, to end of line.  */
                          do
                            c = getc (fp);
                          while (!(c == EOF || c == '\n'));
                          if (c == EOF)
                            break;
                          continue;
                        }
                      ungetc (c, fp);
                      if (fscanf (fp, "%50s %50s", buf1, buf2) < 2)
                        break;
                      l1 = strlen (buf1);
                      l2 = strlen (buf2);
                      old_res_ptr = res_ptr;
                      if (res_size == 0)
                        {
                          res_size = l1 + 1 + l2 + 1;
                          res_ptr = (char *) malloc (res_size + 1);
                        }
                      else
                        {
                          res_size += l1 + 1 + l2 + 1;
                          res_ptr = (char *) realloc (res_ptr, res_size + 1);
                        }
                      if (res_ptr == NULL)
                        {
                          /* Out of memory. */
                          res_size = 0;
                          free (old_res_ptr);
                          break;
                        }
                      strcpy (res_ptr + res_size - (l2 + 1) - (l1 + 1), buf1);
                      strcpy (res_ptr + res_size - (l2 + 1), buf2);
                    }
                  fclose (fp);
                  if (res_size == 0)
                    cp = "";
                  else
                    {
                      *(res_ptr + res_size) = '\0';
                      cp = res_ptr;
                    }
                }
            }

          free (file_name);
        }

      charset_aliases = cp;
    }

  return cp;
}

int main(void) {
  const char *c = get_charset_aliases();

  printf(c);

  return EXIT_SUCCESS;
}
