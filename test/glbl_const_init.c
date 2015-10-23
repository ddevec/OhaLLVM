#include <stdlib.h>
#include <stdio.h>

struct hello_world {
  const char *str1;
  const char *str2;
  void (*do_print)(const char *);
};


const char *g_str1 = "hello";
const char *g_str2 = " world!\n";

static void print(const char *p) {
  printf(p);
}

static void print2(const char *p) {
  printf(p);
  printf(p);
}

struct hello_world g_hw = {
  .str1 = "hello", 
  .str2 = "world!\n", 
  .do_print = print
};

struct hello_world hw_arr[] = {
  {"hello", "world!\n", print},
  {"again, ", "hello!\n", print2}
};

int main(int argc, char **argv) {
  g_hw.do_print = print;

  int num = atoi(argv[1]);

  for (int i = 0; i < num; i++) {
    const char *str1 = hw_arr[i].str1;
    const char *str2 = hw_arr[i].str2;
    void (*func)(const char *) = hw_arr[i].do_print;
    func(str1);
    func(str2);
  }

  return EXIT_SUCCESS;
}
