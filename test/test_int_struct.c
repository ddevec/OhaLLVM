#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void *my_alloc(size_t);
void *my_calloc(size_t, size_t);
void my_free(void *);

struct my_struct {
  int32_t w_bits;
  int32_t w_bits2;
};

struct call_struct {
  int bleh;
  void (*free)(void *);
  void *(*alloc)(size_t);
} calls = {0, free, my_alloc};

void *my_alloc(size_t size) {
  void *ret = malloc(size);

  if (ret == NULL) {
    fprintf(stderr, "Failed to alloc\n");
    exit(EXIT_FAILURE);
  }

  return ret;
}

int32_t g_num = 0;

int main(void) {
  struct my_struct *vals1 = calls.alloc(sizeof(struct my_struct));

  vals1->w_bits = 1;
  vals1->w_bits2 = 2;

  printf("vals1: %d, %d\n", vals1->w_bits, vals1->w_bits2);

  calls.free(vals1);

  return EXIT_SUCCESS;
}

