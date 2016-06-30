#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void *my_alloc(size_t);
void *my_calloc(size_t, size_t);
void my_free(void *);

struct my_struct {
  int32_t *w_bits;
  int32_t *w_bits2;
};

struct call_struct {
  void *(*alloc)(size_t);
  void (*free)(void *);
  void *(*calloc)(size_t, size_t);
} calls = {my_alloc, my_free, my_calloc};

void *my_alloc(size_t size) {
  void *ret = malloc(size);

  if (ret == NULL) {
    fprintf(stderr, "Failed to alloc\n");
    exit(EXIT_FAILURE);
  }

  return ret;
}

void *my_calloc(size_t size, size_t num) {
  void *ret = malloc(size * num);
  if (ret == NULL) {
    fprintf(stderr, "Failed to alloc\n");
    exit(EXIT_FAILURE);
  }

  memset(ret, 0, size * num);

  return ret;
}

void my_free(void *to_free) {
  if (to_free == NULL) {
    fprintf(stderr, "Tried to free NULL\n");
    exit(EXIT_FAILURE);
  }

  free(to_free);
}

int32_t g_num = 0;

struct my_struct *do_thing(void) {
  struct my_struct *vals = calls.alloc(sizeof(struct my_struct));

  vals->w_bits = malloc(sizeof(int32_t));
  *vals->w_bits = g_num;
  g_num += 100;
  vals->w_bits2 = &g_num;
  g_num += 100;

  return vals;
}

int main(void) {
  struct my_struct *vals1 = do_thing();
  struct my_struct *vals2 = do_thing();

  printf("vals1: %d, %d\n", *vals1->w_bits, *vals1->w_bits2);
  printf("vals2: %d, %d\n", *vals2->w_bits, *vals2->w_bits2);

  calls.free(vals1);
  calls.free(vals2);

  return EXIT_SUCCESS;
}

