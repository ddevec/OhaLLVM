/*
 * Allocation functions taken from SPEC2007 sphinx
 */


#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define E_FATAL(...) exit(EXIT_FAILURE)

typedef int32_t int32;

typedef struct mylist_s {
    char **freelist;        	/* ptr to first element in freelist */
    struct mylist_s *next;        /* Next linked list */
    int32 elemsize;        	/* #(char *) in element */
    int32 blocksize;        	/* #elements to alloc if run out of free elments */
    int32 blk_alloc;        	/* #Alloc operations before increasing blocksize */
} mylist_t;
static mylist_t *head = NULL;

#define MIN_MYALLOC        50	/* Min #elements to allocate in one block */
char *__mymalloc__ (int32 elemsize, char *caller_file, int32 caller_line)
{
  char *cp;
  int32 j;
  char **cpp;
  mylist_t *prev, *list;

  /* Find list for elemsize, if existing */
  prev = NULL;
  for (list = head; list && (list->elemsize != elemsize); list = list->next)
    prev = list;

  if (! list) {
    /* New list element size encountered, create new list entry */
    if ((elemsize % sizeof(void *)) != 0)
      E_FATAL("List item size (%d) not multiple of sizeof(void *)\n", elemsize);

    list = (mylist_t *) calloc (1, sizeof(mylist_t));
    list->freelist = NULL;
    list->elemsize = elemsize;
    list->blocksize = MIN_MYALLOC;
    list->blk_alloc = (1<<18) / (list->blocksize * elemsize);

    /* Link entry at head of list */
    list->next = head;
    head = list;
  } else if (prev) {
    /* List found; move entry to head of list */
    prev->next = list->next;
    list->next = head;
    head = list;
  }

  /* Allocate a new block if list empty */
  if (list->freelist == NULL) {
    /* Check if block size should be increased (if many requests for this size) */
    if (list->blk_alloc == 0) {
      list->blocksize <<= 1;
      list->blk_alloc = (1<<18) / (list->blocksize * elemsize);
      if (list->blk_alloc <= 0)
        list->blk_alloc = (int32)0x70000000;	/* Limit blocksize to new value */
    }

    /* Allocate block */
    cpp = list->freelist = (char **) calloc(list->blocksize, elemsize);
        
    cp = (char *) cpp;
    for (j = list->blocksize - 1; j > 0; --j) {
      cp += elemsize;
      *cpp = cp;
      cpp = (char **)cp;
    }
    *cpp = NULL;
    --(list->blk_alloc);
  }

  /* Unlink and return first element in freelist */
  cp = (char *)(list->freelist);
  list->freelist = (char **)(*(list->freelist));

  return (cp);
}

void __myfree__ (char *elem, int32 elemsize, char *caller_file, int32 caller_line)
{
  char **cpp;
  mylist_t *prev, *list;

  /* Find list for elemsize */
  prev = NULL;
  for (list = head; list && (list->elemsize != elemsize); list = list->next)
    prev = list;

  if (! list) {
    E_FATAL("Unknown list item size: %d; called from %s(%d)\n",
        elemsize, caller_file, caller_line);
  } else if (prev) {
    /* List found; move entry to head of list */
    prev->next = list->next;
    list->next = head;
    head = list;
  }

  /*
   * Insert freed item at head of list.
   * NOTE: skipping check for size being multiple of (void *).
   */
  cpp = (char **) elem;
  *cpp = (char *) list->freelist;
  list->freelist = cpp;
}

const char *g_str = "Hello";

void *do_alloc(size_t size) {
  return __mymalloc__(size, __FILE__, __LINE__);
}

int *do_fib1(int);

int *do_fib_m1(int count) {
  return do_fib1(count - 1);
}

int *do_fib_m2(int count) {
  return do_fib1(count - 2);
}

int *do_fib1(int count) {
  int *data = do_alloc(sizeof(int));

  if (count == 2) {
    *data = 1;
  }

  if (count == 1) {
    *data = 2;
  }

  int *res1 = do_fib_m1(count);
  int *res2 = do_fib_m2(count);

  *data = *res1 + *res2;

  __myfree__((char *)res1, sizeof(res1), __FILE__, __LINE__);
  __myfree__((char *)res2, sizeof(res1), __FILE__, __LINE__);

  return data;
}

int main(void) {
  int *fib1 = do_fib1(1);
  int *fib2 = do_fib1(1000);
  
  return EXIT_SUCCESS;
}


