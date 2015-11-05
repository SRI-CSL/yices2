/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>

#include "utils/generic_heap.h"


#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline int random(void) {
  return rand();
}

#endif


/*
 * Global heap
 */
static generic_heap_t heap;


/*
 * Add n random elements to heap
 */
static void add_random(generic_heap_t *heap, uint32_t n) {
  uint32_t i, k;
  int32_t x;

  k = 0;
  for (i=0; i<n; i++) {
    x = random() % 100;
    generic_heap_add(heap, x);
    printf(" %2"PRId32, x);
    k ++;
    if (k >= 20) {
      printf("\n");
      k = 0;
    }
  }

  if (k > 0) {
    printf("\n");
  }
}

/*
 * Remove n random elements from heap
 */
static void remove_random(generic_heap_t *heap, uint32_t n) {
  uint32_t i, k;
  int32_t x;

  k = 0;
  for (i=0; i<n; i++) {
    x = random() % 100;
    generic_heap_remove(heap, x);
    printf(" %2"PRId32, x);
    k ++;
    if (k >= 20) {
      printf("\n");
      k = 0;
    }
  }

  if (k > 0) {
    printf("\n");
  }
}



/*
 * Print the heap elements
 */
static void print_heap(generic_heap_t *heap) {
  uint32_t i, n, k;

  k = 0;
  n = heap->nelems;
  for (i=1; i<=n; i++) {
    printf(" %2"PRId32, heap->heap[i]);
    k ++;
    if (k >= 20) {
      printf("\n");
      k = 0;
    }
  }
  if (k > 0) {
    printf("\n");
  }
}

/*
 * Extract all elements one by one and print them
 */
static void test_heap(generic_heap_t *heap) {
  uint32_t k;
  int32_t x;

  k = 0;
  for (;;) {
    x = generic_heap_get_min(heap);
    if (x < 0) break;
    printf(" %2"PRId32, x);
    k ++;
    if (k >= 20) {
      printf("\n");
      k = 0;
    }
  }
  if (k > 0) {
    printf("\n");
  }
}


/*
 * For testing: comparison function is >
 */
static bool test_cmp(void *data, int32_t x, int32_t y) {
  return x > y;
}



int main(void) {
  uint32_t i, n;

  init_generic_heap(&heap, 5, 5, test_cmp, NULL);

  for (n = 10; n<200; n += 20) {
    for (i=0; i<100; i++) {
      printf("\n=== Test %"PRIu32" size %"PRIu32" ===\n", i, n);
      printf("--- Random add ---\n");
      add_random(&heap, n);
      printf("--- Random remove ---\n");
      remove_random(&heap, 20);
      printf("--- Heap content ---\n");
      print_heap(&heap);
      printf("--- Extract elements ---\n");
      test_heap(&heap);
      reset_generic_heap(&heap);
    }
  }

  delete_generic_heap(&heap);
  return 0;
}
