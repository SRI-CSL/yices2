/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test int_bag vectors
 */

#include <stdio.h>
#include <inttypes.h>

#include "utils/int_bags.h"

// Mask to set/clear the sign bit of an integer
#define SIGN_BIT_MASK ((uint32_t) 0x80000000)

static inline int32_t flip_sign_bit(int32_t k) {
  return (int32_t)(((uint32_t) k) ^ SIGN_BIT_MASK);
}


/*
 * Print content of vector b
 */
static void print_bag(int32_t *b) {
  int_bag_t *bag;
  uint32_t i, n;
  int32_t x;

  printf("Bag %p\n", b);
  if (b == NULL) {
    printf("  null bag\n");
  } else {
    bag = ibag_header(b);
    printf("  capacity = %"PRIu32"\n", bag->capacity);
    printf("  size = %"PRIu32"\n", bag->size);
    printf("  nelems = %"PRIu32"\n", bag->nelems);
    printf("  free = %"PRId32, bag->free);
    if (bag->free < -1) {
      printf(" (index %"PRId32")\n", flip_sign_bit(bag->free));
    } else {
      printf("\n");
    }
    printf("  content:\n");
    n = ibag_size(b);
    for (i=0; i<n; i++) {
      x = b[i];
      printf("   data[%"PRIu32"] = %"PRId32, i, x);
      if (x < -1) {
	printf(" (index %"PRId32")\n", flip_sign_bit(x));
      } else {
	printf("\n");
      }
    }
  }
}


/*
 * Test data
 */

#define NUMTESTS 40

static int32_t data[NUMTESTS] = {
  30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
  50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
};

static int32_t index[NUMTESTS];

static int32_t *bag;


/*
 * Test add and remove
 */
int main() {
  uint32_t i;
  int32_t k;

  for (i=0; i<NUMTESTS; i ++) {
    index[i] = -1;
  }

  bag = NULL;
  printf("*** Initial bag ***\n");
  print_bag(bag);


  for (i=0; i<NUMTESTS; i += 2) {
    k = ibag_add(&bag, data[i]);
    index[i] = k;
    printf("Adding %"PRId32": index = %"PRId32"\n", data[i], k);
  }
  print_bag(bag);
  printf("\n");

  for (i=0; i<NUMTESTS; i += 4) {
    k = index[i];
    if (k >= 0) {
      printf("Removing %"PRId32" at index %"PRId32"\n", data[i], k);
      ibag_clear_elem(bag, k);
      index[i] = -1;
    }
  }
  print_bag(bag);
  printf("\n");

  for (i=0; i<NUMTESTS; i++) {
    k = index[i];
    if (k < 0) {
      k = ibag_add(&bag, data[i]);
      index[i] = k;
      printf("Adding %"PRId32": index = %"PRId32"\n", data[i], k);
      print_bag(bag);
    }
  }

  for (i=20; i<NUMTESTS; i += 3) {
    k = index[i];
    if (k >= 0) {
      printf("Removing %"PRId32" at index %"PRId32"\n", data[i], k);
      ibag_clear_elem(bag, k);
      print_bag(bag);
      index[i] = -1;
    }
  }

  printf("**** Reset ****\n");
  ibag_reset(bag);
  print_bag(bag);

  ibag_delete(bag);
  return 0;
}
