/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "utils/pair_hash_sets.h"

#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline int random(void) {
  return rand();
}

#endif


static pair_hset_t hset;

static void print_hset(pair_hset_t *set) {
  uint32_t i;
  int_pair_t *d;

  printf("set %p\n", set);
  printf("  size = %"PRIu32"\n", set->size);
  printf("  nelems = %"PRIu32"\n", set->nelems);
  printf("  content:\n");

  d = set->data;
  for (i=0; i<set->size; i++) {
    if (d->left >= 0) {
      printf("   [left = %"PRId32", right = %"PRId32"]\n", d->left, d->right);
    }
    d ++;
  }
  printf("\n");
}

#define NTEST 40

static int32_t test_values[40] = {
  01, 12, 23, 34, 45, 56, 67, 78, 89, 90,
  90, 89, 87, 86, 65, 64, 3, 832, 73, 10,
  73, 83, 12, 18, 38, 02, 473, 19, 91, 13,
  10, 10, 23, 36, 47, 79, 17, 53, 35, 19,
};


int main(void) {
  int32_t a, b;
  uint32_t i, n;

  init_pair_hset(&hset, 8);

  printf("\n*** Initial set ***\n");
  print_hset(&hset);

  // test add and resize
  n = 20;
  for (i=0; i<n; i++) {
    a = test_values[2*i];
    b = test_values[2*i+1];
    printf("Adding [%"PRId32", %"PRId32"]: ", a, b);
    if (pair_hset_add(&hset, a, b)) {
      printf("new pair\n");
    } else {
      printf("already present\n");
    }
  }

  printf("\n*** After additions ***\n");
  print_hset(&hset);

  // test find
  n = 39;
  for (i=0; i<n; i++) {
    a = test_values[i];
    b = test_values[i + 1];
    printf("Checking [%"PRId32", %"PRId32"]: ", a, b);
    if (pair_hset_member(&hset, a, b)) {
      printf("present\n");
    } else {
      printf("absent\n");
    }
  }

  printf("\n*** Reset ***\n");
  pair_hset_reset(&hset);
  print_hset(&hset);


  // random additions
  for (i=0; i<100000; i++) {
    a = random() % 100;
    b = random() % 100;
    pair_hset_add(&hset, a, b);
  }




  delete_pair_hset(&hset);
  return 0;
}
