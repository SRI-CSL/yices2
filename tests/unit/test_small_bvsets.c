/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <inttypes.h>

#include "utils/bitvectors.h"
#include "model/small_bvsets.h"

#ifdef MINGW

static inline long int random(void) {
  return rand();
}

#endif


/*
 * Print the content of set s
 */
static void print_bvset(small_bvset_t *s) {
  uint32_t i, n;

  printf("set %p\n", s);
  printf("  size = %"PRIu32"\n", s->size);
  printf("  nelems = %"PRIu32"\n", s->nelems);
  printf("  ptr = %"PRIu32"\n", s->ptr);

  if (s->nelems > 0) {
    printf("  content:");
    n = s->size;
    for (i=0; i<n; i++) {
      if (tst_bit(s->set, i)) {
	printf(" %"PRIu32, i);
      }
    }
    printf("\n");
  }
}


/*
 * Add n random elements to set s
 */
static void add_random(small_bvset_t *s, uint32_t n) {
  uint32_t i, x, mask;

  mask = s->size - 1;
  for (i=0; i<n; i++) {
    x = ((uint32_t) random()) & mask;
    small_bvset_add(s, x);
  }
}


/*
 * Initialization for size n
 * - then add m random elements
 */
static void init_test_set(small_bvset_t *s, uint32_t n, uint32_t m) {
  uint32_t i, x, mask;

  init_small_bvset(s, n);
  mask = (1<<n) - 1;
  for (i=0; i<m; i++) {
    x = ((uint32_t) random()) & mask;
    small_bvset_add(s, x);
  }
}


/*
 * Global set
 */
static small_bvset_t set;


/*
 * Main test
 */
int main() {
  uint32_t x;

  init_test_set(&set, 4, 10);
  printf("\n=== Initial set ===\n");
  print_bvset(&set);
  printf("\n");

  // collect fresh values until the set is full
  while (! small_bvset_full(&set)) {
    x = small_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, set.nelems);
  }

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");

  reset_small_bvset(&set);
  printf("\n=== After reset ===\n");
  print_bvset(&set);
  printf("\n");

  add_random(&set, 14);
  printf("\n=== After 14 additions ===\n");
  print_bvset(&set);
  printf("\n");

  while (! small_bvset_full(&set)) {
    x = small_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, set.nelems);
  }

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");

  delete_small_bvset(&set);


  // Try a larger size
  init_test_set(&set, 24, 6000);
  printf("\n=== Initial set ===\n");
  print_bvset(&set);
  printf("\n");

  // collect fresh values until the set is full
  while (! small_bvset_full(&set)) {
    x = small_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, set.nelems);
  }

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");

  delete_small_bvset(&set);

  return 0;
}
