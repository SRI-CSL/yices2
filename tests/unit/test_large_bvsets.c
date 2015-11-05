/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <inttypes.h>

#include "utils/bitvectors.h"
#include "model/large_bvsets.h"

#ifdef MINGW

static inline long int random(void) {
  return rand();
}

#endif


/*
 * Print the content of set s
 */
static void print_bvset(large_bvset_t *s) {
  uint32_t i, n;

  printf("set %p\n", s);
  printf("  size = %"PRIu32"\n", s->size);
  printf("  nelems = %"PRIu32"\n", s->nelems);
  printf("  max_val = %"PRIu32"\n", s->max_val);
  printf("  fsize = %"PRIu32"\n", s->fsize);
  printf("  nfresh = %"PRIu32"\n", s->nfresh);

  if (s->nelems > 0) {
    printf("  bits:");
    n = s->size;
    for (i=0; i<n; i++) {
      if (tst_bit(s->set, i)) {
	printf(" %"PRIu32, i);
      }
    }
    printf("\n");
  }

  n = s->nfresh;
  if (n > 0) {
    printf("  fresh elements:");
    for (i=0; i<n; i++) {
      printf(" %"PRIu32, s->fresh_vals[i]);
    }
    printf("\n");
  }
}


/*
 * Add n random elements to set s
 * - mask = 2^k - 1 where k = bitsize considered
 *   (i.e., elements are in the interval [0, 2^k-1]
 */
static void add_random(large_bvset_t *s, uint32_t n, uint32_t mask) {
  uint32_t i, x;

  for (i=0; i<n; i++) {
    x = ((uint32_t) random()) & mask;
    large_bvset_add(s, x);
  }
}


/*
 * Initialization:
 * - n = bit size
 * - add m random elements
 */
static void init_test_set(large_bvset_t *s, uint32_t n, uint32_t m) {
  uint32_t mask;

  init_large_bvset(s, n, 0);
  mask = (1<<n) - 1;
  add_random(s, m, mask);
}


/*
 * Global set
 */
static large_bvset_t set;



/*
 * First test: size = 64
 */
static void test1(void) {
  uint32_t x;

  printf("\n"
	 "=================\n"
	 "     TEST 1\n"
	 "=================\n\n");

  // 50 initial elements
  init_test_set(&set, 6, 50);
  printf("=== Initial set: 50 additions ===\n");
  print_bvset(&set);
  printf("\n");

  do {
    x = large_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, set.nelems);
  } while (x != 0);

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");

  reset_large_bvset(&set);
  printf("\n=== After reset ===\n");
  print_bvset(&set);
  printf("\n");

  // 40 initial elements
  add_random(&set, 40, 63);
  printf("\n=== After 40 additions ===\n");
  print_bvset(&set);
  printf("\n");

  do {
    x = large_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, set.nelems);
  } while (x != 0);

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");


  // empty initial set
  reset_large_bvset(&set);
  printf("\n=== After reset ===\n");
  print_bvset(&set);
  printf("\n");

  do {
    x = large_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, set.nelems);
  } while (x != 0);

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");

  delete_large_bvset(&set);
}



/*
 * Second test: size = 256
 */
static void test2(void) {
  uint32_t x;

  printf("\n"
	 "=================\n"
	 "     TEST 2\n"
	 "=================\n\n");

  // 200 initial additions
  init_test_set(&set, 8, 200);
  printf("=== Initial set: 200 additions ===\n");
  print_bvset(&set);
  printf("\n");

  do {
    x = large_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, set.nelems);
  } while (x != 0);

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");

  reset_large_bvset(&set);
  printf("\n=== After reset ===\n");
  print_bvset(&set);
  printf("\n");

  // 240 initial elements
  add_random(&set, 240, 255);
  printf("\n=== After 240 additions ===\n");
  print_bvset(&set);
  printf("\n");

  do {
    x = large_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, set.nelems);
  } while (x != 0);

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");


  // empty initial set
  reset_large_bvset(&set);
  printf("\n=== After reset ===\n");
  print_bvset(&set);
  printf("\n");

  do {
    x = large_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, set.nelems);
  } while (x != 0);

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");

  delete_large_bvset(&set);
}



/*
 * Size = 2048
 */
static void test3(void) {
  uint32_t x;

  printf("\n"
	 "=================\n"
	 "     TEST 3\n"
	 "=================\n\n");

  // 1000 initial additions
  init_test_set(&set, 11, 1000);
  printf("=== Initial set: 1000 additions ===\n");
  print_bvset(&set);
  printf("\n");

  do {
    x = large_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, set.nelems);
  } while (x != 0);

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");

  reset_large_bvset(&set);
  printf("\n=== After reset ===\n");
  print_bvset(&set);
  printf("\n");

  // 2000 initial additions
  add_random(&set, 2000, 2047);
  printf("\n=== After 2000 additions ===\n");
  print_bvset(&set);
  printf("\n");

  do {
    x = large_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, set.nelems);
  } while (x != 0);

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");


  // empty initial set
  reset_large_bvset(&set);
  printf("\n=== After reset ===\n");
  print_bvset(&set);
  printf("\n");

  do {
    x = large_bvset_get_fresh(&set);
    printf("get fresh: %"PRIu32", nelems = %"PRIu32"\n", x, set.nelems);
  } while (x != 0);

  printf("\n=== Final set ===\n");
  print_bvset(&set);
  printf("\n");

  delete_large_bvset(&set);
}





/*
 * Main test
 */
int main(void) {
  test1();
  test2();
  test3();

  return 0;
}
