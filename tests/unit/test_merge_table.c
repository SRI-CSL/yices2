/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "solvers/bv/merge_table.h"

#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif


/*
 * Display root of x for all x in 0 .. n - 1
 */
static void show_all_roots(mtbl_t *table, uint32_t n) {
  int32_t x, y;

  for (x=0; x<n; x++) {
    y = mtbl_get_root(table, x);
    printf("root[%"PRId32"] = %"PRId32"\n", x, y);
  }
}


/*
 * Display root[x] only if it's not x
 */
static void show_roots(mtbl_t *table, uint32_t n) {
  int32_t x, y;

  for (x=0; x<n; x++) {
    y = mtbl_get_root(table, x);
    if (x != y) {
      printf("root[%"PRId32"] = %"PRId32"\n", x, y);
    }
  }
}



/*
 * Collect root[x] for all x in 0 ... n-1
 * - store the result in array a
 */
static void collect_roots(mtbl_t *table, uint32_t n, int32_t *a) {
  uint32_t i;

  for (i=0; i<n; i++) {
    a[i] = mtbl_get_root(table, i);
  }
}


/*
 * Check whether the table and array a agree
 * - a[i] contains the expected root of i
 */
static bool check_roots(mtbl_t *table, uint32_t n, int32_t *a) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (a[i] != mtbl_get_root(table, i)) {
      return false;
    }
  }

  return true;
}


/*
 * Merge the classes of x and y
 * - by mapping root[x] to y
 */
static void test_merge(mtbl_t *table, int32_t x, int32_t y) {
  int32_t r, s;

  printf("test_merge %"PRId32" and %"PRId32"\n", x, y);
  if (mtbl_equiv(table, x, y)) {
    printf(" ---> not mergeable: already in the same class\n");
  } else {
    r = mtbl_get_root(table, x);
    assert(mtbl_is_root(table, r));
    printf(" ---> root[%"PRId32"] = %"PRId32"\n", x, r);

    s = mtbl_get_root(table, y);
    assert(mtbl_is_root(table, s));
    printf(" ---> root[%"PRId32"] = %"PRId32"\n", y, s);

    mtbl_map(table, r, y);
    printf(" ---> setting map[%"PRId32"] := %"PRId32"\n", r, y);

    // check that all x, y, r all have root s
    if (mtbl_get_root(table, x) != s ||
	mtbl_get_root(table, r) != s ||
	mtbl_get_root(table, y) != s) {
      printf("**** BUG DETECTED ****\n");
      fflush(stdout);
      abort();
    }
  }
}


/*
 * Select k random pairs of integers in the interval [0, n -1]
 * and call test_merge on them.
 */
static void random_merges(mtbl_t *table, uint32_t k, uint32_t n) {
  int32_t x, y;

  while (k > 0) {
    k --;
    x = random() % n;
    y = random() % n;
    test_merge(table, x, y);
  }
}


#define RANGE 1000

static mtbl_t merge;
static int32_t content[6][RANGE];


int main(void) {
  init_mtbl(&merge);

  printf("=== Initial table ===\n");
  show_all_roots(&merge, RANGE);

  reset_mtbl(&merge);
  printf("\n=== After reset ===\n");
  show_all_roots(&merge, RANGE);
  printf("\n\n");

  random_merges(&merge, 30, RANGE/2);
  printf("\n=== Level 0: after 30 random merges ===\n");
  show_roots(&merge, RANGE);
  collect_roots(&merge, RANGE, content[0]);
  printf("\n\n");

  // empty push/pop
  mtbl_push(&merge);
  mtbl_pop(&merge);

  if (! check_roots(&merge, RANGE, content[0])) {
    printf("*** BUG IN POP ***\n");
    fflush(stdout);
    abort();
  }


  // seqyence off push + merge
  mtbl_push(&merge);
  random_merges(&merge, 40, 3*RANGE/4);
  printf("\n=== Level 1: after 40 random merges ===\n");
  show_roots(&merge, RANGE);
  collect_roots(&merge, RANGE, content[1]);
  printf("\n\n");

  mtbl_push(&merge);
  random_merges(&merge, 10, 2*RANGE/3);
  printf("\n=== Level 2: after 10 random merges ===\n");
  show_roots(&merge, RANGE);
  collect_roots(&merge, RANGE, content[2]);
  printf("\n\n");

  mtbl_push(&merge);
  random_merges(&merge, 30, RANGE);
  printf("\n=== Level 3: after 30 random merges ===\n");
  show_roots(&merge, RANGE);
  collect_roots(&merge, RANGE, content[3]);
  printf("\n\n");

  mtbl_push(&merge);
  random_merges(&merge, 50, RANGE);
  printf("\n=== Level 4: after 50 random merges ===\n");
  show_roots(&merge, RANGE);
  printf("\n\n");

  // test pop
  mtbl_pop(&merge);
  printf("\n=== Back to level 3 ===\n");
  show_roots(&merge, RANGE);
  printf("\n\n");
  if (! check_roots(&merge, RANGE, content[3])) {
    printf("*** BUG IN POP ***\n");
    fflush(stdout);
    abort();
  }

  mtbl_pop(&merge);
  printf("\n=== Back to level 2 ===\n");
  show_roots(&merge, RANGE);
  printf("\n\n");
  if (! check_roots(&merge, RANGE, content[2])) {
    printf("*** BUG IN POP ***\n");
    fflush(stdout);
    abort();
  }

  mtbl_pop(&merge);
  printf("\n=== Back to level 1 ===\n");
  show_roots(&merge, RANGE);
  printf("\n\n");
  if (! check_roots(&merge, RANGE, content[1])) {
    printf("*** BUG IN POP ***\n");
    fflush(stdout);
    abort();
  }

  // more push + merge
  mtbl_push(&merge);
  random_merges(&merge, 40, RANGE);
  printf("\n=== Level 2: after 40 random merges ===\n");
  show_roots(&merge, RANGE);
  collect_roots(&merge, RANGE, content[2]);
  printf("\n\n");

  // push/no merge
  mtbl_push(&merge);
  printf("\n=== Level 3: no changes ===\n");
  show_roots(&merge, RANGE);
  collect_roots(&merge, RANGE, content[3]);
  printf("\n\n");

  // push + merge
  mtbl_push(&merge);
  random_merges(&merge, 40, RANGE);
  printf("\n=== Level 4: after 40 random merges ===\n");
  show_roots(&merge, RANGE);

  // pop back to 0
  mtbl_pop(&merge);
  printf("\n=== Back to level 3 ===\n");
  show_roots(&merge, RANGE);
  if (! check_roots(&merge, RANGE, content[3])) {
    printf("*** BUG IN POP ***\n");
    fflush(stdout);
    abort();
  }

  mtbl_pop(&merge);
  printf("\n=== Back to level 2 ===\n");
  show_roots(&merge, RANGE);
  if (! check_roots(&merge, RANGE, content[2])) {
    printf("*** BUG IN POP ***\n");
    fflush(stdout);
    abort();
  }

  mtbl_pop(&merge);
  printf("\n=== Back to level 1 ===\n");
  show_roots(&merge, RANGE);
  if (! check_roots(&merge, RANGE, content[1])) {
    printf("*** BUG IN POP ***\n");
    fflush(stdout);
    abort();
  }

  mtbl_pop(&merge);
  printf("\n=== Back to level 0 ===\n");
  show_roots(&merge, RANGE);
  if (! check_roots(&merge, RANGE, content[0])) {
    printf("*** BUG IN POP ***\n");
    fflush(stdout);
    abort();
  }

  delete_mtbl(&merge);

  return 0;
}
