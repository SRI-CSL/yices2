/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <inttypes.h>
#include <assert.h>

#include "utils/memalloc.h"
#include "terms/rationals.h"
#include "terms/extended_rationals.h"
#include "terms/rational_hash_maps.h"


static void print_hmap(xq_hmap_t *map) {
  xq_hmap_rec_t *r;
  uint32_t i, n;

  printf("map %p\n", map);
  printf("  size = %"PRIu32"\n", map->size);
  printf("  nelems = %"PRIu32"\n", map->nelems);
  printf("  nentries = %"PRIu32"\n", map->nentries);
  printf("  ndeleted = %"PRIu32"\n", map->ndeleted);
  printf("  content:\n");

  r = map->data;
  n = map->size;
  for (i=0; i<n; i++) {
    if (r->value != 0 && r->value != UINT32_MAX) {
      printf("    [key = ");
      xq_print(stdout, &r->key);
      printf(", value = %"PRIu32"]\n", r->value);
    }
    r ++;
  }
  printf("\n");
}



/*
 * Rational numbers used for testing: each pair is num/den
 */
typedef struct rr_s {
  int32_t num;
  uint32_t den;
} rr_t;

#define NUM_PAIRS 11

static rr_t base[NUM_PAIRS] = {
  { 0, 1},
  { -1, 2}, { 1, 2},
  { -2, 3}, { 2, 3},
  { -1, 1}, { 1, 1},
  { -2, 1}, { 2, 1},
  { -3, 1}, { 3, 1},
};


/*
 * Initialize array q with n extended rationals
 */
static void init_test_array(xrational_t *q, uint32_t n) {
  uint32_t i, j, k;

  j = 0;
  k = 0;
  for (i=0; i<n; i++) {
    assert(j < NUM_PAIRS && k < NUM_PAIRS);

    xq_init(q);
    q_set_int32(&q->main, base[j].num, base[j].den);
    q_set_int32(&q->delta, base[k].num, base[k].den);
    q ++;

    j ++;
    if (j == NUM_PAIRS) {
      j = 0;
      k ++;
      if (k == NUM_PAIRS) {
	k = 0;
      }
    }
  }
}


/*
 * Delete array q of n elements
 */
static void free_test_array(xrational_t *q, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    xq_clear(q + i);
  }

  safe_free(q);
}



/*
 * Add q to map
 */
static void test_add(xq_hmap_t *map, xrational_t *q) {
  uint32_t a, na, ea;
  uint32_t b, nb, eb;

  printf("test add ");
  xq_print(stdout, q);
  fflush(stdout);

  a = xq_hmap_multiplicity(map, q);
  ea = xq_hmap_num_entries(map);
  na = xq_hmap_num_classes(map);

  xq_hmap_add_entry(map, q);

  b = xq_hmap_multiplicity(map, q);
  eb = xq_hmap_num_entries(map);
  nb = xq_hmap_num_classes(map);

  if (b != a+1 || eb != ea+1) {
    printf(" failed: incorrect counters\n");
    fflush(stdout);
    exit(1);
  }

  if ((a == 0 && nb != na + 1) || (a >= 1 && nb != na)) {
    printf(" failed: incorrect number of classes\n");
    fflush(stdout);
    exit(1);
  }

  printf(" ok\n");
}


/*
 * Remove q from map: q must be present in the table
 */
static void test_remove(xq_hmap_t *map, xrational_t *q) {
  uint32_t a, na, ea;
  uint32_t b, nb, eb;

  printf("test remove ");
  xq_print(stdout, q);
  fflush(stdout);

  a = xq_hmap_multiplicity(map, q);
  ea = xq_hmap_num_entries(map);
  na = xq_hmap_num_classes(map);

  assert(a > 0 && na > 0 && ea > 0);

  xq_hmap_remove_entry(map, q);

  b = xq_hmap_multiplicity(map, q);
  eb = xq_hmap_num_entries(map);
  nb = xq_hmap_num_classes(map);

  if (b != a-1 || eb != ea - 1) {
    printf(" failed: incorrect counters\n");
    fflush(stdout);
    exit(1);
  }

  if ((a == 1 && nb != na - 1) || (a > 1 && nb != na)) {
    printf(" failed: incorrect number of classes\n");
    fflush(stdout);
    exit(1);
  }

  printf(" ok\n");
}


/*
 * TEST1: add all elements in a[0 ... n-1] to hmap
 * then remove them all one by one.
 */
static void test1(xq_hmap_t *map, xrational_t *q, uint32_t n) {
  uint32_t i;

  printf("Test1: start map\n");
  print_hmap(map);
  printf("\n");

  for (i=0; i<n; i++) {
    test_add(map, q + i);
  }

  printf("\nTest1: after additions\n");
  print_hmap(map);
  printf("\n");

  for (i=0; i<n; i++) {
    test_remove(map, q + i);
  }

  printf("\nTest1: after removals\n");
  print_hmap(map);
  printf("\n");
}






/*
 * Global table used in the tests
 */
static xq_hmap_t map;

int main(void) {
  xrational_t *a;

  init_rationals();
  a = (xrational_t *) safe_malloc(150 * sizeof(xrational_t));
  init_test_array(a, 150);

  printf("Init: size 1\n");
  init_xq_hmap(&map, 1);
  print_hmap(&map);


  test1(&map, a, 150);

  printf("Reset\n");
  reset_xq_hmap(&map);
  print_hmap(&map);

  test1(&map, a, 150);

  delete_xq_hmap(&map);

  free_test_array(a, 150);
  cleanup_rationals();

  return 0;
}
