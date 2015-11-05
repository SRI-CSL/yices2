/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>

#include "utils/int_hash_map2.h"


#ifdef MINGW
// random does not exist on MINGW
static inline long int random(void) {
  return rand();
}

#endif


/*
 * Show the map
 */
static void print_map(int_hmap2_t *map) {
  int_hmap2_rec_t *d;
  uint32_t i, n, check;

  printf("map %p\n", map);
  printf("  size = %"PRIu32"\n", map->size);
  printf("  nelems = %"PRIu32"\n", map->nelems);
  printf("  resize_threshold = %"PRIu32"\n", map->resize_threshold);
  printf("  data = %p\n", map->data);
  printf("  content:\n");

  check = 0;
  d = map->data;
  n = map->size;
  for (i=0; i<n; i++) {
    if (d->k0 >= 0) {
      printf("    [k0 = %"PRId32", k1 = %"PRId32", val = %"PRId32"]\n", d->k0, d->k1, d->val);
      check ++;
    }
    d ++;
  }
  printf("  %"PRIu32" records\n\n", check);
  assert(check == map->nelems);
}


/*
 * Input data: array of at most MAXP pairs
 */
#define MAXP 4000

typedef struct pair_s {
  int32_t k0;
  int32_t k1;
} pair_t;

static pair_t data[MAXP];


/*
 * Random key (integer in the range [0 ... 99]
 */
static int32_t random_key(void) {
  int32_t x;

  x = random();
  assert(x >= 0);
  return (x % 100);
}

/*
 * Initialize array *a with n random pairs
 */
static void random_pairs(pair_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    a[i].k0 = random_key();
    a[i].k1 = random_key();
  }
}



/*
 * Test: add array a to hmap
 * - hmap must be initialized
 * - n = size of the array
 */
static void test1(int_hmap2_t *hmap, pair_t *a, uint32_t n) {
  int_hmap2_rec_t *find, *get;
  int32_t k0, k1;
  uint32_t i;
  bool new;

  // first pass: find + get
  for (i=0; i<n; i++) {
    k0 = a[i].k0;
    k1 = a[i].k1;
    printf("Testing: k0 = %"PRId32", k1 = %"PRId32"\n", k0, k1);
    find = int_hmap2_find(hmap, k0, k1);
    new = false;
    get = int_hmap2_get(hmap, k0, k1, &new);
    if (find != NULL) {
      assert(!new && get == find && find->k0 == k0 &&
	     find->k1 == k1 && find->val == (k0+k1));

      printf("Found record: [k0 = %"PRId32", k1 = %"PRId32", val = %"PRId32"]\n",
	     find->k0, find->k1, find->val);
    } else {
      assert(new && get != NULL && get->k0 == k0 && get->k1 == k1);
      get->val = k0+k1;
      printf("New record: [k0 = %"PRId32", k1 = %"PRId32", val = %"PRId32"]\n",
	     get->k0, get->k1, get->val);
    }
  }

  // second pass: find should always succeed
  for (i=0; i<n; i++) {
    k0 = a[i].k0;
    k1 = a[i].k1;
    printf("Checking: k0 = %"PRId32", k1 = %"PRId32"...", k0, k1);
    find = int_hmap2_find(hmap, k0, k1);
    get = int_hmap2_get(hmap, k0, k1, &new);
    if (!new &&  find != NULL && find == get &&
	find->k0 == k0 && find->k1 == k1 && find->val == k0+k1) {
      printf("ok\n");
    } else {
      printf("failed\n");
      fflush(stdout);
      abort();
    }
  }
}


/*
 * Garbage collection test:
 * - remove all pairs such that val >= 130
 */
static bool keep_alive(void *aux, int_hmap2_rec_t *r) {
  return r->val < 130;
}

static void test_gc(int_hmap2_t *hmap) {
  printf("*************\n"
	 "*  GC TEST  *\n"
	 "*************\n"
	 "\n");

  printf("Before\n");
  print_map(hmap);
  int_hmap2_gc(hmap, NULL, keep_alive);

  printf("After\n");
  print_map(hmap);
  printf("\n");
}



/*
 * Global hmap
 */
static int_hmap2_t hmap;


/*
 * Run the tests
 */
int main(void) {
  // init/reset/delete test
  init_int_hmap2(&hmap, 0);
  printf("*** Initial map ***\n");
  print_map(&hmap);
  reset_int_hmap2(&hmap);
  printf("*** After reset ***\n");
  print_map(&hmap);
  delete_int_hmap2(&hmap);

  // start from a minimal size table
  printf("\n*** Minimal map ***\n");
  init_int_hmap2(&hmap, 1);
  print_map(&hmap);
  // add 50 random pairs
  random_pairs(data, 50);
  test1(&hmap, data, 50);
  printf("*** Content ***\n");
  print_map(&hmap);
  reset_int_hmap2(&hmap);
  printf("*** After reset ***\n");
  print_map(&hmap);


  // more add tests: 4000 pairs
  random_pairs(data, MAXP);
  test1(&hmap, data, MAXP);
  printf("*** Content ***\n");
  print_map(&hmap);

  // gc test twice
  test_gc(&hmap);
  test_gc(&hmap);

  // add after GC: 200 pairs
  random_pairs(data, 200);
  test1(&hmap, data, 200);
  printf("*** Content ***\n");
  print_map(&hmap);

  // reset then delete
  reset_int_hmap2(&hmap);
  printf("*** Final reset ***\n");
  print_map(&hmap);
  delete_int_hmap2(&hmap);

  return 0;
}
