/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2018 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>

#include "terms/rationals.h"
#include "terms/int_rational_hash_maps.h"

#ifdef MINGW
// random does not exist on MINGW
static inline long int random(void) {
  return rand();
}
#endif

/*
 * Print the map
 */
static void print_hmap(int_rat_hmap_t *map) {
  int_rat_hmap_rec_t *d;
  uint32_t i, n, count;

  printf("hmap %p\n", map);
  printf("  size = %"PRIu32"\n", map->size);
  printf("  nelems = %"PRIu32"\n", map->nelems);
  printf("  resize threshold = %"PRIu32"\n", map->resize_threshold);
  printf("  content:\n");

  count = 0;
  d = map->data;
  n = map->size;
  for (i=0; i<n; i++) {
    if (d->key >= 0) {
      printf("    [key = %"PRId32", val = ", d->key);
      q_print(stdout, &d->value);
      printf("]\n");
      count ++;
    }
    d ++;
  }

  printf("  %"PRIu32" records\n\n", count);
  assert(count == map->nelems);
}


/*
 * Test input: i --> 1/i for i=1 to 100 from an empty hmap
 */
static void add_data(int_rat_hmap_t *hmap) {  
  int_rat_hmap_rec_t *r;
  bool new;
  int32_t i;

  assert(hmap->nelems == 0);
  
  for (i=1; i<=100; i++) {
    r = int_rat_hmap_find(hmap, i);
    if (r != NULL) {
      fprintf(stderr, "Error in find(hmap, %"PRId32"): expected NULL, got %p\n", i, r);
      exit(1);
    }

    r = int_rat_hmap_get(hmap, i, &new);
    if (r == NULL) {
      fprintf(stderr, "Error in get(hmap, %"PRId32"): got NULL pointer\n", i);
      exit(1);
    }
    if (r->key != i) {
      fprintf(stderr, "Error in get(hmap, %"PRId32"): key = %"PRId32"\n", i, r->key);
      exit(1);
    }
    if (q_is_nonzero(&r->value)) {
      fprintf(stderr, "Error in get(hmap, %"PRId32"): value is", i);
      q_print(stderr, &r->value);
      fprintf(stderr, " (should be 0)\n");
      exit(1);
    }
    if (!new) {
      fprintf(stderr, "Error in get(hmap, %"PRId32"): record not marked as new\n", i);
      exit(1);      
    }
    q_set_int32(&r->value, 1, (uint32_t) i);
  }
  printf("add_data worked\n");
}


/*
 * Check that the data is correct after the above addition
 */
static void check_data(int_rat_hmap_t *hmap) {
  int_rat_hmap_rec_t *r;
  int32_t i;
  int32_t num;
  uint32_t den;

  for (i=1; i<=100; i++) {
    r = int_rat_hmap_find(hmap, i);
    if (r == NULL) {
      fprintf(stderr, "Error in find(hmap, %"PRId32"): got NULL\n", i);
      exit(1);
    }
    if (r->key != i) {
      fprintf(stderr, "Error in find(hmap, %"PRId32"): key = %"PRId32"\n", i, r->key);
      exit(1);
    }
    if (! q_get_int32(&r->value, &num, &den)) {
      fprintf(stderr, "Error in find(hmap, %"PRId32"): value doesn't fit in 32bit\n", i);
      exit(1);
    }
    if (num != 1 || den != ((uint32_t) i)) {
      fprintf(stderr, "Error in find(hmap, %"PRId32"): value = %"PRId32"/%"PRIu32"\n", i, num, den);
      exit(1);
    }
  }
  printf("check_data passed\n");
}


/*
 * Global map
 */
static int_rat_hmap_t hmap;

/*
 * Run the tests
 */
int main(void) {
  init_rationals();

  init_int_rat_hmap(&hmap, 0);
  printf("**** Initial map (empty) ****\n");
  print_hmap(&hmap);
  reset_int_rat_hmap(&hmap);
  printf("**** After reset (empty) ****\n");
  print_hmap(&hmap);
  delete_int_rat_hmap(&hmap);

  init_int_rat_hmap(&hmap, 0);
  add_data(&hmap);
  printf("**** After addition (100 elements) ****\n");
  print_hmap(&hmap);
  check_data(&hmap);
  reset_int_rat_hmap(&hmap);
  printf("**** After reset ****\n");
  print_hmap(&hmap);
  add_data(&hmap);
  printf("**** After addition (100 elements) ****\n");
  print_hmap(&hmap);
  check_data(&hmap);
  delete_int_rat_hmap(&hmap);
  
  cleanup_rationals();

  return 0;
}
