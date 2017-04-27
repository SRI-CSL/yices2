/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
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
#include <inttypes.h>

#include "model/small_bvsets.h"
#include "utils/bitvectors.h"

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
int main(void) {
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
