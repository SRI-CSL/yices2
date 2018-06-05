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

/*
 * Hash table that maps non-negative integers to rationals.
 * This is used in the difference-logic profiler.
 *
 * This implementation supports only addition and query (not removal
 * of entries).
 */

#include <assert.h>

#include "terms/int_rational_hash_maps.h"
#include "utils/memalloc.h"

/*
 * For debugging: check whether n is 0 or a power of 2
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


/*
 * Initialization:
 * - n = initial size, must be a power of 2
 * - if n = 0, the default size is used
 */
void init_int_rat_hmap(int_rat_hmap_t *hmap, uint32_t n) {
  int_rat_hmap_rec_t *tmp;
  uint32_t i;

  if (n == 0) {
    n = INT_RAT_HMAP_DEF_SIZE;
  }

  if (n > INT_RAT_HMAP_MAX_SIZE) {
    out_of_memory();
  }
  
  assert(is_power_of_two(n));

  tmp = (int_rat_hmap_rec_t *) safe_malloc(n * sizeof(int_rat_hmap_rec_t));
  for (i=0; i<n; i++) {
    tmp[i].key = -1;
    q_init(&tmp[i].value);
  }

  hmap->data = tmp;
  hmap->size = n;
  hmap->nelems = 0;
  hmap->resize_threshold = (uint32_t) (n * INT_RAT_HMAP_RESIZE_RATIO);
}


/*
 * Delete: free memory
 */
void delete_int_rat_hmap(int_rat_hmap_t *hmap) {
  int_rat_hmap_rec_t *tmp;
  uint32_t i, n;

  tmp = hmap->data;
  n = hmap->size;
  for (i=0; i<n; i++) {
    q_clear(&tmp[i].value);
  }

  safe_free(tmp);
  hmap->data = NULL;
}



/*
 * Remove all records
 */
void reset_int_rat_hmap(int_rat_hmap_t *hmap) {
  int_rat_hmap_rec_t *tmp;
  uint32_t i, n;

  tmp = hmap->data;
  n = hmap->size;
  for (i=0; i<n; i++) {
    tmp[i].key = -1;
    q_clear(&tmp[i].value);
  }

  hmap->nelems = 0;
}


/*
 * Hash code for a 32bit key.
 * This is Jenkins's hash function (cf. utils/hash_functions.c)
 */
static uint32_t hash_key(int32_t k) {
  uint32_t x;

  x = (uint32_t) k;
  x = (x + 0x7ed55d16) + (x<<12);
  x = (x ^ 0xc761c23c) ^ (x>>19);
  x = (x + 0x165667b1) + (x<<5);
  x = (x + 0xd3a2646c) ^ (x<<9);
  x = (x + 0xfd7046c5) + (x<<3);
  x = (x ^ 0xb55a4f09) ^ (x>>16);

  return x;
}


/*
 * Find record with key k. Return NULL if there's none.
 * - k must be non-negative.
 */
int_rat_hmap_rec_t *int_rat_hmap_find(int_rat_hmap_t *hmap, int32_t k) {
  int_rat_hmap_rec_t *r;
  uint32_t i, mask;

  assert(k >= 0);
  assert(hmap->nelems < hmap->size); // otherwise, this will loop
  assert(is_power_of_two(hmap->size));

  mask = hmap->size - 1;
  i = hash_key(k) & mask;
  for (;;) {
    r = hmap->data + i;
    if (r->key < 0) return NULL;
    if (r->key == k) return r;
    i ++;
    i &= mask;
  }
}


/*
 * Copy record r into a fresh table a
 * - mask = size of a - 1 (a'size is a power of two)
 * - there must be room in a
 * - warning: this makes a shallow copy of r->value.
 *   So we must not call q_clear(&r->value);
 */
static void int_rat_hmap_clean_copy(int_rat_hmap_rec_t *a, int_rat_hmap_rec_t *r, uint32_t mask) {
  uint32_t i;

  assert(r->key >= 0);

  i = hash_key(r->key) & mask;
  while (a[i].key >= 0) {
    i ++;
    i &= mask;
  }

  a[i] = *r;
}

/*
 * Make the table twice as large.
 */
static void int_rat_hmap_extend(int_rat_hmap_t *hmap) {
  int_rat_hmap_rec_t *tmp, *r;
  uint32_t i, n, n2, mask;

  n = hmap->size;
  n2 = n << 1;
  if (n2 > INT_RAT_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n2));

  tmp = (int_rat_hmap_rec_t *) safe_malloc(n2 * sizeof(int_rat_hmap_rec_t));
  for (i=0; i<n2; i++) {
    tmp[i].key = -1;
    q_init(&tmp[i].value);
  }

  mask = n2 -1;
  r = hmap->data;
  for (i=0; i<n; i++) {
    if (r->key >= 0) {
      int_rat_hmap_clean_copy(tmp, r, mask);
    }
    r ++;
  }

  // we don't clear the rationals of hmap->data
  // since we made shallow copies in tmp.
  safe_free(hmap->data);

  hmap->data = tmp;
  hmap->size = n2;
  hmap->resize_threshold = (uint32_t) (n2 * INT_RAT_HMAP_RESIZE_RATIO);
}



/*
 * Get record with key k
 * - if one is in the table return it and set *new to false.
 * - otherwise, create a fresh record with key k, value 0, 
 *   and  set *new to true.
 * - k must be non-negative
 */
int_rat_hmap_rec_t *int_rat_hmap_get(int_rat_hmap_t *hmap, int32_t k, bool *new) {
  int_rat_hmap_rec_t *r;
  uint32_t i, mask;

  assert(k >= 0);
  assert(hmap->nelems < hmap->size); // otherwise, this will loop
  assert(is_power_of_two(hmap->size));

  *new = false;
  mask = hmap->size - 1;
  i = hash_key(k) & mask;
  for (;;) {
    r = hmap->data + i;
    if (r->key == k) return r;
    if (r->key < 0) break; // found an empty slot
    i ++;
    i &= mask;
  }

  *new = true;
  r->key = k;  
  hmap->nelems ++;
  if (hmap->nelems > hmap->resize_threshold) {
    int_rat_hmap_extend(hmap);
    r = int_rat_hmap_find(hmap, k);
    assert(r != NULL);
  }

  return r;
}


/*
 * Compute the sum of all values
 */
void int_rat_hmap_sum(int_rat_hmap_t *hmap, rational_t *sum) {
  int_rat_hmap_rec_t *r;
  uint32_t i, n;

  q_clear(sum);
  n = hmap->size;
  r = hmap->data;
  for (i=0; i<n; i++) {
    if (r->key >= 0) {
      q_add(sum, &r->value);
    }
    r ++;
  }
}

