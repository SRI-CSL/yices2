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

/*
 * Sets of unsigned 32-bit numbers
 * - only supports addition of elements
 */

#include <string.h>
#include <assert.h>

#include "utils/int_hash_sets.h"
#include "utils/int_array_sort.h"
#include "utils/memalloc.h"

/*
 * For debugging: check whether n is a power of two
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif



/*
 * Initialize: allocate an array of size n
 * n must be a power of two
 */
void init_int_hset(int_hset_t *set, uint32_t n) {
  uint32_t *tmp;

  if (n == 0) {
    n = INT_HSET_DEFAULT_SIZE;
  }

  if (n >= MAX_HSET_SIZE) {
    out_of_memory(); // abort
  }

  assert(is_power_of_two(n));

  // initialize all elements of tmp to zero
  tmp = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  memset(tmp, 0, n * sizeof(uint32_t));

  set->data = tmp;
  set->size = n;
  set->nelems = 0;
  set->z_flag = false;
  set->resize_threshold = (uint32_t)(n * INT_HSET_RESIZE_RATIO);
}


/*
 * Delete: free the array
 */
void delete_int_hset(int_hset_t *set) {
  safe_free(set->data);
  set->data = NULL;
}


/*
 * Hash function: 32 bits unsigned to 32 bits
 * Source: Jenkins hash
 * (http://www.burtleburtle.net/bob/hash/integer.html)
 */
static uint32_t hash(uint32_t x) {
  x = (x + 0x7ed55d16) + (x<<12);
  x = (x ^ 0xc761c23c) ^ (x>>19);
  x = (x + 0x165667b1) + (x<<5);
  x = (x + 0xd3a2646c) ^ (x<<9);
  x = (x + 0xfd7046c5) + (x<<3);
  x = (x ^ 0xb55a4f09) ^ (x>>16);
  return x;
}


/*
 * Insert integer x into array a.
 * - mask = 2^n - 1 where size of a = 2^n
 * - x must be nonzero, and not already in a
 * There must be at least one empty slot in a,
 * i.e., one i such that a[i] == 0.
 */
static void hset_insert(uint32_t *a, uint32_t mask, uint32_t x) {
  uint32_t i;

  i = hash(x) & mask;
  while (a[i] != 0) {
    i ++;
    i &= mask;
  }
  a[i] = x;
}


/*
 * Check whether x is present in a
 * - mask = 2^n - 1 where size of a = 2^n
 * - x must be nonzero
 * - if x is not present, there must be at least one
 *   empty slot in a, otherwise the function loops.
 */
static bool hset_search(uint32_t *a, uint32_t mask, uint32_t x) {
  uint32_t i;

  i = hash(x) & mask;
  for (;;) {
    if (a[i] == x) return true;
    if (a[i] == 0) return false;
    i ++;
    i &= mask;
  }
}


/*
 * Add x to a if it's not already present
 * - return true if x was added
 * - mask = 2^n - 1, where size of a = 2^n
 * - x must be nonzero
 * - there must be at least one empty slot in a (unless x is
 * present)
 */
static bool hset_add(uint32_t *a, uint32_t mask, uint32_t x) {
  uint32_t i;

  i = hash(x) & mask;
  while (a[i] != 0) {
    if (a[i] == x) return false;
    i ++;
    i &= mask;
  }
  a[i] = x;
  return true;
}



/*
 * Double the size of set. keep all elements
 */
static void hset_extend(int_hset_t *set) {
  uint32_t n, n2;
  uint32_t *tmp;
  uint32_t i, mask, x;

  n = set->size;
  n2 = n << 1; // new size
  if (n2 >= MAX_HSET_SIZE) {
    // overflow
    out_of_memory();
  }

  tmp = (uint32_t *) safe_malloc(n2 * sizeof(uint32_t));
  memset(tmp, 0, n2 * sizeof(uint32_t));

  // copy set->data into tmp
  mask = n2 - 1;
  for (i=0; i<n; i++) {
    x = set->data[i];
    if (x != 0) {
      hset_insert(tmp, mask, x);
    }
  }

  safe_free(set->data);
  set->data = tmp;
  set->size = n2;
  set->resize_threshold = (uint32_t)(n2 * INT_HSET_RESIZE_RATIO);
}



/*
 * External function: check whether x is present in set
 */
bool int_hset_member(int_hset_t *set, uint32_t x) {
  if (x == 0) {
    return set->z_flag;
  }
  return hset_search(set->data, set->size - 1, x);
}


/*
 * Add x to set. Return true if the addition was performed,
 * that is, if x is not present already.
 */
bool int_hset_add(int_hset_t *set, uint32_t x) {
  bool result;

  if (x == 0) {
    result = ! set->z_flag;
    set->z_flag = true;
  } else {
    assert(set->size > set->nelems);

    result = hset_add(set->data, set->size - 1, x);
    if (result) {
      set->nelems ++;
      if (set->nelems > set->resize_threshold) {
        hset_extend(set);
      }
    }
  }

  return result;
}


/*
 * Close the set
 * 1) move all non-zero elements in data[0 ... nelems-1]
 * 2) if z_flag is set, copy 0 into data[nelems], then increment nelems
 */
void int_hset_close(int_hset_t *set) {
  uint32_t i, j, n, x, *a;

  n = set->size;
  a = set->data;
  i = 0;
  for (j=0; j<n; j++) {
    x = a[j];
    if (x != 0) {
      a[i] = x;
      i ++;
    }
  }

  assert(i == set->nelems && i < n);
  if (set->z_flag) {
    a[i] = 0;
    i ++;
    set->nelems = i;
  }
}

/*
 * Close the set and sort it
 * 1) move all non-zero elements in data[0 ... nelems-1]
 * 2) sort data[0 ... nelems-1]
 * 3) if z_flag is set, copy 0 into data[nelems], then increment nelems
 */
void int_hset_close_and_sort(int_hset_t *set) {
  uint32_t i, j, n, x, *a;

  n = set->size;
  a = set->data;
  i = 0;
  for (j=0; j<n; j++) {
    x = a[j];
    if (x != 0) {
      a[i] = x;
      i ++;
    }
  }

  assert(i == set->nelems && i < n);
  if (set->z_flag) {
    a[i] = 0;
    i ++;
    set->nelems = i;
  }

  int_array_sort((int32_t*) a, set->nelems);
}


/*
 * Empty the set
 */
void int_hset_reset(int_hset_t *set) {
  uint32_t i, n, *a;

  n = set->size;
  a = set->data;

  if (n >= INT_HSET_SHRINK_SIZE) {
    safe_free(set->data);

    n = INT_HSET_DEFAULT_SIZE;
    a = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
    set->data = a;

    set->size = n;
    set->resize_threshold = (uint32_t)(n * INT_HSET_RESIZE_RATIO);
  }

  for (i=0; i<n; i++) {
    a[i] = 0;
  }

  set->nelems = 0;
  set->z_flag = false;
}
