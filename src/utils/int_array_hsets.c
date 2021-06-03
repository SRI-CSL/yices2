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
 * SUPPORT FOR HASH CONSING OF INTEGER ARRAYS
 */

#include <assert.h>
#include <stdbool.h>

#include "utils/hash_functions.h"
#include "utils/int_array_hsets.h"
#include "utils/memalloc.h"



/*
 * ARRAY DESCRIPTORS
 */

/*
 * Hash code of array a[0 ...n-1]
 */
static inline uint32_t hash_array(const int32_t *a, uint32_t n) {
  return jenkins_hash_intarray(a, n);
}


/*
 * Create descriptor for a[0 ... n-1]
 * - don't set the hash code
 */
static harray_t *make_harray(const int32_t *a, uint32_t n) {
  harray_t *tmp;
  uint32_t i;

  if (n >= MAX_HARRAY_SIZE) {
    out_of_memory();
  }

  tmp = (harray_t *) safe_malloc(sizeof(harray_t) + n * sizeof(int32_t));
  tmp->nelems = n;
  for (i=0; i<n; i++) {
    tmp->data[i] = a[i];
  }

  return tmp;
}


/*
 * Check whether v == a[0...n-1]
 */
static bool eq_harray(const harray_t *p, const int32_t *a, uint32_t n) {
  uint32_t i;

  if (p->nelems != n) {
    return false;
  }

  for (i=0; i<n; i++) {
    if (p->data[i] != a[i]) {
      return false;
    }
  }

  return true;
}



/*
 * HASH TABLE
 */

/*
 * For debugging: check whether n is a power of two
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


/*
 * Initialize set
 * - n = initial size
 * - n must be a power of 2. If n = 0, the default size is used.
 */
void init_int_array_hset(int_array_hset_t *set, uint32_t n) {
  uint32_t i;
  harray_t **tmp;

  if (n == 0) {
    n = DEF_INT_ARRAY_HSET_SIZE;
  }

  if (n >= MAX_INT_ARRAY_HSET_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));

  tmp = (harray_t **) safe_malloc(n * sizeof(harray_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  set->data = tmp;
  set->size = n;
  set->nelems = 0;
  set->ndeleted = 0;

  set->resize_threshold = (uint32_t) (n * INT_ARRAY_HSET_RESIZE_RATIO);
  set->cleanup_threshold = (uint32_t) (n * INT_ARRAY_HSET_CLEANUP_RATIO);
}


/*
 * Check whether p is a non-deleted/non-null pointer
 */
static inline bool live_harray(harray_t *p) {
  return p != NULL && p != DELETED_HARRAY;
}


/*
 * Delete the set
 */
void delete_int_array_hset(int_array_hset_t *set) {
  harray_t *p;
  uint32_t i, n;

  n = set->size;
  for (i=0; i<n; i++) {
    p = set->data[i];
    if (live_harray(p)) safe_free(p);
  }
  safe_free(set->data);
  set->data = NULL;
}


/*
 * Empty the set
 */
void reset_int_array_hset(int_array_hset_t *set) {
  harray_t *p;
  uint32_t i, n;

  n = set->size;
  for (i=0; i<n; i++) {
    p = set->data[i];
    if (live_harray(p)) safe_free(p);
    set->data[i] = NULL;
  }
  set->nelems = 0;
  set->ndeleted = 0;
}


/*
 * Store p in a clean data array
 * - mask = size of data - 1 (the size must be a power of 2)
 * - p->hash must be the correct hash code for p
 * - data must not contain DELETED_HARRAY marks and must have room for p
 */
static void int_array_hset_clean_copy(harray_t **data, const harray_t *p, uint32_t mask) {
  uint32_t i;

  i = p->hash & mask;
  while (data[i] != NULL) {
    i ++;
    i &= mask;
  }
  data[i] = p;
}


/*
 * Remove all deletion markers from set
 */
static void int_array_hset_cleanup(int_array_hset_t *set) {
  harray_t **tmp, *p;
  uint32_t i, n, mask;

  n = set->size;
  tmp = (harray_t **) safe_malloc(n * sizeof(harray_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  mask = n - 1;
  for (i=0; i<n; i++) {
    p = set->data[i];
    if (live_harray(p)) {
      int_array_hset_clean_copy(tmp, p, mask);
    }
  }

  safe_free(set->data);
  set->data = tmp;
  set->ndeleted = 0;
}


/*
 * Remove all deletion markers and make the set twice larger
 */
static void int_array_hset_extend(int_array_hset_t *set) {
  harray_t **tmp, *p;
  uint32_t i, n, mask, new_size;

  n = set->size;
  new_size = n << 1;
  if (new_size >= MAX_INT_ARRAY_HSET_SIZE) {
    out_of_memory();
  }

  tmp = (harray_t **) safe_malloc(new_size * sizeof(harray_t *));
  for (i=0; i<new_size; i++) {
    tmp[i] = NULL;
  }

  mask = new_size - 1;
  for (i=0; i<n; i++) {
    p = set->data[i];
    if (live_harray(p)) {
      int_array_hset_clean_copy(tmp, p, mask);
    }
  }

  safe_free(set->data);
  set->data = tmp;
  set->size = new_size;
  set->ndeleted = 0;

  set->resize_threshold = (uint32_t) (new_size * INT_ARRAY_HSET_RESIZE_RATIO);
  set->cleanup_threshold = (uint32_t) (new_size * INT_ARRAY_HSET_CLEANUP_RATIO);
}


/*
 * Search for array a[0 ... n-1]
 */
harray_t *int_array_hset_find(const int_array_hset_t *set, uint32_t n, const int32_t *a) {
  harray_t *p;
  uint32_t i, h, mask;

  assert(set->nelems + set->ndeleted < set->size);

  mask = set->size - 1;
  h = hash_array(a, n);
  i = h & mask;
  for (;;) {
    p = set->data[i];
    if (p == NULL || (p != DELETED_HARRAY && p->hash == h && eq_harray(p, a, n))) {
      return p;
    }
    i ++;
    i &= mask;
  }
}


/*
 * Find or create descriptor for a[0...n-1]
 */
harray_t *int_array_hset_get(int_array_hset_t *set, uint32_t n, const int32_t *a) {
  harray_t *p;
  uint32_t i, j, h, mask;

  assert(set->nelems + set->ndeleted < set->size);

  mask = set->size - 1;
  h = hash_array(a, n);
  i = h & mask;
  for (;;) {
    p = set->data[i];
    if (p == NULL) goto add;
    if (p == DELETED_HARRAY) break;
    if (p->hash == h && eq_harray(p, a, n)) goto found;
    i ++;
    i &= mask;
  }

  // set->data[i] = where new set can be added
  j = i;
  for (;;) {
    j ++;
    j &= mask;
    p = set->data[j];
    if (p == NULL) {
      set->ndeleted --;
      goto add;
    }
    if (p != DELETED_HARRAY && p->hash == h && eq_harray(p, a, n)) goto found;
  }

 add:
  p = make_harray(a, n);
  p->hash = h;
  set->data[i] = p;
  set->nelems ++;
  if (set->nelems + set->ndeleted > set->resize_threshold) {
    int_array_hset_extend(set);
  }

 found:
  return p;
}


/*
 * Remove a from the set
 * - no change if a is not in the set
 */
void int_array_hset_remove(int_array_hset_t *set, uint32_t n, const int32_t *a) {
  harray_t *p;
  uint32_t i, h, mask;

  assert(set->nelems + set->ndeleted < set->size);

  mask = set->size - 1;
  h = hash_array(a, n);
  i = h & mask;
  for (;;) {
    p = set->data[i];
    if (p == NULL) return;
    if (p != DELETED_HARRAY && p->hash == h && eq_harray(p, a, n)) break;
    i ++;
    i &= mask;
  }

  // remove p
  safe_free(p);
  set->data[i] = DELETED_HARRAY;
  set->nelems --;
  set->ndeleted ++;

  if (set->ndeleted > set->cleanup_threshold) {
    int_array_hset_cleanup(set);
  }
}


/*
 * Remove all arrays that satisfy f
 * - for every array a in the table, call f(aux, a)
 * - if that returns true, then a is deleted
 * - f must not have side effects
 */
void int_array_hset_remove_arrays(int_array_hset_t *set, void *aux, int_array_hset_filter_t f) {
  harray_t *p;
  uint32_t i, n, k;

  n = set->size;
  k = 0;
  for (i=0; i<n; i++) {
    p = set->data[i];
    if (live_harray(p) && f(aux, p)) {
      // remove p
      safe_free(p);
      set->data[i] = DELETED_HARRAY;
      k ++;
    }
  }

  // k = number of deletions
  assert(k <= set->nelems);
  set->nelems -= k;
  set->ndeleted += k;
  if (set->ndeleted > set->cleanup_threshold) {
    int_array_hset_cleanup(set);
  }
}

