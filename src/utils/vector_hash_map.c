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
 * Table to map integer keys to an array of integers (vector)
 */

#include <assert.h>
#include <stdbool.h>

#include "utils/memalloc.h"
#include "utils/vector_hash_map.h"


/*
 * Allocate a new vector of default size for key k
 */
static vhmap_vector_t *new_vhmap_vector(int32_t k) {
  vhmap_vector_t *tmp;
  uint32_t n;

  n = DEF_VECTOR_HMAP_SIZE;
  tmp = (vhmap_vector_t *) safe_malloc(sizeof(vhmap_vector_t) + n * sizeof(int32_t));
  tmp->key = k;
  tmp->size = n;
  tmp->nelems = 0;

  return tmp;
}

/*
 * Add x to vector v: v must not be full
 */
static void vhmap_vector_add(vhmap_vector_t *v, int32_t x) {
  uint32_t i;

  i = v->nelems;
  assert(i < v->size);
  v->data[i] = x;
  v->nelems = i+1;
}


/*
 * Check whether v is full
 */
static inline bool vhmap_vector_is_full(vhmap_vector_t *v) {
  return v->nelems == v->size;
}

/*
 * Increase v's size by 50%
 */
static vhmap_vector_t *extend_vhmap_vector(vhmap_vector_t *v) {
  vhmap_vector_t *tmp;
  uint32_t n;  

  n = v->size;
  n += (n >> 1);
  if (n > MAX_VECTOR_HMAP_SIZE) {
    out_of_memory();
  }

  tmp = (vhmap_vector_t *) safe_realloc(v, sizeof(vhmap_vector_t) + n * sizeof(int32_t));
  tmp->size = n;

  return tmp;
}


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
 * - n = initial size. It must be a power of 2 or 0.
 * - if n = 0, the default size is used.
 */
void init_vector_hmap(vector_hmap_t *hmap, uint32_t n) {
  vhmap_vector_t **tmp;
  uint32_t i;

  if (n == 0) {
    n = DEF_VECTOR_HMAP_SIZE;
  }
  if (n > MAX_VECTOR_HMAP_SIZE) {
    out_of_memory();
  }
  assert(is_power_of_two(n));

  tmp = (vhmap_vector_t **) safe_malloc(n * sizeof(vhmap_vector_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }
  hmap->data = tmp;
  hmap->size = n;
  hmap->nelems = 0;
  hmap->resize_threshold = (uint32_t) (n * VECTOR_HMAP_RESIZE_RATIO);
}


/*
 * Empty the table
 */
void reset_vector_hmap(vector_hmap_t *hmap) {
  uint32_t i, n;

  n = hmap->size;
  for (i=0; i<n; i++) {
    if (hmap->data[i] != NULL) {
      safe_free(hmap->data[i]);
      hmap->data[i] = NULL;
    }
  }
  hmap->nelems = 0;
}


/*
 * Delete: free memory
 */
void delete_vector_hmap(vector_hmap_t *hmap) {
  reset_vector_hmap(hmap);
  safe_free(hmap->data);
  hmap->data = NULL;
}


/*
 * Hash of a key (Jenkins hash)
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
 * Store v into a clean array a:
 * - mask = size of a - 1 where the size is a power of two
 * - the array must not be full
 */
static void vector_hmap_clean_copy(vhmap_vector_t **a, vhmap_vector_t *v, uint32_t mask) {
  uint32_t i;

  i = hash_key(v->key) & mask;
  while (a[i] != NULL) {
    i ++;
    i &= mask;
  }
  a[i] = v;
}


/*
 * Make the table twice as large. Keep the content
 */
static void extend_vector_hmap(vector_hmap_t *hmap) {
  vhmap_vector_t **tmp;
  vhmap_vector_t *v;
  uint32_t i, n, new_size, mask;

  n = hmap->size;
  new_size = n << 1;
  if (new_size > MAX_VECTOR_HMAP_SIZE) {
    out_of_memory();
  }

  tmp = (vhmap_vector_t **) safe_malloc(new_size * sizeof(vhmap_vector_t *));
  for (i=0; i<new_size; i++) {
    tmp[i] = NULL;
  }

  assert(is_power_of_two(new_size));
  mask = new_size - 1;
  for (i=0; i<n; i++) {
    v = hmap->data[i];
    if (v != NULL) {
      vector_hmap_clean_copy(tmp, v, mask);
    }
  }

  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->size = new_size;
  hmap->resize_threshold = (uint32_t) (new_size * VECTOR_HMAP_RESIZE_RATIO);
}


/*
 * Get the vector of key k
 * - return NULL if there's no vector of key k
 */
vhmap_vector_t *vector_hmap_find(const vector_hmap_t *hmap, int32_t k) {
  vhmap_vector_t *v;
  uint32_t i, mask;

  assert(is_power_of_two(hmap->size) && hmap->nelems < hmap->size);

  mask = hmap->size - 1;
  i = hash_key(k) & mask;
  for (;;) {
    v = hmap->data[i];
    if (v == NULL || v->key == k) break;
    i ++;
    i &= mask;    
  }

  return v;
}

/*
 * Add a fresh vector v to the table:
 * - k = key
 * - x = element to store in v
 * - i = index in hmap->data to store v
 */
static void vector_hmap_add_new(vector_hmap_t *hmap, int32_t k, int32_t x, uint32_t i) {
  vhmap_vector_t *v;

  assert(i < hmap->size && hmap->data[i] == NULL);

  v = new_vhmap_vector(k);
  vhmap_vector_add(v, x);
  hmap->data[i] = v;
  hmap->nelems ++;
  if (hmap->nelems >= hmap->resize_threshold) {
    extend_vector_hmap(hmap);
  }
}

/*
 * Add element x to an existing vector v at index i
 */
static void vector_hmap_add_to_vector(vector_hmap_t *hmap, vhmap_vector_t *v, int32_t x, uint32_t i)  {
  assert(i < hmap->size && hmap->data[i] == v);

  if (vhmap_vector_is_full(v)) {
    v = extend_vhmap_vector(v);
    hmap->data[i] = v;
  }
  vhmap_vector_add(v, x);
}

/*
 * Add element x to the vector of key k
 * - this creates a new vector if k is not already in the table.
 */
void vector_hmap_add(vector_hmap_t *hmap, int32_t k, int32_t x) {
  vhmap_vector_t *v;
  uint32_t i, mask;

  assert(is_power_of_two(hmap->size) && hmap->nelems < hmap->size);

  mask = hmap->size - 1;
  i = hash_key(k) & mask;
  for (;;) {
    v = hmap->data[i];
    if (v == NULL) {
      vector_hmap_add_new(hmap, k, x, i);
      break;
    }
    if (v->key == k) {
      vector_hmap_add_to_vector(hmap, v, x, i);
      break;
    }
    i ++;
    i &= mask;
  }
}

