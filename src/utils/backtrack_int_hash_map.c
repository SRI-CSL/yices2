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
 * HASH MAPS WITH SUPPORT FOR PUSH/POP
 *
 * keys and values are signed 32bit integers that must be non-negative.
 */

#include <assert.h>
#include <stdbool.h>

#include "utils/backtrack_int_hash_map.h"
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
 * Hash of a key (Jenkins hash)
 */
static uint32_t hash_key(int32_t k) {
  uint32_t x;

  assert(k >= 0);

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
 * DATA ARRAYS
 */

/*
 * Allocate and initialize arrays pair/level
 * - n = size of both arrays
 */
static void alloc_data_arrays(back_hmap_data_t *data, uint32_t n) {
  uint32_t i;

  data->pair = (back_hmap_elem_t *) safe_malloc(n * sizeof(back_hmap_elem_t));
  data->level = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  for (i=0; i<n; i++) {
    data->pair[i].key = BACK_HMAP_EMPTY_KEY;
  }
}

/*
 * Free both arrays
 */
static void free_data_arrays(back_hmap_data_t *data) {
  safe_free(data->pair);
  safe_free(data->level);
  data->pair = NULL;
  data->level = NULL;
}

/*
 * Reset all keys to empty:
 * - n = size of both arrays
 */
static void reset_data_arrays(back_hmap_data_t *data, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    data->pair[i].key = BACK_HMAP_EMPTY_KEY;
  }
}


/*
 * Copy pair p and level l into a clean data array d
 * - mask = size of d - 1, where size of d is a power of 2
 * - d must not be full
 */
static void back_hmap_clean_copy(back_hmap_data_t *d, const back_hmap_elem_t *p, uint32_t l, uint32_t mask) {
  uint32_t i;

  i = hash_key(p->key) & mask;
  while (d->pair[i].key >= 0) {
    i ++;
    i &= mask;
  }

  assert(d->pair[i].key == BACK_HMAP_EMPTY_KEY);
  
  d->pair[i] = *p;
  d->level[i] = l;
}


/*
 * Copy all elements with a positive key from s to d
 * - d is a clean array
 * - preserve the levels.
 * - n = size of d
 * - m = size of s
 */
static void back_hmap_clean_copy_all(back_hmap_data_t *d, const back_hmap_data_t *s, uint32_t n, uint32_t m) {
  const back_hmap_elem_t *e;
  uint32_t i, mask;
  
  assert(n >= m && is_power_of_two(n));

  mask = n-1;

  e = s->pair;
  for (i=0; i<m; i++) {
    if (e->key >= 0) {
      back_hmap_clean_copy(d, e, s->level[i], mask);
    }
    e ++;
  }
}


/*
 * Search for key k in d->pair
 * - mask = size of d - 1 (the size is a power of two)
 * - return NULL if it's not found
 * - return the pair with key == k otherwise
 */
static back_hmap_elem_t *find(const back_hmap_data_t *d, int32_t k, uint32_t mask) {
  back_hmap_elem_t *e;
  uint32_t i;

  i = hash_key(k) & mask;
  for (;;) {
    e = d->pair + i;
    if (e->key == k) return e;
    if (e->key == BACK_HMAP_EMPTY_KEY) return NULL;
    i ++;
    i &= mask;
  }
}


/*
 * Create a fresh entry with key k and  val = -1 at level l.
 * - mask = size of d - 1
 * - d->pair must not be full and contain only valid or empty keys
 *   (i.e., nothing DELETED).
 * - return a pointer to the new entry
 */
static back_hmap_elem_t *get_clean(back_hmap_data_t *d, int32_t k, uint32_t l, uint32_t mask) {
  uint32_t i;

  i = hash_key(k) & mask;
  while (d->pair[i].key >= 0) {
    i ++;
    i &= mask;
  }

  assert(d->pair[i].key == BACK_HMAP_EMPTY_KEY);

  d->pair[i].key = k;
  d->pair[i].val = -1;
  d->level[i] = l;

  return d->pair + i;
}


/*
 * Mark all elements of d with level >= l as deleted
 * - n = size of d
 * return the number of elements removed.
 */
static uint32_t erase_level(back_hmap_data_t *d, uint32_t l, uint32_t n) {
  back_hmap_elem_t *e;
  uint32_t i, deletions;

  deletions = 0;

  e = d->pair;
  for (i=0; i<n; i++) {
    if (e->key >= 0 && d->level[i] >= l) {
      e->key = BACK_HMAP_DELETED_KEY;
      deletions ++;
    }
    e ++;
  }

  return deletions;
}


/*
 * HMAP
 */

/*
 * Initialization:
 * - n = initial size, must be a power of 2
 * - if n = 0, the default size is used
 */
void init_back_hmap(back_hmap_t *hmap, uint32_t n) {
  if (n == 0) {
    n = BACK_HMAP_DEF_SIZE;
  }
  if (n > BACK_HMAP_MAX_SIZE) {
    out_of_memory();
  }
  assert(is_power_of_two(n) && n>0);

  alloc_data_arrays(&hmap->data, n);
  hmap->size = n;
  hmap->nelems = 0;
  hmap->ndeleted = 0;
  hmap->resize_threshold = (uint32_t)(n * BACK_HMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t) (n * BACK_HMAP_CLEANUP_RATIO);
  hmap->level = 0;
}


/*
 * Free memory
 */
void delete_back_hmap(back_hmap_t *hmap) {
  free_data_arrays(&hmap->data);
}


/*
 * Empty the table and reset level to 0
 */
void reset_back_hmap(back_hmap_t *hmap) {
  reset_data_arrays(&hmap->data, hmap->size);
  hmap->nelems = 0;
  hmap->ndeleted = 0;
  hmap->level = 0;
}


/*
 * Find entry with key = k.
 * - return NULL if there's no such entry
 */
back_hmap_elem_t *back_hmap_find(const back_hmap_t *hmap, int32_t k) {
  assert(is_power_of_two(hmap->size) && hmap->size > 0);
  return find(&hmap->data, k, hmap->size - 1);
}


/*
 * Double the size of the table and remove all deleted entries
 */
static void back_hmap_extend(back_hmap_t *hmap) {
  back_hmap_data_t aux;
  uint32_t n, new_size;

  n = hmap->size;
  new_size = n << 1;

  if (new_size > BACK_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(new_size));
  
  alloc_data_arrays(&aux, new_size);
  back_hmap_clean_copy_all(&aux, &hmap->data, new_size, n);
  free_data_arrays(&hmap->data);
  hmap->data = aux;

  hmap->size = new_size;
  hmap->ndeleted = 0;
  hmap->resize_threshold = (uint32_t) (new_size * BACK_HMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t) (new_size * BACK_HMAP_CLEANUP_RATIO);
}


/*
 * Remove all deleted entries. Keep the same size.
 */
static void back_hmap_cleanup(back_hmap_t *hmap) {
  back_hmap_data_t aux;
  uint32_t n;

  n = hmap->size;

  assert(is_power_of_two(n));

  alloc_data_arrays(&aux, n);
  back_hmap_clean_copy_all(&aux, &hmap->data, n, n);
  free_data_arrays(&hmap->data);
  hmap->data = aux;

  hmap->ndeleted = 0;
}


/*
 * Find or add an entry with key = k.
 * - if the key is not already there, a new record is created with key=k,
 *   and val=-1 at the current level.
 */
back_hmap_elem_t *back_hmap_get(back_hmap_t *hmap, int32_t k) {
  back_hmap_elem_t *d, *aux;
  uint32_t i, j, mask;

  assert(is_power_of_two(hmap->size) && hmap->size > 0);
  assert(hmap->size > hmap->ndeleted + hmap->nelems);

  mask = hmap->size - 1;
  i = hash_key(k) & mask;

  for (;;) {
    d = hmap->data.pair + i;
    if (d->key == k) return d;
    if (d->key < 0) break;
    i ++;
    i &= mask;
  }

  aux = d; // we'll add in this location
  j = i;

  while (d->key != BACK_HMAP_EMPTY_KEY) {
    i ++;
    i &= mask;
    d = hmap->data.pair + i;
    if (d->key == k) return d;
  }

  // k is not in the table
  if (hmap->nelems + hmap->ndeleted >= hmap->resize_threshold) {
    back_hmap_extend(hmap);
    aux = get_clean(&hmap->data, k, hmap->level, hmap->size - 1);
    hmap->nelems ++;
  } else {
    if (aux->key == BACK_HMAP_DELETED_KEY) {
      assert(hmap->ndeleted > 0);
      hmap->ndeleted --;
    }
    hmap->nelems ++;
    aux->key = k;
    aux->val = -1;
    hmap->data.level[j] = hmap->level;
  }

  return aux;
}


/*
 * Backtrack to the previous level: remove all elements
 * added at the current level.
 * - hmap->level must be positive
 */
void back_hmap_pop(back_hmap_t *hmap) {
  uint32_t d;
  assert(hmap->level > 0);

  d = erase_level(&hmap->data, hmap->level, hmap->size);
  hmap->ndeleted += d;
  hmap->nelems -= d;
  hmap->level --;
  if (hmap->ndeleted >= hmap->cleanup_threshold) {
    back_hmap_cleanup(hmap);
  }
}
