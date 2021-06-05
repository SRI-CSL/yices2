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
 * HASH MAPS
 * - keys are 32bit integers, values are void * pointers
 * - keys are assumed positive, -1 and -2 are special markers
 */

#include <stdbool.h>
#include <assert.h>

#include "utils/memalloc.h"
#include "utils/ptr_hash_map.h"


/*
 * For debugging: check whether n is a power of two
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
void init_ptr_hmap(ptr_hmap_t *hmap, uint32_t n) {
  uint32_t i;
  ptr_hmap_pair_t *tmp;

  if (n == 0) {
    n = PTR_HMAP_DEFAULT_SIZE;
  }

  if (n >= PTR_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));

  tmp = (ptr_hmap_pair_t *) safe_malloc(n * sizeof(ptr_hmap_pair_t));
  for (i=0; i<n; i++) {
    tmp[i].key = PHMAP_EMPTY_KEY;
  }

  hmap->data = tmp;
  hmap->size = n;
  hmap->nelems = 0;
  hmap->ndeleted = 0;

  hmap->resize_threshold = (uint32_t)(n * PTR_HMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t) (n * PTR_HMAP_CLEANUP_RATIO);
}


/*
 * Free memory
 */
void delete_ptr_hmap(ptr_hmap_t *hmap) {
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
 * Make a copy of record d in a clean array data
 * - mask = size of data - 1 (size must be a power of 2)
 */
static void ptr_hmap_clean_copy(ptr_hmap_pair_t *data, ptr_hmap_pair_t *d, uint32_t mask) {
  uint32_t j;

  j = hash_key(d->key) & mask;
  while (data[j].key != PHMAP_EMPTY_KEY) {
    j ++;
    j &= mask;
  }

  data[j].key = d->key;
  data[j].val = d->val;
}


/*
 * Remove deleted records
 */
static void ptr_hmap_cleanup(ptr_hmap_t *hmap) {
  ptr_hmap_pair_t *tmp, *d;
  uint32_t j, n, mask;

  n = hmap->size;
  tmp = (ptr_hmap_pair_t *) safe_malloc(n * sizeof(ptr_hmap_pair_t));
  for (j=0; j<n; j++) {
    tmp[j].key = PHMAP_EMPTY_KEY;
  }

  mask = n - 1;
  d = hmap->data;
  for (j=0; j<n; j++) {
    if (d->key >= 0) {
      ptr_hmap_clean_copy(tmp, d, mask);
    }
    d++;
  }

  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->ndeleted = 0;
}


/*
 * Remove deleted records and make the table twice as large
 */
static void ptr_hmap_extend(ptr_hmap_t *hmap) {
  ptr_hmap_pair_t *tmp, *d;
  uint32_t j, n, n2, mask;

  n = hmap->size;
  n2 = n << 1;
  if (n2 >= PTR_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  tmp = (ptr_hmap_pair_t *) safe_malloc(n2 * sizeof(ptr_hmap_pair_t));
  for (j=0; j<n2; j++) {
    tmp[j].key = PHMAP_EMPTY_KEY;
  }

  mask = n2 - 1;
  d = hmap->data;
  for (j=0; j<n; j++) {
    if (d->key >= 0) {
      ptr_hmap_clean_copy(tmp, d, mask);
    }
    d ++;
  }

  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->size = n2;
  hmap->ndeleted = 0;

  hmap->resize_threshold = (uint32_t)(n2 * PTR_HMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t)(n2 * PTR_HMAP_CLEANUP_RATIO);
}


/*
 * Find record with key k
 * - return NULL if k is not in the table
 */
ptr_hmap_pair_t *ptr_hmap_find(const ptr_hmap_t *hmap, int32_t k) {
  uint32_t mask, j;
  ptr_hmap_pair_t *d;

  assert(k >= 0);

  mask = hmap->size - 1;
  j = hash_key(k) & mask;
  for (;;) {
    d = hmap->data + j;
    if (d->key == k) return d;
    if (d->key == PHMAP_EMPTY_KEY) return NULL;
    j ++;
    j &= mask;
  }
}


/*
 * Add record with key k after hmap was extended:
 * - initialize val to NULL
 * - we know that no record with key k is present
 */
static ptr_hmap_pair_t *ptr_hmap_get_clean(ptr_hmap_t *hmap, int32_t k) {
  uint32_t mask, j;
  ptr_hmap_pair_t *d;

  mask = hmap->size - 1;
  j = hash_key(k) & mask;
  for (;;) {
    d = hmap->data + j;
    if (d->key < 0) {
      hmap->nelems ++;
      d->key = k;
      d->val = NULL;
      return d;
    }
    j ++;
    j &= mask;
  }
}


/*
 * Find or add record with key k
 */
ptr_hmap_pair_t *ptr_hmap_get(ptr_hmap_t *hmap, int32_t k) {
  uint32_t mask, j;
  ptr_hmap_pair_t *d, *aux;

  assert(k >= 0);
  assert(hmap->size > hmap->ndeleted + hmap->nelems);

  mask = hmap->size - 1;
  j = hash_key(k) & mask;

  for (;;) {
    d = hmap->data + j;
    if (d->key == k) return d;
    if (d->key < 0) break;
    j ++;
    j &= mask;
  }

  aux = d; // new record, if needed, will be aux
  while (d->key != PHMAP_EMPTY_KEY) {
    j ++;
    j &= mask;
    d = hmap->data + j;
    if (d->key == k) return d;
  }

  if (aux->key == PHMAP_DEL_KEY) {
    assert(hmap->ndeleted > 0);
    hmap->ndeleted --;
  }

  if (hmap->nelems + hmap->ndeleted >= hmap->resize_threshold) {
    ptr_hmap_extend(hmap);
    aux = ptr_hmap_get_clean(hmap, k);
  } else {
    hmap->nelems ++;
    aux->key = k;
    aux->val = NULL;
  }

  return aux;
}


/*
 * Erase record r
 */
void ptr_hmap_erase(ptr_hmap_t *hmap, ptr_hmap_pair_t *r) {
  assert(ptr_hmap_find(hmap, r->key) == r);

  r->key = PHMAP_DEL_KEY;
  hmap->nelems --;
  hmap->ndeleted ++;
  if (hmap->ndeleted > hmap->cleanup_threshold) {
    ptr_hmap_cleanup(hmap);
  }
}


/*
 * Empty the map
 */
void ptr_hmap_reset(ptr_hmap_t *hmap) {
  uint32_t i, n;
  ptr_hmap_pair_t *d;

  n = hmap->size;
  d = hmap->data;
  for (i=0; i<n; i++) {
    d->key = PHMAP_EMPTY_KEY;
    d ++;
  }

  hmap->nelems = 0;
  hmap->ndeleted = 0;
}


/*
 * Remove all records that satisfy f
 * - for every record r in the table, call f(aux, r)
 * - if that returns true, then the record r is deleted
 * - f must not have side effects
 */
void ptr_hmap_remove_records(ptr_hmap_t *hmap, void *aux, ptr_hmap_filter_t f) {
  ptr_hmap_pair_t *d;
  uint32_t i, n, k;

  n = hmap->size;
  d = hmap->data;
  k = 0;
  for (i=0; i<n; i++) {
    if (d->key >= 0 && f(aux, d)) {
      d->key = PHMAP_DEL_KEY;
      k ++;
    }
  }

  // k = number of deletions
  assert(k <= hmap->nelems);
  hmap->nelems -= k;
  hmap->ndeleted += k;
  if (hmap->ndeleted >= hmap->cleanup_threshold) {
    ptr_hmap_cleanup(hmap);
  }
}



/*
 * First non-empty record in the table, starting from p
 */
static const ptr_hmap_pair_t *ptr_hmap_get_next(const ptr_hmap_t *hmap, const ptr_hmap_pair_t *p) {
  ptr_hmap_pair_t *end;

  end = hmap->data + hmap->size;
  while (p < end) {
    if (p->key >= 0) return p;
    p ++;
  }

  return NULL;
}


/*
 * Get the first non-empty record or NULL if the table is empty
 */
ptr_hmap_pair_t *ptr_hmap_first_record(const ptr_hmap_t *hmap) {
  return (ptr_hmap_pair_t *) ptr_hmap_get_next(hmap, hmap->data);
}


/*
 * Next record after p or NULL
 */
ptr_hmap_pair_t *ptr_hmap_next_record(const ptr_hmap_t *hmap, const ptr_hmap_pair_t *p) {
  assert(p != NULL && p<hmap->data + hmap->size && p->key >= 0);
  return (ptr_hmap_pair_t *) ptr_hmap_get_next(hmap, p+1);
}


