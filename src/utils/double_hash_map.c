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
 * MAPS 32BIT INTEGERS TO DOUBLES (adapted from int_hash_map)
 * Assumes that keys are non-negative
 */

#include <assert.h>
#include <string.h>

#include "utils/memalloc.h"

#include "double_hash_map.h"

/*
 * For debugging: check whether n is 0 or a power of 2
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif

/*
 * Markers for empty/deleted pairs
 */
enum {
  DELETED_KEY = -2,
  EMPTY_KEY = -1,
};

/*
 * Initialization:
 * - n = initial size, must be a power of 2
 * - if n = 0, the default size is used
 */
void init_double_hmap(double_hmap_t *hmap, uint32_t n) {
  uint32_t i;
  double_hmap_pair_t *tmp;

  if (n == 0) {
    n = DOUBLE_HMAP_DEFAULT_SIZE;
  }

  if (n >= DOUBLE_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));

  tmp = (double_hmap_pair_t *) safe_malloc(n * sizeof(double_hmap_pair_t));
  for (i=0; i<n; i++) {
    tmp[i].key = EMPTY_KEY;
  }

  hmap->data = tmp;
  hmap->size = n;
  hmap->nelems = 0;
  hmap->ndeleted = 0;

  hmap->resize_threshold = (uint32_t)(n * DOUBLE_HMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t) (n * DOUBLE_HMAP_CLEANUP_RATIO);
}


/*
 * Free memory
 */
void delete_double_hmap(double_hmap_t *hmap) {
  safe_free(hmap->data);
  hmap->data = NULL;
}

/*
 * Swap m1 and m2
 */
void double_hmap_swap(double_hmap_t *m1, double_hmap_t *m2) {
  double_hmap_t aux;

  aux = *m1;
  *m1 = *m2;
  *m2 = aux;
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
static void double_hmap_clean_copy(double_hmap_pair_t *data, double_hmap_pair_t *d, uint32_t mask) {
  uint32_t j;

  j = hash_key(d->key) & mask;
  while (data[j].key != EMPTY_KEY) {
    j ++;
    j &= mask;
  }

  data[j].key = d->key;
  data[j].val = d->val;
}


/*
 * Remove deleted records
 */
static void double_hmap_cleanup(double_hmap_t *hmap) {
  double_hmap_pair_t *tmp, *d;
  uint32_t j, n, mask;

  n = hmap->size;
  tmp = (double_hmap_pair_t *) safe_malloc(n * sizeof(double_hmap_pair_t));
  for (j=0; j<n; j++) {
    tmp[j].key = EMPTY_KEY;
  }

  mask = n - 1;
  d = hmap->data;
  for (j=0; j<n; j++) {
    if (d->key >= 0) {
      double_hmap_clean_copy(tmp, d, mask);
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
static void double_hmap_extend(double_hmap_t *hmap) {
  double_hmap_pair_t *tmp, *d;
  uint32_t j, n, n2, mask;

  n = hmap->size;
  n2 = n << 1;
  if (n2 >= DOUBLE_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  tmp = (double_hmap_pair_t *) safe_malloc(n2 * sizeof(double_hmap_pair_t));
  for (j=0; j<n2; j++) {
    tmp[j].key = EMPTY_KEY;
  }

  mask = n2 - 1;
  d = hmap->data;
  for (j=0; j<n; j++) {
    if (d->key >= 0) {
      double_hmap_clean_copy(tmp, d, mask);
    }
    d ++;
  }

  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->size = n2;
  hmap->ndeleted = 0;

  hmap->resize_threshold = (uint32_t)(n2 * DOUBLE_HMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t)(n2 * DOUBLE_HMAP_CLEANUP_RATIO);
}


/*
 * Find record with key k
 * - return NULL if k is not in the table
 */
double_hmap_pair_t *double_hmap_find(const double_hmap_t *hmap, int32_t k) {
  uint32_t mask, j;
  double_hmap_pair_t *d;

  assert(k >= 0);

  mask = hmap->size - 1;
  j = hash_key(k) & mask;
  for (;;) {
    d = hmap->data + j;
    if (d->key == k) return d;
    if (d->key == EMPTY_KEY) return NULL;
    j ++;
    j &= mask;
  }
}


/*
 * Add record with key k after hmap was extended:
 * - initialize val to -1
 * - we know that no record with key k is present
 */
static double_hmap_pair_t *double_hmap_get_clean(double_hmap_t *hmap, int32_t k) {
  uint32_t mask, j;
  double_hmap_pair_t *d;

  mask = hmap->size - 1;
  j = hash_key(k) & mask;
  for (;;) {
    d = hmap->data + j;
    if (d->key < 0) {
      hmap->nelems ++;
      d->key = k;
      d->val = -1;
      return d;
    }
    j ++;
    j &= mask;
  }
}


/*
 * Find or add record with key k
 */
double_hmap_pair_t *double_hmap_get(double_hmap_t *hmap, int32_t k) {
  uint32_t mask, j;
  double_hmap_pair_t *d, *aux;

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
  while (d->key != EMPTY_KEY) {
    j ++;
    j &= mask;
    d = hmap->data + j;
    if (d->key == k) return d;
  }

  if (aux->key == DELETED_KEY) {
    assert(hmap->ndeleted > 0);
    hmap->ndeleted --;
  }

  if (hmap->nelems + hmap->ndeleted >= hmap->resize_threshold) {
    double_hmap_extend(hmap);
    aux = double_hmap_get_clean(hmap, k);
  } else {
    hmap->nelems ++;
    aux->key = k;
    aux->val = -1;
  }

  return aux;
}


/*
 * Add record [k -> v ] to hmap
 * - there must not be a record with the same key
 */
void double_hmap_add(double_hmap_t *hmap, int32_t k, double v) {
  uint32_t i, mask;

  assert(k >= 0 && hmap->nelems + hmap->ndeleted < hmap->size);

  mask = hmap->size - 1;
  i = hash_key(k) & mask;
  while (hmap->data[i].key >= 0) {
    assert(hmap->data[i].key != k);
    i ++;
    i &= mask;
  }

  // store the new record in data[i]
  if (hmap->data[i].key == DELETED_KEY) {
    assert(hmap->ndeleted > 0);
    hmap->ndeleted --;
  }
  hmap->data[i].key = k;
  hmap->data[i].val = v;
  hmap->nelems ++;

  if (hmap->nelems + hmap->ndeleted >= hmap->resize_threshold) {
    double_hmap_extend(hmap);
  }
}


/*
 * Add record [k -> v ] to hmap
 * - if there is a record with the same key, it is replaced by the new record
 */
void double_hmap_add_replace(double_hmap_t *hmap, int32_t k, double v) {
  double_hmap_pair_t* record = double_hmap_find(hmap, k);
  if (record != NULL){
    double_hmap_erase(hmap, record);
  }
  double_hmap_add(hmap, k, v);
}

/*
 * Add record [k -> v ] to hmap
 * - if there is a record with the same key, it does not replace it (but does not throw an error)
 */
void double_hmap_add_not_replace(double_hmap_t *hmap, int32_t k, double v) {
  double_hmap_pair_t* record = double_hmap_find(hmap, k);
  if (record == NULL){
    double_hmap_add(hmap, k, v);
  }
}


/*
 * Erase record r
 */
void double_hmap_erase(double_hmap_t *hmap, double_hmap_pair_t *r) {
  assert(double_hmap_find(hmap, r->key) == r);

  r->key = DELETED_KEY;
  hmap->nelems --;
  hmap->ndeleted ++;
  if (hmap->ndeleted >= hmap->cleanup_threshold) {
    double_hmap_cleanup(hmap);
  }
}

/*
 * Deep copy one map to another
 */
extern void double_hmap_copy(double_hmap_t *hmap_to, const double_hmap_t *hmap_from) {
  hmap_to->size = hmap_from->size;
  hmap_to->nelems = hmap_from->nelems;
  hmap_to->ndeleted = hmap_from->ndeleted;
  hmap_to->resize_threshold = hmap_from->resize_threshold;
  hmap_to->cleanup_threshold = hmap_from->cleanup_threshold;
  hmap_to->data = safe_realloc(hmap_to->data, hmap_from->size * sizeof(double_hmap_pair_t));
  memcpy(hmap_to->data, hmap_from->data, hmap_from->size * sizeof(double_hmap_pair_t));
}


/*
 * Empty the map
 */
void double_hmap_reset(double_hmap_t *hmap) {
  uint32_t i, n;
  double_hmap_pair_t *d;

  n = hmap->size;
  d = hmap->data;
  for (i=0; i<n; i++) {
    d->key = EMPTY_KEY;
    d ++;
  }

  hmap->nelems = 0;
  hmap->ndeleted = 0;
}



/*
 * First non-empty record in the table, starting from p
 */
static const double_hmap_pair_t *double_hmap_get_next(const double_hmap_t *hmap, const double_hmap_pair_t *p) {
  double_hmap_pair_t *end;

  end = hmap->data + hmap->size;
  while (p < end) {
    if (p->key != EMPTY_KEY) return p;
    p ++;
  }

  return NULL;
}


/*
 * Get the first non-empty record or NULL if the table is empty
 */
extern double_hmap_pair_t *double_hmap_first_record(const double_hmap_t *hmap) {
  return (double_hmap_pair_t *) double_hmap_get_next(hmap, hmap->data);
}


/*
 * Next record after p or NULL
 */
extern double_hmap_pair_t *double_hmap_next_record(const double_hmap_t *hmap, const double_hmap_pair_t *p) {
  assert(p != NULL && p<hmap->data + hmap->size && p->key != EMPTY_KEY);
  return (double_hmap_pair_t *) double_hmap_get_next(hmap, p + 1);
}

