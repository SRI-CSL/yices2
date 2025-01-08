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


// TODO rename double_hash_map
/*
 * MAPS 32BIT INTEGERS TO DOUBLES (adapted rfrom int_hash_map)
 * Assumes that keys are non-negative
 */

#include <assert.h>

#include "utils/memalloc.h"

#include "mcsat/l2o/eval_hash_map.h"

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
void init_eval_hmap(eval_hmap_t *hmap, uint32_t n) {
  uint32_t i;
  eval_hmap_pair_t *tmp;

  if (n == 0) {
    n = EVAL_HMAP_DEFAULT_SIZE;
  }

  if (n >= EVAL_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));

  tmp = (eval_hmap_pair_t *) safe_malloc(n * sizeof(eval_hmap_pair_t));
  for (i=0; i<n; i++) {
    tmp[i].key = EMPTY_KEY;
  }

  hmap->data = tmp;
  hmap->size = n;
  hmap->nelems = 0;
  hmap->ndeleted = 0;

  hmap->resize_threshold = (uint32_t)(n * EVAL_HMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t) (n * EVAL_HMAP_CLEANUP_RATIO);
}


/*
 * Free memory
 */
void delete_eval_hmap(eval_hmap_t *hmap) {
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
static void eval_hmap_clean_copy(eval_hmap_pair_t *data, eval_hmap_pair_t *d, uint32_t mask) {
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
static void eval_hmap_cleanup(eval_hmap_t *hmap) {
  eval_hmap_pair_t *tmp, *d;
  uint32_t j, n, mask;

  n = hmap->size;
  tmp = (eval_hmap_pair_t *) safe_malloc(n * sizeof(eval_hmap_pair_t));
  for (j=0; j<n; j++) {
    tmp[j].key = EMPTY_KEY;
  }

  mask = n - 1;
  d = hmap->data;
  for (j=0; j<n; j++) {
    if (d->key >= 0) {
      eval_hmap_clean_copy(tmp, d, mask);
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
static void eval_hmap_extend(eval_hmap_t *hmap) {
  eval_hmap_pair_t *tmp, *d;
  uint32_t j, n, n2, mask;

  n = hmap->size;
  n2 = n << 1;
  if (n2 >= EVAL_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  tmp = (eval_hmap_pair_t *) safe_malloc(n2 * sizeof(eval_hmap_pair_t));
  for (j=0; j<n2; j++) {
    tmp[j].key = EMPTY_KEY;
  }

  mask = n2 - 1;
  d = hmap->data;
  for (j=0; j<n; j++) {
    if (d->key >= 0) {
      eval_hmap_clean_copy(tmp, d, mask);
    }
    d ++;
  }

  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->size = n2;
  hmap->ndeleted = 0;

  hmap->resize_threshold = (uint32_t)(n2 * EVAL_HMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t)(n2 * EVAL_HMAP_CLEANUP_RATIO);
}


/*
 * Find record with key k
 * - return NULL if k is not in the table
 */
eval_hmap_pair_t *eval_hmap_find(const eval_hmap_t *hmap, int32_t k) {
  uint32_t mask, j;
  eval_hmap_pair_t *d;

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
static eval_hmap_pair_t *eval_hmap_get_clean(eval_hmap_t *hmap, int32_t k) {
  uint32_t mask, j;
  eval_hmap_pair_t *d;

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
eval_hmap_pair_t *eval_hmap_get(eval_hmap_t *hmap, int32_t k) {
  uint32_t mask, j;
  eval_hmap_pair_t *d, *aux;

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
    eval_hmap_extend(hmap);
    aux = eval_hmap_get_clean(hmap, k);
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
void eval_hmap_add(eval_hmap_t *hmap, int32_t k, double v) {
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
    eval_hmap_extend(hmap);
  }
}


/*
 * Add record [k -> v ] to hmap
 * - if there is a record with the same key, it is replaced by the new record
 */
void eval_hmap_add_replace(eval_hmap_t *hmap, int32_t k, double v) {
  eval_hmap_pair_t* record = eval_hmap_find(hmap, k);
  if (record != NULL){
    eval_hmap_erase(hmap, record);
  }
  eval_hmap_add(hmap, k, v);
}

/*
 * Add record [k -> v ] to hmap
 * - if there is a record with the same key, it does not replace it (but does not throw an error)
 */
void eval_hmap_add_not_replace(eval_hmap_t *hmap, int32_t k, double v) {
  eval_hmap_pair_t* record = eval_hmap_find(hmap, k);
  if (record == NULL){
    eval_hmap_add(hmap, k, v);
  }
}


/*
 * Erase record r
 */
void eval_hmap_erase(eval_hmap_t *hmap, eval_hmap_pair_t *r) {
  assert(eval_hmap_find(hmap, r->key) == r);

  r->key = DELETED_KEY;
  hmap->nelems --;
  hmap->ndeleted ++;
  if (hmap->ndeleted >= hmap->cleanup_threshold) {
    eval_hmap_cleanup(hmap);
  }
}

/*
 * Deep copy one map to another
 */
extern void eval_hmap_copy(eval_hmap_t *hmap_from, eval_hmap_t *hmap_to){
  init_eval_hmap(hmap_to, hmap_from->size);
  hmap_to->size = hmap_from->size;
  hmap_to->nelems = hmap_from->nelems;
  hmap_to->ndeleted = hmap_from->ndeleted;
  hmap_to->resize_threshold = hmap_from->resize_threshold;
  hmap_to->cleanup_threshold = hmap_from->cleanup_threshold;
  for(uint32_t i=0 ; i < hmap_from->size ; i++){
    hmap_to->data[i] = hmap_from->data[i];
  }
}


/*
 * Merge one map to another (overwriting records)
 */
extern void eval_hmap_merge(eval_hmap_t *hmap_from, eval_hmap_t *hmap_to){
  for(uint32_t i=0 ; i < hmap_from->size ; i++){
    eval_hmap_pair_t record = hmap_from->data[i];
    if(record.key == -1){
      continue;
    }
    eval_hmap_add_replace(hmap_to, record.key, record.val);
  }
}


/*
 * Empty the map
 */
void eval_hmap_reset(eval_hmap_t *hmap) {
  uint32_t i, n;
  eval_hmap_pair_t *d;

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
static const eval_hmap_pair_t *eval_hmap_get_next(const eval_hmap_t *hmap, const eval_hmap_pair_t *p) {
  eval_hmap_pair_t *end;

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
eval_hmap_pair_t *eval_hmap_first_record(const eval_hmap_t *hmap) {
  return (eval_hmap_pair_t *) eval_hmap_get_next(hmap, hmap->data);
}


/*
 * Next record after p or NULL
 */
eval_hmap_pair_t *eval_hmap_next_record(const eval_hmap_t *hmap, const eval_hmap_pair_t *p) {
  assert(p != NULL && p<hmap->data + hmap->size && p->key != EMPTY_KEY);
  return (eval_hmap_pair_t *) eval_hmap_get_next(hmap, p+1);
}



