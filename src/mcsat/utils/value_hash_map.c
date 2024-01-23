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
 * MAPS 32BIT INTEGERS TO 32BIT INTEGERS
 * Assumes that keys are non-negative
 */

#include <assert.h>

#include "value_hash_map.h"
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
 * Markers for empty/deleted pairs
 */
#define VALUE_HMAP_EMPTY_KEY ((mcsat_value_t*) 0)
#define VALUE_HMAP_DELETED_KEY ((mcsat_value_t*) 1)

static inline
bool value_hmap_valid_key(const mcsat_value_t* k) {
  return k != VALUE_HMAP_DELETED_KEY && k != VALUE_HMAP_EMPTY_KEY;
}

/*
 * Initialization:
 * - n = initial size, must be a power of 2
 * - if n = 0, the default size is used
 */
void init_value_hmap(value_hmap_t *hmap, uint32_t n) {
  uint32_t i;
  value_hmap_pair_t *tmp;

  if (n == 0) {
    n = VALUE_HMAP_DEFAULT_SIZE;
  }

  if (n >= VALUE_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));

  tmp = (value_hmap_pair_t *) safe_malloc(n * sizeof(value_hmap_pair_t));
  for (i=0; i<n; i++) {
    tmp[i].key = VALUE_HMAP_EMPTY_KEY;
  }

  hmap->data = tmp;
  hmap->size = n;
  hmap->nelems = 0;
  hmap->ndeleted = 0;

  hmap->resize_threshold = (uint32_t)(n * VALUE_HMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t) (n * VALUE_HMAP_CLEANUP_RATIO);
}


/*
 * Free memory
 */
void delete_value_hmap(value_hmap_t *hmap) {
  value_hmap_reset(hmap);
  safe_free(hmap->data);
  hmap->data = NULL;
}


/** Hash of a key */
static inline
uint32_t hash_key(const mcsat_value_t* k) {
  return mcsat_value_hash(k);
}

/** Equality */
static inline
bool eq_key(const mcsat_value_t* k1, const mcsat_value_t* k2) {
  if (k1->type != k2->type) { return false; }
  if (k1->type == VALUE_BV
      && k2->type == VALUE_BV
      && (k1->bv_value.bitsize != k2->bv_value.bitsize)) { return false; }
  return mcsat_value_eq(k1, k2);
}

/*
 * Make a copy of record d in a clean array data
 * - mask = size of data - 1 (size must be a power of 2)
 */
static void value_hmap_clean_copy(value_hmap_pair_t *data, value_hmap_pair_t *d, uint32_t mask) {
  uint32_t j;

  j = hash_key(d->key) & mask;
  while (data[j].key != VALUE_HMAP_EMPTY_KEY) {
    j ++;
    j &= mask;
  }

  data[j].key = d->key;
  data[j].val = d->val;
}


/*
 * Remove deleted records
 */
static void value_hmap_cleanup(value_hmap_t *hmap) {
  value_hmap_pair_t *tmp, *d;
  uint32_t j, n, mask;

  n = hmap->size;
  tmp = (value_hmap_pair_t *) safe_malloc(n * sizeof(value_hmap_pair_t));
  for (j=0; j<n; j++) {
    tmp[j].key = VALUE_HMAP_EMPTY_KEY;
  }

  mask = n - 1;
  d = hmap->data;
  for (j=0; j<n; j++) {
    if (value_hmap_valid_key(d->key)) {
      value_hmap_clean_copy(tmp, d, mask);
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
static void value_hmap_extend(value_hmap_t *hmap) {
  value_hmap_pair_t *tmp, *d;
  uint32_t j, n, n2, mask;

  n = hmap->size;
  n2 = n << 1;
  if (n2 >= VALUE_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  tmp = (value_hmap_pair_t *) safe_malloc(n2 * sizeof(value_hmap_pair_t));
  for (j=0; j<n2; j++) {
    tmp[j].key = VALUE_HMAP_EMPTY_KEY;
  }

  mask = n2 - 1;
  d = hmap->data;
  for (j=0; j<n; j++) {
    if (value_hmap_valid_key(d->key)) {
      value_hmap_clean_copy(tmp, d, mask);
    }
    d ++;
  }

  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->size = n2;
  hmap->ndeleted = 0;

  hmap->resize_threshold = (uint32_t)(n2 * VALUE_HMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t)(n2 * VALUE_HMAP_CLEANUP_RATIO);
}


/*
 * Find record with key k
 * - return NULL if k is not in the table
 */
value_hmap_pair_t *value_hmap_find(const value_hmap_t *hmap, const mcsat_value_t* k) {
  uint32_t mask, j;
  value_hmap_pair_t *d;

  assert(k != NULL);

  mask = hmap->size - 1;
  j = hash_key(k) & mask;
  for (;;) {
    d = hmap->data + j;
    if (value_hmap_valid_key(d->key)) {
      if (eq_key(d->key, k)) {
        return d;
      }
    }
    if (d->key == VALUE_HMAP_EMPTY_KEY) return NULL;
    j ++;
    j &= mask;
  }

  // Not reachable
  return NULL;
}


/*
 * Add record with key k after hmap was extended:
 * - initialize val to -1
 * - we know that no record with key k is present
 */
static
value_hmap_pair_t *value_hmap_get_clean(value_hmap_t *hmap, const mcsat_value_t* k) {
  uint32_t mask, j;
  value_hmap_pair_t *d;

  mask = hmap->size - 1;
  j = hash_key(k) & mask;
  for (;;) {
    d = hmap->data + j;
    if (!value_hmap_valid_key(d->key)) {
      hmap->nelems ++;
      d->key = mcsat_value_new_copy(k);
      d->val = -1;
      return d;
    }
    j ++;
    j &= mask;
  }

  // Not reachable
  return NULL;
}


/*
 * Find or add record with key k
 */
value_hmap_pair_t *value_hmap_get(value_hmap_t *hmap, const mcsat_value_t* k) {
  uint32_t mask, j;
  value_hmap_pair_t *d, *aux;

  assert(k >= 0);
  assert(hmap->size > hmap->ndeleted + hmap->nelems);

  mask = hmap->size - 1;
  j = hash_key(k) & mask;

  for (;;) {
    d = hmap->data + j;
    if (value_hmap_valid_key(d->key)) {
      if (eq_key(d->key, k)) return d;
    } else {
      break;
    }
    j ++;
    j &= mask;
  }

  aux = d; // new record, if needed, will be aux
  while (d->key != VALUE_HMAP_EMPTY_KEY) {
    j ++;
    j &= mask;
    d = hmap->data + j;
    if (value_hmap_valid_key(d->key)) {
      if (eq_key(d->key, k)) return d;
    }
  }

  if (aux->key == VALUE_HMAP_DELETED_KEY) {
    assert(hmap->ndeleted > 0);
    hmap->ndeleted --;
  }

  if (hmap->nelems + hmap->ndeleted >= hmap->resize_threshold) {
    value_hmap_extend(hmap);
    aux = value_hmap_get_clean(hmap, k);
  } else {
    hmap->nelems ++;
    aux->key = mcsat_value_new_copy(k);
    aux->val = -1;
  }

  return aux;
}


/*
 * Add record [k -> v ] to hmap
 * - there must not be a record with the same key
 */
void value_hmap_add(value_hmap_t *hmap, const mcsat_value_t* k, int32_t v) {
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
  if (hmap->data[i].key == VALUE_HMAP_DELETED_KEY) {
    assert(hmap->ndeleted > 0);
    hmap->ndeleted --;
  }
  hmap->data[i].key = mcsat_value_new_copy(k);
  hmap->data[i].val = v;
  hmap->nelems ++;

  if (hmap->nelems + hmap->ndeleted >= hmap->resize_threshold) {
    value_hmap_extend(hmap);
  }
}


/*
 * Erase record r
 */
void value_hmap_erase(value_hmap_t *hmap, value_hmap_pair_t *r) {
  assert(value_hmap_find(hmap, r->key) == r);
  assert(value_hmap_valid_key(r->key));

  mcsat_value_delete(r->key);
  r->key = VALUE_HMAP_DELETED_KEY;
  hmap->nelems --;
  hmap->ndeleted ++;
  if (hmap->ndeleted >= hmap->cleanup_threshold) {
    value_hmap_cleanup(hmap);
  }
}


/*
 * Empty the map
 */
void value_hmap_reset(value_hmap_t *hmap) {
  uint32_t i, n;
  value_hmap_pair_t *d;

  n = hmap->size;
  d = hmap->data;
  for (i=0; i<n; i++) {
    if (value_hmap_valid_key(d->key)) {
      mcsat_value_delete(d->key);
    }
    d->key = VALUE_HMAP_EMPTY_KEY;
    d ++;
  }

  hmap->nelems = 0;
  hmap->ndeleted = 0;
}



/*
 * First non-empty record in the table, starting from p
 */
static value_hmap_pair_t *value_hmap_get_next(const value_hmap_t *hmap, value_hmap_pair_t *p) {
  value_hmap_pair_t *end;

  end = hmap->data + hmap->size;
  while (p < end) {
    if (p->key != VALUE_HMAP_EMPTY_KEY) return p;
    p ++;
  }

  return NULL;
}


/*
 * Get the first non-empty record or NULL if the table is empty
 */
value_hmap_pair_t *value_hmap_first_record(const value_hmap_t *hmap) {
  return value_hmap_get_next(hmap, hmap->data);
}


/*
 * Next record after p or NULL
 */
value_hmap_pair_t *value_hmap_next_record(const value_hmap_t *hmap, value_hmap_pair_t *p) {
  assert(p != NULL && p<hmap->data + hmap->size && p->key != VALUE_HMAP_EMPTY_KEY);
  return value_hmap_get_next(hmap, p+1);
}


/*
 * Remove the records that satisfy filter f
 * - calls f(aux, p) on every record p stored in hmap
 * - if f(aux, p) returns true then record p is removed
 */
void value_hmap_remove_records(value_hmap_t *hmap, void *aux, value_hmap_filter_t f) {
  value_hmap_pair_t *d;
  uint32_t i, n, k;

  n = hmap->size;
  d = hmap->data;
  k = 0;
  for (i=0; i<n; i++) {
    if (value_hmap_valid_key(d->key) && f(aux, d)) {
      // mark d as deleted
      mcsat_value_delete(d->key);
      d->key = VALUE_HMAP_DELETED_KEY;
      k ++;
    }
    d ++;
  }

  // k = number of deleted records
  assert(k <= hmap->nelems);
  hmap->nelems -= k;
  hmap->ndeleted += k;
  if (hmap->ndeleted >= hmap->cleanup_threshold) {
    value_hmap_cleanup(hmap);
  }
}


/*
 * Updates the value of the records
 * - calls f(aux, p) on every record p stored in hmap
 * - p->val is set according to the return value of f(aux, p)
 */
void value_hmap_update_records(value_hmap_t *hmap, void *aux, value_hmap_map_t f) {
  value_hmap_pair_t *d;
  uint32_t i, n;

  n = hmap->size;
  d = hmap->data;
  for (i=0; i<n; i++) {
    if (d->key != VALUE_HMAP_DELETED_KEY && d->key != VALUE_HMAP_EMPTY_KEY) {
      d->val = (int32_t) f(aux, d);
    }
    d ++;
  }
}


/*
 * Iterator: call f(aux, p) on every record p
 */
void value_hmap_iterate(value_hmap_t *hmap, void *aux, value_hmap_iterator_t f) {
  value_hmap_pair_t *d;
  uint32_t i, n;

  n = hmap->size;
  d = hmap->data;
  for (i=0; i<n; i++) {
    if (d->key != VALUE_HMAP_DELETED_KEY && d->key != VALUE_HMAP_EMPTY_KEY) {
      f(aux, d);
    }
    d ++;
  }
}
