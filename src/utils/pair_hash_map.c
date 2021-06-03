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
 * MAPS INTEGERS TO INTEGERS
 */

/*
 * Keys are 32bit non-negative integers. Values are signed 32bit integers.
 */

#include <assert.h>
#include <stdbool.h>

#include "utils/memalloc.h"
#include "utils/pair_hash_map.h"


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
void init_pmap(pmap_t *hmap, uint32_t n) {
  uint32_t i;
  pmap_rec_t *tmp;

  if (n == 0) {
    n = PMAP_DEFAULT_SIZE;
  }

  if (n >= PMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));
  tmp = (pmap_rec_t *) safe_malloc(n * sizeof(pmap_rec_t));
  for (i=0; i<n; i++) {
    tmp[i].val = NULL;
  }

  hmap->data = tmp;
  hmap->size = n;
  hmap->nelems = 0;
  hmap->ndeleted = 0;

  hmap->resize_threshold = (uint32_t)(n * PMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t) (n * PMAP_CLEANUP_RATIO);
}


/*
 * Free memory
 */
void delete_pmap(pmap_t *hmap) {
  safe_free(hmap->data);
  hmap->data = NULL;
}


/*
 * Hash of a pair k0, k1 based on Jenkins lookup3 code.
 * (public domain code, see http://www.burtleburtle.net)
 */
#define rot(x,k) (((x)<<(k)) | ((x)>>(32-(k))))

#define final(x,y,z)      \
{                         \
  z ^= y; z -= rot(y,14); \
  x ^= z; x -= rot(z,11); \
  y ^= x; y -= rot(x,25); \
  z ^= y; z -= rot(y,16); \
  x ^= z; x -= rot(z,4);  \
  y ^= x; y -= rot(x,14); \
  z ^= y; z -= rot(y,24); \
}

static uint32_t hash_pair(int32_t k0, int32_t k1) {
  uint32_t x, y, z;

  x = (uint32_t) k0;
  y = (uint32_t) k1;
  z = 0xdeadbeef;
  final(x, y, z);

  return z;
}


/*
 * Check whether d is a valid record: non-null, not deleted
 */
static inline bool valid_record(const pmap_rec_t *r) {
  return r->val != NULL && r->val != DELETED_PTR;
}


/*
 * Make a copy of record d in a clean array data
 * - mask = size of data - 1 (size must be a power of 2)
 */
static void pmap_clean_copy(pmap_rec_t *data, pmap_rec_t *d, uint32_t mask) {
  uint32_t j;

  j = hash_pair(d->k0, d->k1) & mask;
  while (data[j].val != NULL) {
    j ++;
    j &= mask;
  }

  data[j].k0 = d->k0;
  data[j].k1 = d->k1;
  data[j].val = d->val;
}


/*
 * Remove deleted records
 */
static void pmap_cleanup(pmap_t *hmap) {
  pmap_rec_t *tmp, *d;
  uint32_t j, n, mask;

  n = hmap->size;
  tmp = (pmap_rec_t *) safe_malloc(n * sizeof(pmap_rec_t));
  for (j=0; j<n; j++) {
    tmp[j].val = NULL;
  }

  mask = n - 1;
  d = hmap->data;
  for (j=0; j<n; j++) {
    if (valid_record(d)) {
      pmap_clean_copy(tmp, d, mask);
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
static void pmap_extend(pmap_t *hmap) {
  pmap_rec_t *tmp, *d;
  uint32_t j, n, n2, mask;

  n = hmap->size;
  n2 = n << 1;
  if (n2 >= PMAP_MAX_SIZE) {
    out_of_memory();
  }

  tmp = (pmap_rec_t *) safe_malloc(n2 * sizeof(pmap_rec_t));
  for (j=0; j<n2; j++) {
    tmp[j].val = NULL;
  }

  mask = n2 - 1;
  d = hmap->data;
  for (j=0; j<n; j++) {
    if (valid_record(d)) {
      pmap_clean_copy(tmp, d, mask);
    }
    d ++;
  }

  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->size = n2;
  hmap->ndeleted = 0;

  hmap->resize_threshold = (uint32_t)(n2 * PMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t)(n2 * PMAP_CLEANUP_RATIO);
}


/*
 * Find record with key (k0, k1)
 * - return NULL if that key is not in the table
 */
pmap_rec_t *pmap_find(const pmap_t *hmap, int32_t k0, int32_t k1) {
  uint32_t mask, j;
  pmap_rec_t *d;

  mask = hmap->size - 1;
  j = hash_pair(k0, k1) & mask;
  for (;;) {
    d = hmap->data + j;
    if (d->val == NULL) return NULL;
    if (d->val != DELETED_PTR && d->k0 == k0 && d->k1 == k1) {
      return d;
    }
    j ++;
    j &= mask;
  }
}


/*
 * Add a fresh record with key (k0, k1) after hmap was extended
 * - there are no record with this key in hmap
 * - there are no deleted record
 */
static pmap_rec_t *pmap_get_clean(pmap_t *hmap, int32_t k0, int32_t k1) {
  uint32_t j, mask;
  pmap_rec_t *d;

  mask = hmap->size - 1;
  j = hash_pair(k0, k1) & mask;
  for (;;) {
    d = hmap->data + j;
    if (d->val == NULL) {
      hmap->nelems ++;
      d->k0 = k0;
      d->k1 = k1;
      d->val = DEFAULT_PTR;
      return d;
    }
    j ++;
    j &= mask;
  }
}


/*
 * Find or add record with key (k0, k1)
 */
pmap_rec_t *pmap_get(pmap_t *hmap, int32_t k0, int32_t k1) {
  uint32_t mask, j;
  pmap_rec_t *d, *aux;

  assert(hmap->size > hmap->ndeleted + hmap->nelems);

  mask = hmap->size - 1;
  j = hash_pair(k0, k1) & mask;

  for (;;) {
    d = hmap->data + j;
    if (d->val == NULL || d->val == DELETED_PTR) break;
    if (d->k0 == k0 && d->k1 == k1) return d;
    j ++;
    j &= mask;
  }

  aux = d; // new record, if needed, will be aux
  while (d->val != NULL) {
    j ++;
    j &= mask;
    if (d->val != DELETED_PTR && d->k0 == k0 && d->k1 == k1) return d;
  }

  if (aux->val == DELETED_PTR){
    assert(hmap->ndeleted > 0);
    hmap->ndeleted --;
  }

  if (hmap->nelems + hmap->ndeleted >= hmap->resize_threshold) {
    pmap_extend(hmap);
    aux = pmap_get_clean(hmap, k0, k1);
  } else {
    aux->k0 = k0;
    aux->k1 = k1;
    aux->val = DEFAULT_PTR;
    hmap->nelems ++;
  }

  return aux;
}


/*
 * Erase record r
 */
void pmap_erase(pmap_t *hmap, pmap_rec_t *r) {
  assert(pmap_find(hmap, r->k0, r->k1) == r);

  r->val = DELETED_PTR;
  hmap->nelems --;
  hmap->ndeleted ++;
  if (hmap->ndeleted > hmap->cleanup_threshold) {
    pmap_cleanup(hmap);
  }
}


/*
 * Empty the map
 */
void pmap_reset(pmap_t *hmap) {
  uint32_t i, n;
  pmap_rec_t *d;

  n = hmap->size;
  d = hmap->data;
  for (i=0; i<n; i++) {
    d->val = NULL;
    d ++;
  }

  hmap->nelems = 0;
  hmap->ndeleted = 0;
}

/*
 * First non-empty record in the table, starting from p
 */
static pmap_rec_t *pmap_get_next(pmap_t *hmap, pmap_rec_t *p) {
  pmap_rec_t *end;

  end = hmap->data + hmap->size;
  while (p < end) {
    if (valid_record(p)) return p;
    p ++;
  }

  return NULL;
}


/*
 * Get the first non-empty record or NULL if the table is empty
 */
pmap_rec_t *pmap_first_record(pmap_t *hmap) {
  return pmap_get_next(hmap, hmap->data);
}


/*
 * Next record after p or NULL
 */
pmap_rec_t *pmap_next_record(pmap_t *hmap, pmap_rec_t *p) {
  assert(p != NULL && p<hmap->data + hmap->size && valid_record(p));
  return pmap_get_next(hmap, p+1);
}


