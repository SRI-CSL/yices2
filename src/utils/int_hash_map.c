/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * MAPS 32BIT INTEGERS TO 32BIT INTEGERS
 * Assumes that keys are non-negative
 */

#include <stdbool.h>
#include <assert.h>

#include "utils/memalloc.h"
#include "utils/int_hash_map.h"


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
void init_int_hmap(int_hmap_t *hmap, uint32_t n) {
  uint32_t i;
  int_hmap_pair_t *tmp;

  if (n == 0) {
    n = INT_HMAP_DEFAULT_SIZE;
  }

  if (n >= INT_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));

  tmp = (int_hmap_pair_t *) safe_malloc(n * sizeof(int_hmap_pair_t));
  for (i=0; i<n; i++) {
    tmp[i].key = EMPTY_KEY;
  }

  hmap->data = tmp;
  hmap->size = n;
  hmap->nelems = 0;
  hmap->ndeleted = 0;

  hmap->resize_threshold = (uint32_t)(n * INT_HMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t) (n * INT_HMAP_CLEANUP_RATIO);
}


/*
 * Free memory
 */
void delete_int_hmap(int_hmap_t *hmap) {
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
static void int_hmap_clean_copy(int_hmap_pair_t *data, int_hmap_pair_t *d, uint32_t mask) {
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
static void int_hmap_cleanup(int_hmap_t *hmap) {
  int_hmap_pair_t *tmp, *d;
  uint32_t j, n, mask;

  n = hmap->size;
  tmp = (int_hmap_pair_t *) safe_malloc(n * sizeof(int_hmap_pair_t));
  for (j=0; j<n; j++) {
    tmp[j].key = EMPTY_KEY;
  }

  mask = n - 1;
  d = hmap->data;
  for (j=0; j<n; j++) {
    if (d->key >= 0) {
      int_hmap_clean_copy(tmp, d, mask);
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
static void int_hmap_extend(int_hmap_t *hmap) {
  int_hmap_pair_t *tmp, *d;
  uint32_t j, n, n2, mask;

  n = hmap->size;
  n2 = n << 1;
  if (n2 >= INT_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  tmp = (int_hmap_pair_t *) safe_malloc(n2 * sizeof(int_hmap_pair_t));
  for (j=0; j<n2; j++) {
    tmp[j].key = EMPTY_KEY;
  }

  mask = n2 - 1;
  d = hmap->data;
  for (j=0; j<n; j++) {
    if (d->key >= 0) {
      int_hmap_clean_copy(tmp, d, mask);
    }
    d ++;
  }

  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->size = n2;
  hmap->ndeleted = 0;

  hmap->resize_threshold = (uint32_t)(n2 * INT_HMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t)(n2 * INT_HMAP_CLEANUP_RATIO);
}


/*
 * Find record with key k
 * - return NULL if k is not in the table
 */
int_hmap_pair_t *int_hmap_find(int_hmap_t *hmap, int32_t k) {
  uint32_t mask, j;
  int_hmap_pair_t *d;

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
static int_hmap_pair_t *int_hmap_get_clean(int_hmap_t *hmap, int32_t k) {
  uint32_t mask, j;
  int_hmap_pair_t *d;

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
int_hmap_pair_t *int_hmap_get(int_hmap_t *hmap, int32_t k) {
  uint32_t mask, j;
  int_hmap_pair_t *d, *aux;

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

  if (hmap->nelems + hmap->ndeleted >= hmap->resize_threshold) {
    int_hmap_extend(hmap);
    aux = int_hmap_get_clean(hmap, k);
  } else {
    hmap->nelems ++;
    aux->key = k;
    aux->val = -1;
  }

  return aux;
}


/*
 * Add record [k -> v ] to hmao
 * - there must not be a record with the same key
 */
void int_hmap_add(int_hmap_t *hmap, int32_t k, int32_t v) {
  uint32_t i, mask;

  assert(k >= 0 && hmap->nelems < hmap->size);

  mask = hmap->size - 1;
  i = hash_key(k) & mask;
  while (hmap->data[i].key >= 0) {
    assert(hmap->data[i].key != k);
    i ++;
    i &= mask;
  }

  // store the new record in data[i]
  hmap->data[i].key = k;
  hmap->data[i].val = v;
  hmap->nelems ++;

  if (hmap->nelems + hmap->ndeleted >= hmap->resize_threshold) {
    int_hmap_extend(hmap);
  }
}


/*
 * Erase record r
 */
void int_hmap_erase(int_hmap_t *hmap, int_hmap_pair_t *r) {
  assert(int_hmap_find(hmap, r->key) == r);

  r->key = DELETED_KEY;
  hmap->nelems --;
  hmap->ndeleted ++;
  if (hmap->ndeleted >= hmap->cleanup_threshold) {
    int_hmap_cleanup(hmap);
  }
}


/*
 * Empty the map
 */
void int_hmap_reset(int_hmap_t *hmap) {
  uint32_t i, n;
  int_hmap_pair_t *d;

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
static int_hmap_pair_t *int_hmap_get_next(int_hmap_t *hmap, int_hmap_pair_t *p) {
  int_hmap_pair_t *end;

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
int_hmap_pair_t *int_hmap_first_record(int_hmap_t *hmap) {
  return int_hmap_get_next(hmap, hmap->data);
}


/*
 * Next record after p or NULL
 */
int_hmap_pair_t *int_hmap_next_record(int_hmap_t *hmap, int_hmap_pair_t *p) {
  assert(p != NULL && p<hmap->data + hmap->size && p->key != EMPTY_KEY);
  return int_hmap_get_next(hmap, p+1);
}




/*
 * Remove the records that satisfy filter f
 * - calls f(aux, p) on every record p stored in hmap
 * - if f(aux, p) returns true then record p is removed
 */
void int_hmap_remove_records(int_hmap_t *hmap, void *aux, int_hmap_filter_t f) {
  int_hmap_pair_t *d;
  uint32_t i, n, k;

  n = hmap->size;
  d = hmap->data;
  k = 0;
  for (i=0; i<n; i++) {
    if (d->key >= 0 && f(aux, d)) {
      // mark d as deleted
      d->key = DELETED_KEY;
      k ++;
    }
    d ++;
  }

  // k = number of deleted records
  assert(k <= hmap->nelems);
  hmap->nelems -= k;
  hmap->ndeleted += k;
  if (hmap->ndeleted >= hmap->cleanup_threshold) {
    int_hmap_cleanup(hmap);
  }
}



/*
 * Iterator: call f(aux, p) on every record p
 */
void int_hmap_iterate(int_hmap_t *hmap, void *aux, int_hmap_iterator_t f) {
  int_hmap_pair_t *d;
  uint32_t i, n;

  n = hmap->size;
  d = hmap->data;
  for (i=0; i<n; i++) {
    if (d->key >= 0) {
      f(aux, d);
    }
    d ++;
  }
}
