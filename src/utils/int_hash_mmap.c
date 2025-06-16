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
#include <stdint.h>

#include "utils/int_hash_mmap.h"
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
enum {
  DELETED_KEY = -2,
  EMPTY_KEY = -1,
};

/*
* Initialization:
* - n = initial size, must be a power of 2
* - if n = 0, the default size is used
*/
void init_int_hmmap(int_hmmap_t *hmmap, uint32_t n) {
  uint32_t i;
  int_hmmap_pair_t *tmp;

  if (n == 0) {
    n = INT_HMMAP_DEFAULT_SIZE;
  }

  if (n >= INT_HMMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));

  tmp = (int_hmmap_pair_t *) safe_malloc(n * sizeof(int_hmmap_pair_t));
  for (i=0; i<n; i++) {
    tmp[i].key = EMPTY_KEY;
  }

  hmmap->data = tmp;
  hmmap->size = n;
  hmmap->nelems = 0;
  hmmap->ndeleted = 0;

  hmmap->resize_threshold = (uint32_t)(n * INT_HMMAP_RESIZE_RATIO);
  hmmap->cleanup_threshold = (uint32_t) (n * INT_HMMAP_CLEANUP_RATIO);
}


/*
* Free memory
*/
void delete_int_hmmap(int_hmmap_t *hmmap) {
  safe_free(hmmap->data);
  hmmap->data = NULL;
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

static uint32_t hash_key_2(int32_t k) {
  uint32_t x;

  x = (uint32_t) k;
  x ^= x >> 16;
  x *= 0xdaaa6a5d;
  x ^= x >> 16;
  x *= 0xefe65e63;
  x ^= x >> 16;

  // ensure h2 returns an odd value
  x |= 1;

  return x;
}

static inline
bool valid_pair(int_hmmap_pair_t *d) {
  return d->key >= 0;
}

static inline
bool empty_pair(int_hmmap_pair_t *d) {
  return d->key == EMPTY_KEY;
}

/*
* Make a copy of record d in a clean array data
* - mask = size of data - 1 (size must be a power of 2)
*/
static
void int_hmmap_clean_copy(int_hmmap_pair_t *data, int_hmmap_pair_t *d, uint32_t mask) {
  uint32_t j = hash_key(d->key) & mask;
  uint32_t h2 = (valid_pair(data + j)) ? hash_key_2(d->key) : 0;

  while (valid_pair(data + j)) {
    assert(h2 > 0);
    j += h2;
    j &= mask;
  }

  data[j].key = d->key;
  data[j].val = d->val;
}

static
void int_hmmap_realloc(int_hmmap_t *hmmap, uint32_t n) {
  int_hmmap_pair_t *tmp, *d;
  uint32_t j, mask;
  uint32_t n1 = hmmap->size, n2 = n;

  assert(n1 <= n2);

  tmp = (int_hmmap_pair_t *) safe_malloc(n2 * sizeof(int_hmmap_pair_t));
  for (j=0; j<n2; j++) {
    tmp[j].key = EMPTY_KEY;
  }

  mask = n2 - 1;
  d = hmmap->data;
  for (j=0; j<n1; j++) {
    if (valid_pair(d)) {
      int_hmmap_clean_copy(tmp, d, mask);
    }
    d ++;
  }

  safe_free(hmmap->data);
  hmmap->data = tmp;
  hmmap->size = n2;
  hmmap->ndeleted = 0;
  hmmap->resize_threshold = (uint32_t)(n2 * INT_HMMAP_RESIZE_RATIO);
  hmmap->cleanup_threshold = (uint32_t)(n2 * INT_HMMAP_CLEANUP_RATIO);
}

/*
 * Remove deleted records and make the table twice as large
 */
static inline
void int_hmmap_extend(int_hmmap_t *hmmap) {
  uint32_t n = hmmap->size << 1;
  if (n >= INT_HMMAP_MAX_SIZE) {
    out_of_memory();
  }
  int_hmmap_realloc(hmmap, n);
}

/*
 * Remove deleted records
 */
static inline
void int_hmmap_cleanup(int_hmmap_t *hmmap) {
  int_hmmap_realloc(hmmap, hmmap->size);
}

/*
 * Checks if map contains k -> v
 */
bool int_hmmap_contains(const int_hmmap_t *hmmap, int32_t k, int32_t v) {
  uint32_t mask, j;
  int_hmmap_pair_t *d;

  assert(k >= 0);

  mask = hmmap->size - 1;
  j = hash_key(k) & mask;
  uint32_t h2 = 0;

  for (;;) {
    d = hmmap->data + j;
    if (d->key == k && d->val == v) return true;
    if (d->key == EMPTY_KEY) return false;
    if (h2 == 0) h2 = hash_key_2(k);
    assert(h2 > 0);
    j += h2;
    j &= mask;
  }
}

/*
 * Find the n-th record with key k
 * - return NULL if not found
 */
int_hmmap_pair_t *int_hmmap_find(const int_hmmap_t *hmmap, int32_t k, uint32_t n) {
  uint32_t mask, j, h2;
  int_hmmap_pair_t *d;

  assert(k >= 0);

  h2 = 0;
  mask = hmmap->size - 1;
  j = hash_key(k) & mask;
  for (;;) {
    d = hmmap->data + j;
    if (d->key == k) {
      if (n == 0) return d;
      else n --;
    }
    if (d->key == EMPTY_KEY) return NULL;
    if (h2 == 0) h2 = hash_key_2(k);
    assert(h2 > 0);
    j += h2;
    j &= mask;
  }
}


void int_hmmap_add(int_hmmap_t *hmmap, int32_t k, int32_t v) {
  uint32_t i, mask;

  assert(k >= 0);
  assert(hmmap->nelems + hmmap->ndeleted < hmmap->size);

  mask = hmmap->size - 1;
  i = hash_key(k) & mask;
  uint32_t h2 = valid_pair(hmmap->data + i) ? hash_key_2(k) : 0;
  while (valid_pair(hmmap->data + i)) {
    assert(h2 > 0);
    i += h2;
    i &= mask;
  }

  // store the new record in data[i]
  if (hmmap->data[i].key == DELETED_KEY) {
    assert(hmmap->ndeleted > 0);
    hmmap->ndeleted --;
  }
  hmmap->data[i].key = k;
  hmmap->data[i].val = v;
  hmmap->nelems ++;

  if (hmmap->nelems + hmmap->ndeleted >= hmmap->resize_threshold) {
    int_hmmap_extend(hmmap);
  }
}


bool int_hmmap_insert(int_hmmap_t *hmmap, int32_t k, int32_t v) {
  uint32_t i, pos, mask;

  assert(k >= 0);
  assert(hmmap->nelems + hmmap->ndeleted < hmmap->size);

  mask = hmmap->size - 1;
  i = hash_key(k) & mask;
  uint32_t h2 = 0;
  while (valid_pair(hmmap->data + i)) {
    int_hmmap_pair_t *p = hmmap->data + i;
    if (p->key == k && p->val == v) return false;
    if (h2 == 0) h2 = hash_key_2(k);
    assert(h2 > 0);
    i += h2;
    i &= mask;
  }

  // found position to insert, continue checking for existence
  pos = i;

  while (!empty_pair(hmmap->data + i)) {
    int_hmmap_pair_t *p = hmmap->data + i;
    if (p->key == k && p->val == v) return false;
    if (h2 == 0) h2 = hash_key_2(k);
    assert(h2 > 0);
    i += h2;
    i &= mask;
  }

  // store the new record in data[pos]
  if (hmmap->data[pos].key == DELETED_KEY) {
    assert(hmmap->ndeleted > 0);
    hmmap->ndeleted --;
  }
  hmmap->data[pos].key = k;
  hmmap->data[pos].val = v;
  hmmap->nelems ++;

  if (hmmap->nelems + hmmap->ndeleted >= hmmap->resize_threshold) {
    int_hmmap_extend(hmmap);
  }

  return true;
}


/*
* Erase record r
*/
void int_hmmap_erase(int_hmmap_t *hmmap, int_hmmap_pair_t *r) {
  r->key = DELETED_KEY;
  hmmap->nelems --;
  hmmap->ndeleted ++;
  if (hmmap->ndeleted >= hmmap->cleanup_threshold) {
    int_hmmap_cleanup(hmmap);
  }
}


/*
* Empty the map
*/
void int_hmmap_reset(int_hmmap_t *hmmap) {
  uint32_t i, n;
  int_hmmap_pair_t *d;

  n = hmmap->size;
  d = hmmap->data;
  for (i=0; i<n; i++) {
    d->key = EMPTY_KEY;
    d ++;
  }

  hmmap->nelems = 0;
  hmmap->ndeleted = 0;
}


/*
 * Finds all values of k and adds them to v.
 */
uint32_t int_hmmap_find_all(int_hmmap_t *hmmap, int32_t k, ivector_t *v) {
  uint32_t mask, j, h2;
  int_hmmap_pair_t *d;
  uint32_t cnt = 0;

  assert(k >= 0);

  h2 = 0;
  mask = hmmap->size - 1;
  j = hash_key(k) & mask;
  for (;;) {
    d = hmmap->data + j;
    if (d->key == k) { cnt++; ivector_push(v, d->val); }
    if (d->key == EMPTY_KEY) return cnt;
    if (h2 == 0) h2 = hash_key_2(k);
    assert(h2 > 0);
    j += h2;
    j &= mask;
  }
}

/*
 * Inserts all elements of v with key k.
 */
void int_hmmap_add_all(int_hmmap_t * hmmap, int32_t k, const ivector_t *v) {
  uint32_t i, mask;
  uint32_t n = v->size;

  assert(k >= 0);

  while (hmmap->nelems + hmmap->ndeleted + n >= hmmap->resize_threshold) {
    int_hmmap_extend(hmmap);
  }

  assert(hmmap->nelems + hmmap->ndeleted + n < hmmap->size);

  mask = hmmap->size - 1;
  i = hash_key(k) & mask;
  uint32_t h2 = valid_pair(hmmap->data + i) || n > 1 ? hash_key_2(k) : 0;
  for (uint32_t m = 0; m < n; ++ m) {
    while (valid_pair(hmmap->data + i)) {
      assert(h2 > 0);
      i += h2;
      i &= mask;
    }
    // store the new record in data[i]
    if (hmmap->data[i].key == DELETED_KEY) {
      assert(hmmap->ndeleted > 0);
      hmmap->ndeleted--;
    }
    hmmap->data[i].key = k;
    hmmap->data[i].val = v->data[m];
    hmmap->nelems++;
    assert(valid_pair(hmmap->data + i));
  }
}

bool int_hmmap_contains_key(const int_hmmap_t *hmmap, int32_t k) {
  return int_hmmap_find(hmmap, k, 0) != NULL;
}

#if 0

/*
* First non-empty record in the table, starting from p
*/
static const int_hmmap_pair_t *int_hmmap_get_next(const int_hmmap_t *hmmap, const int_hmmap_pair_t *p) {
  int_hmmap_pair_t *end;

  end = hmmap->data + hmmap->size;
  while (p < end) {
    if (p->key != EMPTY_KEY) return p;
    p ++;
  }

  return NULL;
}


/*
* Get the first non-empty record or NULL if the table is empty
*/
int_hmmap_pair_t *int_hmmap_first_record(const int_hmmap_t *hmmap) {
  return (int_hmmap_pair_t *) int_hmmap_get_next(hmmap, hmmap->data);
}


/*
* Next record after p or NULL
*/
int_hmmap_pair_t *int_hmmap_next_record(const int_hmmap_t *hmmap, const int_hmmap_pair_t *p) {
  assert(p != NULL && p<hmmap->data + hmmap->size && p->key != EMPTY_KEY);
  return (int_hmmap_pair_t *) int_hmmap_get_next(hmmap, p+1);
}




/*
* Remove the records that satisfy filter f
* - calls f(aux, p) on every record p stored in hmmap
* - if f(aux, p) returns true then record p is removed
*/
void int_hmmap_remove_records(int_hmmap_t *hmmap, void *aux, int_hmmap_filter_t f) {
  int_hmmap_pair_t *d;
  uint32_t i, n, k;

  n = hmmap->size;
  d = hmmap->data;
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
  assert(k <= hmmap->nelems);
  hmmap->nelems -= k;
  hmmap->ndeleted += k;
  if (hmmap->ndeleted >= hmmap->cleanup_threshold) {
    int_hmmap_cleanup(hmmap);
  }
}



/*
* Iterator: call f(aux, p) on every record p
*/
void int_hmmap_iterate(int_hmmap_t *hmmap, void *aux, int_hmmap_iterator_t f) {
  int_hmmap_pair_t *d;
  uint32_t i, n;

  n = hmmap->size;
  d = hmmap->data;
  for (i=0; i<n; i++) {
    if (d->key >= 0) {
      f(aux, d);
    }
    d ++;
  }
}

#endif
