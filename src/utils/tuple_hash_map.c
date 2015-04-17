/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * MAPS TUPLES (ARRAYS) OF 32BIT INTEGERS TO 32BIT INTEGERS
 */

#include <assert.h>

#include "utils/hash_functions.h"
#include "utils/memalloc.h"
#include "utils/tuple_hash_map.h"


/*
 * RECORDS
 */

/*
 * Hash code for key[0 ... n-1]
 */
static inline uint32_t hash_tuple_key(uint32_t n, int32_t key[]) {
  return jenkins_hash_intarray(key, n);
}


/*
 * Check whether two keys of same size are equal.
 * - n = size of the two arrays
 */
static bool equal_tuples(uint32_t n, int32_t a[], int32_t b[]) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (a[i] != b[i]) {
      return false;
    }
  }

  return true;
}


/*
 * Create record for the given key and hash value
 * - key must be an array of n integers
 * - hash must be the hash code for key
 * - the value field is not initialized
 */
static tuple_hmap_rec_t *new_tuple_hmap_record(uint32_t hash, uint32_t n, int32_t key[]) {
  tuple_hmap_rec_t *tmp;
  uint32_t i;

  assert(n < TUPLE_HMAP_MAX_ARITY && hash == hash_tuple_key(n, key));

  tmp = (tuple_hmap_rec_t *) safe_malloc(sizeof(tuple_hmap_rec_t) + n * sizeof(int32_t));
  tmp->hash = hash;
  tmp->arity = n;
  for (i=0; i<n; i++) {
    tmp->key[i] = key[i];
  }

  return tmp;
}



/*
 * HASH TABLE
 */

/*
 * Allocate and initialize and array of n record pointers
 */
static tuple_hmap_rec_t **alloc_rec_array(uint32_t n) {
  tuple_hmap_rec_t **tmp;
  uint32_t i;

  tmp = (tuple_hmap_rec_t **) safe_malloc(n * sizeof(tuple_hmap_rec_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  return tmp;
}




/*
 * For debugging: check whether n is 0 or a power of 2
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n-1)) == 0;
}
#endif


/*
 * Initialization:
 * - n = initial size (must be a power of 2)
 * - if n = 0, the default initial size is used
 */
void init_tuple_hmap(tuple_hmap_t *hmap, uint32_t n) {
  if (n == 0) {
    n = TUPLE_HMAP_DEF_SIZE;
  }

  if (n >= TUPLE_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));

  hmap->data = alloc_rec_array(n);
  hmap->size = n;
  hmap->nelems = 0;
  hmap->ndeleted = 0;
  hmap->resize_threshold = (uint32_t) (n * TUPLE_HMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t) (n * TUPLE_HMAP_CLEANUP_RATIO);
}



/*
 * Check whether r is a valid record pointer
 */
static inline bool live_tuple_record(tuple_hmap_rec_t *r) {
  return (r != NULL) && (r != TUPLE_HMAP_DELETED);
}



/*
 * Free all memory used by hmap
 */
void delete_tuple_hmap(tuple_hmap_t *hmap) {
  tuple_hmap_rec_t **tmp;
  uint32_t i, n;

  tmp = hmap->data;
  n = hmap->size;
  for (i=0; i<n; i++) {
    if (live_tuple_record(tmp[i])) {
      safe_free(tmp[i]);
    }
  }

  safe_free(tmp);
  hmap->data = NULL;
}


/*
 * Empty the hash table
 */
void reset_tuple_hmap(tuple_hmap_t *hmap) {
  tuple_hmap_rec_t **tmp;
  uint32_t i, n;

  tmp = hmap->data;
  n = hmap->size;
  for (i=0; i<n; i++) {
    if (live_tuple_record(tmp[i])) {
      safe_free(tmp[i]);
    }
    tmp[i] = NULL;
  }

  hmap->nelems = 0;
  hmap->ndeleted = 0;
}



/*
 * Add record r to array a
 * - a must be an array of size 2^k for k > 0
 * - mask must be equal to (2^k -1)
 * - there must be no deleted markers in a
 * - a must not be full.
 */
static void tuple_hmap_clean_copy(tuple_hmap_rec_t **a, tuple_hmap_rec_t *r, uint32_t mask) {
  uint32_t i;

  i = r->hash & mask;
  while (a[i] != NULL) {
    i ++;
    i &= mask;
  }
  a[i] = r;
}



/*
 * Remove the deletion marks
 */
static void tuple_hmap_cleanup(tuple_hmap_t *hmap) {
  tuple_hmap_rec_t **tmp;
  tuple_hmap_rec_t *r;
  uint32_t i, n, mask;

  n = hmap->size;
  tmp = alloc_rec_array(n);
  mask = n - 1;
  for (i=0; i<n; i++) {
    r = hmap->data[i];
    if (live_tuple_record(r)) {
      tuple_hmap_clean_copy(tmp, r, mask);
    }
  }

  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->ndeleted = 0;
}


/*
 * Double the hash-table size and keep its content
 */
static void tuple_hmap_extend(tuple_hmap_t *hmap) {
  tuple_hmap_rec_t **tmp;
  tuple_hmap_rec_t *r;
  uint32_t i, n, n2, mask;

  n = hmap->size;
  n2 = n << 1;
  if (n2 >= TUPLE_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n2));

  tmp = alloc_rec_array(n2);
  mask = n2 - 1;
  for (i=0; i<n; i++) {
    r = hmap->data[i];
    if (live_tuple_record(r)) {
      tuple_hmap_clean_copy(tmp, r, mask);
    }
  }

  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->size = n2;
  hmap->ndeleted = 0;
  hmap->resize_threshold = (uint32_t) (n2 * TUPLE_HMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t) (n2 * TUPLE_HMAP_CLEANUP_RATIO);
}






/*
 * Find record that matches the given key
 * - key must be an array of n integers
 * - return NULL if there's no matching record
 */
tuple_hmap_rec_t *tuple_hmap_find(tuple_hmap_t *hmap, uint32_t n, int32_t key[]) {
  tuple_hmap_rec_t *r;
  uint32_t i, h, mask;

  assert(n <= TUPLE_HMAP_MAX_ARITY && hmap->nelems < hmap->size
         && is_power_of_two(hmap->size));

  h = hash_tuple_key(n, key);
  mask = hmap->size - 1;
  i = h & mask;

  for (;;) {
    r = hmap->data[i];
    if (r == NULL ||
        (r != TUPLE_HMAP_DELETED && r->hash == h && r->arity == n && equal_tuples(n, key, r->key))) {
      return r;
    }
    i ++;
    i &= mask;
  }
}



/*
 * Find or add a record with the given key
 * - key must be an array of n integers
 * - if there's a matching record in the table, it's returned and *new is set to false.
 * - otherwise, a new record is created and added to the table, *new is set to true,
 *   and the new record is returned.
 *   The value field of the new record is not initialized.
 */
tuple_hmap_rec_t *tuple_hmap_get(tuple_hmap_t *hmap, uint32_t n, int32_t key[], bool *new) {
  tuple_hmap_rec_t *r;
  uint32_t i, j, h, mask;

  assert(n <= TUPLE_HMAP_MAX_ARITY && hmap->nelems < hmap->size &&
         is_power_of_two(hmap->size));

  h = hash_tuple_key(n, key);
  mask = hmap->size - 1;
  i = h & mask;

  for (;;) {
    r = hmap->data[i];
    if (r == NULL) goto add;
    if (r == TUPLE_HMAP_DELETED) break;
    if (r->hash == h && r->arity == n && equal_tuples(n, key, r->key)) goto found;
    i ++;
    i &= mask;
  }

  // i = where the new record will be added if necessary
  j = i;
  for (;;) {
    j ++;
    j &= mask;
    r = hmap->data[j];
    if (r == NULL) {
      hmap->ndeleted --;
      goto add;
    }
    if (r != TUPLE_HMAP_DELETED && r->hash == h && r->arity == n && equal_tuples(n, key, r->key)) {
      goto found;
    }
  }

 add:
  assert(hmap->data[i] == NULL || hmap->data[i] == TUPLE_HMAP_DELETED);
  r = new_tuple_hmap_record(h, n, key);
  hmap->data[i] = r;
  hmap->nelems ++;
  if (hmap->nelems + hmap->ndeleted > hmap->resize_threshold) {
    tuple_hmap_extend(hmap);
  }
  *new = true;
  return r;

 found:
  *new = false;
  return r;
}



/*
 * Add the record (key, val) to the table
 * - key must be an array of n integers
 * - n must be no more than TUPLE_HMAP_MAX_ARITY
 * - there must not be a record with the same key in the table.
 */
void tuple_hmap_add(tuple_hmap_t *hmap, uint32_t n, int32_t key[], int32_t val) {
  tuple_hmap_rec_t *r;
  uint32_t i, h, mask;

  assert(tuple_hmap_find(hmap, n, key) == NULL);

  h = hash_tuple_key(n, key);
  r = new_tuple_hmap_record(h, n, key);
  r->value = val;

  mask = hmap->size - 1;
  i = h & mask;
  while (live_tuple_record(hmap->data[i])) {
    i ++;
    i &= mask;
  }

  assert(hmap->data[i] == NULL || hmap->data[i] == TUPLE_HMAP_DELETED);
  if (hmap->data[i] == TUPLE_HMAP_DELETED) {
    hmap->ndeleted --;
  }
  hmap->data[i] = r;
  hmap->nelems ++;
  if (hmap->nelems + hmap->ndeleted > hmap->resize_threshold) {
    tuple_hmap_extend(hmap);
  }
}


/*
 * Remove record r from the table
 */
void tuple_hmap_erase(tuple_hmap_t *hmap, tuple_hmap_rec_t *r) {
  uint32_t i, mask;

  assert(tuple_hmap_find(hmap, r->arity, r->key) == r);

  mask = hmap->size - 1;
  i = r->hash & mask;
  while (hmap->data[i] != r) {
    i ++;
    i &= mask;
  }

  safe_free(r);

  hmap->data[i] = TUPLE_HMAP_DELETED;
  hmap->nelems --;
  hmap->ndeleted ++;
  if (hmap->ndeleted > hmap->cleanup_threshold) {
    tuple_hmap_cleanup(hmap);
  }
}



/*
 * Remove record that matches the given key
 * - key must be an array of n integers
 * - n must be no more than TUPLE_HMAP_MAX_ARITY
 * - no change if there's no matching record in the table.
 */
void tuple_hmap_remove(tuple_hmap_t *hmap, uint32_t n, int32_t key[]) {
  tuple_hmap_rec_t *r;
  uint32_t i, h, mask;

  assert(n <= TUPLE_HMAP_MAX_ARITY && hmap->nelems < hmap->size &&
         is_power_of_two(hmap->size));

  h = hash_tuple_key(n, key);
  mask = hmap->size - 1;
  i = h & mask;

  for (;;) {
    r = hmap->data[i];
    if (r == NULL) return;
    if (r != TUPLE_HMAP_DELETED && r->hash == h &&
        r->arity == n && equal_tuples(n, key, r->key)) break;
    i ++;
    i &= mask;
  }

  safe_free(r);

  hmap->data[i] = TUPLE_HMAP_DELETED;
  hmap->nelems --;
  hmap->ndeleted ++;
  if (hmap->ndeleted > hmap->cleanup_threshold) {
    tuple_hmap_cleanup(hmap);
  }
}



/*
 * Garbage collection
 * - f is a function that indicates whether a record should be kept or not
 * - aux is an auxiliary pointer passed as argument to f
 * The function scans the hash table and calls f(aux, r) for every record r
 * in the table. If f returns false, r is deleted, otherwise, r is kept.
 */
void tuple_hmap_gc(tuple_hmap_t *hmap, void *aux, tuple_hmap_keep_fun_t f) {
  tuple_hmap_rec_t *r;
  uint32_t i, n;

  n = hmap->size;
  for (i=0; i< n; i++) {
    r = hmap->data[i];
    if (live_tuple_record(r) && !f(aux, r)) {
      // r must be deleted
      safe_free(r);
      hmap->data[i] = TUPLE_HMAP_DELETED;
      hmap->nelems --;
      hmap->ndeleted ++;
    }
  }

  if (hmap->ndeleted > hmap->cleanup_threshold) {
    tuple_hmap_cleanup(hmap);
  }
}

