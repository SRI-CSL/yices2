/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * HASH MAP: KEYS ARE STRINGS, VALUES ARE 32 BIT INTEGERS
 */

#include <assert.h>
#include <string.h>

#include "utils/memalloc.h"
#include "utils/refcount_strings.h"
#include "utils/hash_functions.h"
#include "utils/string_hash_map.h"


/*
 * For debugging: check whether n is a power of 2 (or n == 0)
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


/*
 * Initialization:
 * - n = initial size (must be a power of 2)
 * - if n = 0, the default size is used
 */
void init_strmap(strmap_t *hmap, uint32_t n) {
  strmap_rec_t *tmp;
  uint32_t i;

  if (n == 0) {
    n = STRMAP_DEF_SIZE;
  }

  if (n >= STRMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));
  tmp = (strmap_rec_t *) safe_malloc(n * sizeof(strmap_rec_t));
  for (i=0; i<n; i++) {
    tmp[i].key = NULL;
  }

  hmap->data = tmp;
  hmap->size = n;
  hmap->nelems = 0;
  hmap->ndeleted = 0;

  hmap->resize_threshold = (uint32_t) (n * STRMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t) (n * STRMAP_CLEANUP_RATIO);
}


/*
 * Check whether key is valid (i.e., not NULL or DELETED_KEY)
 */
#define MASK_TAG ((size_t) 3)

static inline bool valid_key(const char *key) {
  return (((size_t) key) & ~MASK_TAG) != ((size_t) NULL);
}


/*
 * Delete: call decref on all keys
 */
void delete_strmap(strmap_t *hmap) {
  uint32_t i, n;
  char *key;

  n = hmap->size;
  for (i=0; i<n; i++) {
    key = hmap->data[i].key;
    if (valid_key(key)) {
      string_decref(key);
    }
  }

  safe_free(hmap->data);
  hmap->data = NULL;
}


/*
 * Empty the table
 */
void reset_strmap(strmap_t *hmap) {
  uint32_t i, n;
  char *key;

  n = hmap->size;
  for (i=0; i<n; i++) {
    key = hmap->data[i].key;
    hmap->data[i].key = NULL;
    if (valid_key(key)) {
      string_decref(key);
    }
  }

  hmap->nelems = 0;
  hmap->ndeleted = 0;
}


/*
 * Make a copy of r in a clean array data
 * - r->hash must be the hash of r->key
 * - mask = size of data - 1
 * - there must be room ub data
 */
static void strmap_clean_copy(strmap_rec_t *data, strmap_rec_t *r, uint32_t mask) {
  uint32_t i;

  i = r->hash & mask;
  while (data[i].key != NULL) {
    i ++;
    i &= mask;
  }

  data[i] = *r;
}


/*
 * Remove the deleted records
 */
static void strmap_cleanup(strmap_t *hmap) {
  strmap_rec_t *r, *tmp;
  uint32_t i, n, mask;

  n = hmap->size;
  tmp = (strmap_rec_t *) safe_malloc(n * sizeof(strmap_rec_t));
  for (i=0; i<n; i++) {
    tmp[i].key = NULL;
  }

  mask = n - 1;
  r = hmap->data;
  for (i=0; i<n; i++) {
    if (valid_key(r->key)) {
      strmap_clean_copy(tmp, r, mask);
    }
    r ++;
  }

  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->ndeleted = 0;
}


/*
 * Remove deleted records and double the table size
 */
static void strmap_extend(strmap_t *hmap) {
  strmap_rec_t *r, *tmp;
  uint32_t i, n, n2, mask;

  n = hmap->size;
  n2 = n << 1;
  if (n2 >= STRMAP_MAX_SIZE) {
    out_of_memory();
  }

  tmp = (strmap_rec_t *) safe_malloc(n2 * sizeof(strmap_rec_t));
  for (i=0; i<n2; i++) {
    tmp[i].key = NULL;
  }

  mask = n2 - 1;
  r = hmap->data;
  for (i=0; i<n; i++) {
    if (valid_key(r->key)) {
      strmap_clean_copy(tmp, r, mask);
    }
    r ++;
  }

  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->size = n2;
  hmap->ndeleted = 0;

  hmap->resize_threshold = (uint32_t) (n2 * STRMAP_RESIZE_RATIO);
  hmap->cleanup_threshold = (uint32_t) (n2 * STRMAP_CLEANUP_RATIO);
}


/*
 * Search for record with the given key
 * - return NULL if not found
 */
strmap_rec_t *strmap_find(strmap_t *hmap, const char *key) {
  uint32_t mask, i, h;
  strmap_rec_t *d;

  assert(is_power_of_two(hmap->size) && hmap->nelems + hmap->ndeleted < hmap->size);

  mask = hmap->size - 1;
  h = jenkins_hash_string(key);
  i = h & mask;
  for (;;) {
    d = hmap->data + i;
    if (d->key == NULL) return NULL;
    if (d->key != DELETED_KEY && d->hash == h && strcmp(d->key, key) == 0) {
      return d;
    }
    i ++;
    i &= mask;
  }
}


/*
 * Return a pointer to a new record in a fresh data array
 * - h = hash of the key to add
 * - hmap->data must not contain records with DELETED_KEY
 * - no record in hmap->data has the same key
 */
static strmap_rec_t *strmap_get_clean(strmap_t *hmap, uint32_t h) {
  uint32_t i, mask;
  strmap_rec_t *d;

  assert(is_power_of_two(hmap->size) && hmap->ndeleted == 0 && hmap->nelems < hmap->size);

  mask = hmap->size - 1;
  i = h & mask;
  for (;;) {
    d = hmap->data + i;
    if (d->key == NULL) break;
    i ++;
    i &= mask;
  }

  return d;
}

/*
 * Find or create record with the given key
 * - set is_new to true if that's a new record
 * - set is_new to false otherwise
 */
strmap_rec_t *strmap_get(strmap_t *hmap, const char *key, bool *is_new) {
  uint32_t mask, i, h;
  strmap_rec_t *d, *aux;
  char *clone;

  assert(is_power_of_two(hmap->size) && hmap->nelems + hmap->ndeleted < hmap->size);

  mask = hmap->size - 1;
  h = jenkins_hash_string(key);
  i = h & mask;
  for (;;) {
    d = hmap->data + i;
    if (! valid_key(d->key)) break;
    if (d->hash == h && strcmp(d->key, key) == 0) goto found;
    i ++;
    i &= mask;
  }

  aux = d; // this is where the new record will go if needed
  while(d->key != NULL) {
    i ++;
    i &= mask;
    if (d->key != DELETED_KEY && d->hash == h && strcmp(d->key, key) == 0) goto found;
  }

  // not found: add a new record
  hmap->nelems ++;
  clone = clone_string(key);
  string_incref(clone);
  if (hmap->nelems + hmap->ndeleted > hmap->resize_threshold) {
    // resize: we can't use the current aux
    strmap_extend(hmap);
    aux = strmap_get_clean(hmap, h);
  }
  aux->key = clone;
  aux->hash = h;
  aux->val = 0;

  *is_new = true;
  return aux;

 found:
  *is_new = false;
  return d;
}


/*
 * Remove record r
 */
void strmap_erase(strmap_t *hmap, strmap_rec_t *r) {
  assert(strmap_find(hmap, r->key) == r);

  string_decref(r->key);
  r->key = DELETED_KEY;
  hmap->nelems --;
  hmap->ndeleted ++;
  if (hmap->ndeleted > hmap->cleanup_threshold) {
    strmap_cleanup(hmap);
  }
}


/*
 * Iterator: apply f(aux, r) to all records r in the table
 */
void strmap_iterate(strmap_t *hmap, void *aux, strmap_iterator_t f) {
  uint32_t i, n;
  strmap_rec_t *r;

  n = hmap->size;
  r = hmap->data;
  for (i=0; i<n; i++) {
    if (valid_key(r->key)) {
      f(aux, r);
    }
    r ++;
  }
}
