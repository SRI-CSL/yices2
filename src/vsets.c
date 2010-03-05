/*
 * Sets of integers stored as arrays
 * Support for hash consing
 */

#include <assert.h>
#include <stdbool.h>

#include "memalloc.h"
#include "hash_functions.h"
#include "vsets.h"


/*
 * VSETS
 */

/*
 * Hash code of set a[0 ...n-1]
 */
static inline uint32_t hash_vset(int32_t *a, uint32_t n) {
  return jenkins_hash_intarray(n, a);
}


/*
 * Create set a[0 ... n-1]
 * - don't set the hash code
 */
static vset_t *make_vset(int32_t *a, uint32_t n) {
  vset_t *tmp;
  uint32_t i;

  if (n >= MAX_VSET_SIZE) {
    out_of_memory();
  }

  tmp = (vset_t *) safe_malloc(sizeof(vset_t) + n * sizeof(int32_t));
  tmp->nelems = n;
  for (i=0; i<n; i++) {
    tmp->data[i] = a[i];
  }

  return tmp;
}


/*
 * Check whether v == a[0...n-1]
 */
static bool eq_vset(vset_t *p, int32_t *a, uint32_t n) {
  uint32_t i;

  if (p->nelems != n) {
    return false;
  }

  for (i=0; i<n; i++) {
    if (p->data[i] != a[i]) {
      return false;
    }
  }

  return true;
}



/*
 * HASH TABLE
 */

/*
 * Initialize table
 * - n = initial size
 * - n must be a power of 2. If n = 0, the default size is used.
 */
void init_vset_htbl(vset_htbl_t *table, uint32_t n) {
  uint32_t i;
  vset_t **tmp;

#ifndef NDEBUG 
  // check that n is a power of 2
  uint32_t n2;
  n2 = n;
  while (n2 > 1) {
    assert((n2 & 1) == 0);
    n2 >>= 1;
  }  
#endif

  if (n == 0) {
    n = DEF_VSET_HTBL_SIZE;
  }

  if (n >= MAX_VSET_HTBL_SIZE) {
    out_of_memory();
  }

  tmp = (vset_t **) safe_malloc(n * sizeof(vset_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  table->data = tmp;
  table->size = n;
  table->nelems = 0;
  table->ndeleted = 0;

  table->resize_threshold = (uint32_t) (n * VSET_HTBL_RESIZE_RATIO);
  table->cleanup_threshold = (uint32_t) (n * VSET_HTBL_CLEANUP_RATIO);
}


/*
 * Check whether p is a non-deleted/non-null pointer
 */
static inline bool live_vset(vset_t *p) {
  return p != NULL && p != DELETED_VSET;
}

/*
 * Delete the table
 */
void delete_vset_htbl(vset_htbl_t *table) {
  vset_t *p;
  uint32_t i, n;

  n = table->size;
  for (i=0; i<n; i++) {
    p = table->data[i];
    if (live_vset(p)) safe_free(p);
  }
  safe_free(table->data);
  table->data = NULL;
}


/*
 * Empty the table
 */
void reset_vset_htbl(vset_htbl_t *table) {
  vset_t *p;
  uint32_t i, n;

  n = table->size;
  for (i=0; i<n; i++) {
    p = table->data[i];
    if (live_vset(p)) safe_free(p);
    table->data[i] = NULL;
  }
  table->nelems = 0;
  table->ndeleted = 0;
}


/*
 * Store p in a clean data array
 * - mask = size of data - 1 (the size must be a power of 2)
 * - p->hash must be the correct hash code for p
 * - data must not contain DELETED_VSET marks and must have room for p
 */
static void vset_htbl_clean_copy(vset_t **data, vset_t *p, uint32_t mask) {
  uint32_t i;

  i = p->hash & mask;
  while (data[i] != NULL) {
    i ++;
    i &= mask;
  }
  data[i] = p;
}


/*
 * Remove all deletion markers from table
 */
static void vset_htbl_cleanup(vset_htbl_t *table) {
  vset_t **tmp, *p;
  uint32_t i, n, mask;

  n = table->size;
  tmp = (vset_t **) safe_malloc(n * sizeof(vset_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  mask = n - 1;
  for (i=0; i<n; i++) {
    p = table->data[i];
    if (live_vset(p)) {
      vset_htbl_clean_copy(tmp, p, mask);
    }
  }

  safe_free(table->data);
  table->data = tmp;
  table->ndeleted = 0;
}


/*
 * Remove all deleted elements and make the table twice larger
 */
static void vset_htbl_extend(vset_htbl_t *table) {
  vset_t **tmp, *p;
  uint32_t i, n, mask, new_size;

  n = table->size;
  new_size = n << 1;
  if (new_size >= MAX_VSET_HTBL_SIZE) {
    out_of_memory();
  }

  tmp = (vset_t **) safe_malloc(new_size * sizeof(vset_t *));
  for (i=0; i<new_size; i++) {
    tmp[i] = NULL;
  }

  mask = new_size - 1;
  for (i=0; i<n; i++) {
    p = table->data[i];
    if (live_vset(p)) {
      vset_htbl_clean_copy(tmp, p, mask);
    }
  }

  safe_free(table->data);
  table->data = tmp;
  table->size = new_size;
  table->ndeleted = 0;

  table->resize_threshold = (uint32_t) (new_size * VSET_HTBL_RESIZE_RATIO);
  table->cleanup_threshold = (uint32_t) (new_size * VSET_HTBL_CLEANUP_RATIO);
}


/*
 * Search for set a[0 ... n-1]
 */
vset_t *vset_htbl_find(vset_htbl_t *table, uint32_t n, int32_t *a) {
  vset_t *p;
  uint32_t i, h, mask;

  assert(table->nelems + table->ndeleted < table->size);

  mask = table->size - 1;
  h = hash_vset(a, n);
  i = h & mask;
  for (;;) {
    p = table->data[i];
    if (p == NULL || (p != DELETED_VSET && p->hash == h && eq_vset(p, a, n))) {
      return p;
    }
    i ++;
    i &= mask;
  }
}


/*
 * Find or create vset a[0...n-1]
 */
vset_t *vset_htbl_get(vset_htbl_t *table, uint32_t n, int32_t *a) {
  vset_t *p;
  uint32_t i, j, h, mask;

  assert(table->nelems + table->ndeleted < table->size);

  mask = table->size - 1;
  h = hash_vset(a, n);
  i = h & mask;
  for (;;) {
    p = table->data[i];
    if (p == NULL) goto add;
    if (p == DELETED_VSET) break;
    if (p->hash == h && eq_vset(p, a, n)) goto found;
    i ++;
    i &= mask;
  }

  // table->data[i] = where new set can be added
  j = i;
  for (;;) {
    j ++;
    j &= mask;
    p = table->data[j];
    if (p == NULL) {
      table->ndeleted --;
      goto add;
    }
    if (p != DELETED_VSET && p->hash == h && eq_vset(p, a, n)) goto found;
  }

 add:
  p = make_vset(a, n);
  p->hash = h;
  table->data[i] = p;
  table->nelems ++;
  if (table->nelems + table->ndeleted > table->resize_threshold) {
    vset_htbl_extend(table);
  }

 found:
  return p;  
}


/*
 * Remove v from the table
 * - v must be present
 */
void vset_htbl_remove(vset_htbl_t *table, uint32_t n, int32_t *a) {
  vset_t *p;
  uint32_t i, h, mask;

  assert(table->nelems + table->ndeleted < table->size);

  mask = table->size - 1;
  h = hash_vset(a, n);
  i = h & mask;
  for (;;) {
    p = table->data[i];
    if (p == NULL) return;
    if (p != DELETED_VSET && p->hash == h && eq_vset(p, a, n)) break;
    i ++;
    i &= mask;
  }

  // remove p
  safe_free(p);
  table->data[i] = DELETED_VSET;
  table->nelems --;
  table->ndeleted ++;

  if (table->ndeleted > table->cleanup_threshold) {
    vset_htbl_cleanup(table);
  }
}
