/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * HASH TABLES OF NON-NEGATIVE INTEGERS FOR HASH CONSING.
 */

#include <stdint.h>
#include <assert.h>

#include "utils/int_hash_tables.h"
#include "utils/memalloc.h"


/*
 * For debugging: check whether n is a power of two
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif



/*
 * Initialize table: n = initial size (must be a power of 2)
 * If n = 0 set size = default value
 */
void init_int_htbl(int_htbl_t *table, uint32_t n) {
  uint32_t i;
  int_hrec_t *tmp;

  if (n == 0) {
    n = INT_HTBL_DEFAULT_SIZE;
  }

  if (n >= MAX_HTBL_SIZE) {
    out_of_memory(); // abort
  }

  assert(is_power_of_two(n));

  tmp = (int_hrec_t *) safe_malloc(n * sizeof(int_hrec_t));
  for (i=0; i<n; i++) {
    tmp[i].value = NULL_VALUE;
  }

  table->records = tmp;
  table->size = n;
  table->nelems = 0;
  table->ndeleted = 0;

  table->resize_threshold = (uint32_t)(n * RESIZE_RATIO);
  table->cleanup_threshold = (uint32_t)(n * CLEANUP_RATIO);
}


/*
 * Delete table
 */
void delete_int_htbl(int_htbl_t *table) {
  safe_free(table->records);
  table->records = NULL;
}


/*
 * Reset table: remove all elements
 */
void reset_int_htbl(int_htbl_t *table) {
  uint32_t i, n;

  n = table->size;
  for (i=0; i<n; i++) {
    table->records[i].value = NULL_VALUE;
  }

  table->nelems = 0;
  table->ndeleted = 0;
}




/*
 * Copy record <k, v> into a clean record array t.
 * t contains no DELETED_VALUE and must have at least one empty slot
 * <k, v> must not be present in t.
 * mask must be 2^n - 1 and (size of t) = 2^n
 */
static void int_htbl_copy_record(int_hrec_t *t, uint32_t k, int32_t v, uint32_t mask) {
  uint32_t j;
  int_hrec_t *r;

  j = k & mask;
  for (;;) {
    r = t + j;
    if (r->value == NULL_VALUE) {
      r->value = v;
      r->key = k;
      return;
    }
    j ++;
    j &= mask;
  }
}


/*
 * Remove deleted elements
 */
static void int_htbl_cleanup(int_htbl_t *table) {
  int_hrec_t *tmp;
  uint32_t j, n;
  uint32_t mask;
  int32_t v;

  n = table->size;
  tmp = (int_hrec_t *) safe_malloc(n * sizeof(int_hrec_t));
  for (j=0; j<n; j++) {
    tmp[j].value = NULL_VALUE;
  }

  mask = n - 1;
  for (j=0; j<n; j++) {
    v = table->records[j].value;
    if (v >= 0) {
      int_htbl_copy_record(tmp, table->records[j].key, v, mask);
    }
  }

  safe_free(table->records);
  table->records = tmp;
  table->ndeleted = 0;
}



/*
 * Remove deleted elements and make table twice as large
 */
static void int_htbl_extend(int_htbl_t *table) {
  int_hrec_t *tmp;
  uint32_t j, n, n2;
  uint32_t mask;
  int32_t v;

  n = table->size;
  n2 = n<<1;
  if (n2 == 0 || n2 >= MAX_HTBL_SIZE) {
    // overflow or too large
    out_of_memory();
  }

  tmp = (int_hrec_t *) safe_malloc(n2 * sizeof(int_hrec_t));
  for (j=0; j<n2; j++) {
    tmp[j].value = NULL_VALUE;
  }
  mask = n2 - 1;

  for (j=0; j<n; j++) {
    v = table->records[j].value;
    if (v >= 0) {
      int_htbl_copy_record(tmp, table->records[j].key, v, mask);
    }
  }

  safe_free(table->records);
  table->records = tmp;
  table->ndeleted = 0;
  table->size = n2;

  // keep same fill/cleanup ratios
  table->resize_threshold = (uint32_t) (n2 * RESIZE_RATIO);
  table->cleanup_threshold = (uint32_t) (n2 * CLEANUP_RATIO);
}


/*
 * Erase <k, v>
 */
void int_htbl_erase_record(int_htbl_t *table, uint32_t k, int32_t v) {
  uint32_t mask, j;
  int_hrec_t *r;

  // table must not be full, otherwise the function loops
  assert(table->size > table->nelems + table->ndeleted);

  mask = table->size - 1;
  j = k & mask;
  for (;;) {
    r = table->records + j;
    if (r->value == v) break;
    if (r->value == NULL_VALUE) return;
    j ++;
    j &= mask;
  }

  assert(r->key == k && r->value == v);
  table->nelems --;
  table->ndeleted ++;
  r->value = DELETED_VALUE;
  if (table->ndeleted > table->cleanup_threshold) {
    int_htbl_cleanup(table);
  }
}


/*
 * Add record <k, v> to the table
 * - the record must not be present in the table
 */
void int_htbl_add_record(int_htbl_t *table, uint32_t k, int32_t v) {
  uint32_t mask, j;
  int_hrec_t *r;

  assert(table->size > table->nelems + table->ndeleted);

  mask = table->size - 1;
  j = k & mask;
  for (;;) {
    r = table->records + j;
    if (r->value == NULL_VALUE) break;
    assert(r->value != v);
    j ++;
    j &= mask;
  }

  // add <k, v> into record r
  table->nelems ++;
  r->key = k;
  r->value = v;

  if (table->nelems + table->ndeleted > table->resize_threshold) {
    int_htbl_extend(table);
  }
}


/*
 * Find index of object equal to o or return -1 if no such index is in the hash table.
 */
int32_t int_htbl_find_obj(int_htbl_t *table, int_hobj_t *o) {
  uint32_t mask, j, k;
  int32_t v;
  int_hrec_t *r;

  // the table must not be full, otherwise, the function loops
  assert(table->size > table->nelems + table->ndeleted);

  mask = table->size - 1;
  k = o->hash(o);
  j = k & mask;
  for (;;) {
    r = table->records + j;
    v = r->value;
    if ((v >= 0 && r->key == k && o->eq(o, v)) || v == NULL_VALUE) {
      return v;
    }
    j ++;
    j &= mask;
  }
}


/*
 * Allocate an index for o (by calling build) then store this index and k in
 * record r. k must be the hash code of o.
 */
static int32_t int_htbl_store_new_obj(int_htbl_t *table, int_hrec_t *r, uint32_t k, int_hobj_t *o) {
  int32_t v;

  v = o->build(o);

  // error in build is signaled by returning v < 0
  if (v >= 0) {
    table->nelems ++;
    r->key = k;
    r->value = v;

    if (table->nelems + table->ndeleted > table->resize_threshold) {
      int_htbl_extend(table);
    }
  }

  return v;
}


/*
 * Get index of an object equal to o if such an index is in the table.
 * Otherwise, allocate an index by calling o->build(o) then store that index
 * in the table.
 */
int32_t int_htbl_get_obj(int_htbl_t *table, int_hobj_t *o) {
  uint32_t mask, j, k;
  int32_t v;
  int_hrec_t *r;
  int_hrec_t *aux;

  assert(table->size > table->nelems + table->ndeleted);

  mask = table->size - 1;
  k = o->hash(o);
  j = k & mask;

  for (;;) {
    r = table->records + j;
    v = r->value;
    if (v == NULL_VALUE) return int_htbl_store_new_obj(table, r, k, o);
    if (v == DELETED_VALUE) break;
    if (r->key == k && o->eq(o, v)) return v;
    j ++;
    j &= mask;
  }

  // aux will be used to store the new index if needed
  aux = r;
  for (;;) {
    j ++;
    j &= mask;
    r = table->records + j;
    v = r->value;
    if (v == NULL_VALUE) {
      table->ndeleted --;
      return int_htbl_store_new_obj(table, aux, k, o);
    }
    if (v >= 0 && r->key == k && o->eq(o, v)) return v;
  }
}


