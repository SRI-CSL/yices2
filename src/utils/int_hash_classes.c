/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * HASH TABLE FOR MAINTAINING EQUIVALENCE CLASSES
 *
 * Objects are represented by non-negative integers and
 * an equivalence relation is defined by a match predicate.
 * The table stores one representative per class and allows
 * one to quickly find it.
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "utils/int_hash_classes.h"


/*
 * For debugging: check whether n is a power of two
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


/*
 * Initialize table
 * - n = initial table size:
 *   n must be a power of 2. If n=0, the default size is used.
 * - hash_fn, match_fn, aux: customization
 * - the table is empty, classes is not allocated yet (NULL).
 */
void init_int_hclass(int_hclass_t *table, uint32_t n, void *aux, iclass_hash_fun_t hash_fn,
                     iclass_match_fun_t match_fn) {
  int32_t *tmp;
  uint32_t i;

  if (n == 0) {
    n = DEF_ICLASS_SIZE;
  }

  if (n >= MAX_ICLASS_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));

  // Initialize: empty hash table of size n
  tmp = (int32_t *) safe_malloc(n * sizeof(int32_t));
  for (i=0; i<n; i++) {
    tmp[i] = null_index;
  }

  table->data = tmp;
  table->size = n;
  table->nelems = 0;
  table->resize_threshold = (uint32_t)(n * ICLASS_RESIZE_RATIO);
  table->aux = aux;
  table->hash = hash_fn;
  table->match = match_fn;
}


/*
 * Delete: free all memory
 */
void delete_int_hclass(int_hclass_t *table) {
  safe_free(table->data);
  table->data = NULL;
}


/*
 * Reset: empty the table
 * - remove all classes
 * - remove all elements in the hash table.
 */
void reset_int_hclass(int_hclass_t *table) {
  uint32_t i, n;

  n = table->size;
  for (i=0; i<n; i++) {
    table->data[i] = null_index;
  }
  table->nelems = 0;
}


/*
 * Copy element x into array a
 * - h = hash code of x
 * - mask = size of a - 1
 * - size of a must be a power of two
 * - a must not be full
 */
static void int_hclass_copy_record(int32_t *a, int32_t x, uint32_t h, uint32_t mask) {
  assert(x != null_index);

  h &= mask;
  while (a[h] != null_index) {
    h ++;
    h &= mask;
  }
  a[h] = x;
}



/*
 * Resize the hash table: double the size, keep the content
 */
static void resize_int_hclass(int_hclass_t *table) {
  int32_t *tmp;
  int32_t x;
  uint32_t i, h, n, n2, mask;

  n = table->size;
  n2 = n << 1;
  if (n2 >= MAX_ICLASS_SIZE) {
    out_of_memory();
  }

  tmp = (int32_t *) safe_malloc(n2 * sizeof(int32_t));
  for (i=0; i<n2; i++) {
    tmp[i] = null_index;
  }

  // copy current content into tmp
  mask = n2 - 1;
  for (i=0; i<n; i++) {
    x = table->data[i];
    if (x != null_index) {
      h = table->hash(table->aux, x);
      int_hclass_copy_record(tmp, x, h, mask);
    }
  }

  // cleanup
  safe_free(table->data);
  table->data = tmp;
  table->size = n2;
  table->resize_threshold = (uint32_t) (n2 * ICLASS_RESIZE_RATIO);
}



/*
 * Search for the representative in x's equivalence class
 * - return null_idx (-1) is there's none
 */
int32_t int_hclass_find_rep(int_hclass_t *table, int32_t x) {
  uint32_t h, mask;
  int32_t y;

  assert(table->size > table->nelems && x >= 0);

  mask = table->size - 1;
  h = table->hash(table->aux, x);
  for (;;) {
    h &= mask;
    y = table->data[h];
    if (y < 0 || table->match(table->aux, x, y)) {
      return y;
    }
    h ++;
  }
}


/*
 * Search for the representative in x's equivalence class
 * If there's no existing representative, add x to the table
 * and return x.
 */
int32_t int_hclass_get_rep(int_hclass_t *table, int32_t x) {
  uint32_t h, mask;
  int32_t y;

  assert(table->size > table->nelems && x >= 0);

  mask = table->size - 1;
  h = table->hash(table->aux, x);
  for (;;) {
    h &= mask;
    y = table->data[h];
    if (y < 0) break;
    if (table->match(table->aux, x, y)) return y;
    h ++;
  }

  // add x in table->data[h]
  table->data[h] = x;
  table->nelems ++;
  if (table->nelems > table->resize_threshold) {
    resize_int_hclass(table);
  }
  return x;
}

