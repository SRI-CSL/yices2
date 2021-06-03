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
 * HASH TABLE FOR MAINTAINING EQUIVALENCE CLASSES OF POINTERS
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "utils/ptr_hash_classes.h"

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
void init_ptr_hclass(ptr_hclass_t *table, uint32_t n, void *aux, pclass_hash_fun_t hash_fn,
                     pclass_match_fun_t match_fn) {
  void **tmp;
  uint32_t i;

  if (n == 0) {
    n = DEF_PCLASS_SIZE;
  }

  if (n >= MAX_PCLASS_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));

  // Initialize: empty hash table of size n
  tmp = (void **) safe_malloc(n * sizeof(void *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  table->data = tmp;
  table->size = n;
  table->nelems = 0;
  table->resize_threshold = (uint32_t)(n * PCLASS_RESIZE_RATIO);
  table->aux = aux;
  table->hash = hash_fn;
  table->match = match_fn;
}


/*
 * Delete: free all memory
 */
void delete_ptr_hclass(ptr_hclass_t *table) {
  safe_free(table->data);
  table->data = NULL;
}


/*
 * Reset: empty the table
 * - remove all classes
 * - remove all elements in the hash table.
 */
void reset_ptr_hclass(ptr_hclass_t *table) {
  uint32_t i, n;

  n = table->size;
  for (i=0; i<n; i++) {
    table->data[i] = NULL;
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
static void ptr_hclass_copy(void **a, void *x, uint32_t h, uint32_t mask) {
  assert(x != NULL);

  h &= mask;
  while (a[h] != NULL) {
    h ++;
    h &= mask;
  }
  a[h] = x;
}



/*
 * Resize the hash table: double the size, keep the content
 */
static void resize_ptr_hclass(ptr_hclass_t *table) {
  void **tmp;
  void *x;
  uint32_t i, h, n, n2, mask;

  n = table->size;
  n2 = n << 1;
  if (n2 >= MAX_PCLASS_SIZE) {
    out_of_memory();
  }

  tmp = (void **) safe_malloc(n2 * sizeof(void *));
  for (i=0; i<n2; i++) {
    tmp[i] = NULL;
  }

  // copy current content into tmp
  mask = n2 - 1;
  for (i=0; i<n; i++) {
    x = table->data[i];
    if (x != NULL) {
      h = table->hash(table->aux, x);
      ptr_hclass_copy(tmp, x, h, mask);
    }
  }

  // cleanup
  safe_free(table->data);
  table->data = tmp;
  table->size = n2;
  table->resize_threshold = (uint32_t) (n2 * PCLASS_RESIZE_RATIO);
}



/*
 * Search for the representative in x's equivalence class
 * - return NULL if there's none
 */
void *ptr_hclass_find_rep(const ptr_hclass_t *table, void *x) {
  uint32_t h, mask;
  void *y;

  assert(table->size > table->nelems && x != NULL);

  mask = table->size - 1;
  h = table->hash(table->aux, x);
  for (;;) {
    h &= mask;
    y = table->data[h];
    if (y == NULL || table->match(table->aux, x, y)) {
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
void *ptr_hclass_get_rep(ptr_hclass_t *table, void *x) {
  uint32_t h, mask;
  void *y;

  assert(table->size > table->nelems && x != NULL);

  mask = table->size - 1;
  h = table->hash(table->aux, x);
  for (;;) {
    h &= mask;
    y = table->data[h];
    if (y == NULL) break;
    if (table->match(table->aux, x, y)) return y;
    h ++;
  }

  // add x in table->data[h]
  table->data[h] = x;
  table->nelems ++;
  if (table->nelems > table->resize_threshold) {
    resize_ptr_hclass(table);
  }
  return x;
}

