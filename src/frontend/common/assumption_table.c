/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2018 SRI International.
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

#include <assert.h>

#include "frontend/common/assumption_table.h"
#include "utils/int_array_sort2.h"
#include "utils/memalloc.h"


/*
 * Initialize table:
 * - the size is 0 and nothing is allocated.
 */
void init_assumption_table(assumption_table_t *table) {
  table->data = NULL;
  table->index = NULL;
  table->size = 0;
  table->nelems = 0;
  table->index_size = 0;
}

/*
 * Delete: free memory
 */
void delete_assumption_table(assumption_table_t *table) {
  safe_free(table->data);
  safe_free(table->index);
  table->data = NULL;
  table->index = NULL;
}

/*
 * Reset: empty the table.
 */
void reset_assumption_table(assumption_table_t *table) {
  safe_free(table->index);
  table->index = NULL;
  table->nelems = 0;
  table->index_size = 0;
}


/*
 * Make the table larger
 */
static void extend_assumption_table(assumption_table_t *table) {
  uint32_t n;

  n = table->size;
  if (n == 0) {
    // initial allocation
    n = ASSUMPTION_TABLE_DEF_SIZE;
    assert(n <= ASSUMPTION_TABLE_MAX_SIZE);
    table->data = (assumption_t *) safe_malloc(n * sizeof(assumption_t));
    table->size = n;
  } else {
    // increase by 50%
    n += (n >> 1);
    if (n > ASSUMPTION_TABLE_MAX_SIZE) {
      out_of_memory();
    }
    table->data = (assumption_t *) safe_realloc(table->data, n * sizeof(assumption_t));
    table->size = n;
  }
}

/*
 * Add an assumption to the table
 * - t = assumed term
 * - name = name to use for t
 * - polarity: true if the assumption is 'name'
 *             false if the assumption is '(not name)'
 */
void assumption_table_add(assumption_table_t *table, term_t t, const char* name, bool polarity) {
  uint32_t i;

  i = table->nelems;
  if (i == table->size) {
    extend_assumption_table(table);
  }
  assert(i < table->size);
  table->data[i].name = name;
  table->data[i].term = t;
  table->data[i].polarity = polarity;
  table->nelems = i+1;
}


/*
 * Ordering: i < j between two indices
 */
static bool assumption_index_lt(void *data, int32_t i, int32_t j) {
  assumption_table_t *table;

  table = data;
  assert(0 <= i && i < table->nelems);
  assert(0 <= j && j < table->nelems);
  return table->data[i].term < table->data[j].term;
}

/*
 * Build the internal index and filter duplicates
 */
void assumption_table_build_index(assumption_table_t *table) {
  uint32_t i, j, n;
  int32_t x, y;

  assert(table->index == NULL && table->index_size == 0);

  n = table->nelems;

  if (n > 0) {

    table->index = (int32_t *) safe_malloc(n * sizeof(int32_t));
    for (i=0; i<n; i++) {
      table->index[i] = i;
    }

    // sort the indices
    int_array_sort2(table->index, n, table, assumption_index_lt);

    // remove duplicates
    x = table->index[0];
    j = 1;
    for (i=1; i<n; i++) {
      y = table->index[i];
      assert(table->data[x].term <= table->data[y].term);

      if (table->data[x].term < table->data[y].term) {
	table->index[j] = y;
	j ++;
	x = y;
      }
    }
    table->index_size = j;
  }
}


/*
 * Collect all the assumptions (no duplicates) in vector v
 */
void collect_assumptions(assumption_table_t *table, ivector_t *v) {
  uint32_t i, n;
  int32_t k;

  if (table->nelems > 0) {
    assert(table->index_size > 0 && table->index != NULL);
    n = table->index_size;
    for (i=0; i<n; i++) {
      k = table->index[i];
      ivector_push(v, table->data[k].term);
    }
  }
}

/*
 * Get the descriptor for assumpion t:
 * - this requires the index to be constructed
 * - returns NULL if there's no such assumption
 */
assumption_t *assumption_table_get(const assumption_table_t *table, term_t t) {
  uint32_t l, h, k;
  int32_t i;
  term_t u;

  if (table->nelems == 0) return NULL;
  
  assert(table->index != NULL && table->index_size > 0);
  
  // binary search in index
  l = 0;
  h = table->index_size;
  for (;;) {
    k = (l + h)/2; // no risk of overflow here since l < h <= index_size <= ASSUMPTION_TABLE_MAX_SIZE
    assert(l <= k && k < h);
    i = table->index[k];
    u = table->data[i].term;
    if (u == t) return table->data + i;
    if (l == k) return NULL;
    if (u < t) {
      l = k+1;
    } else {
      h = k;
    }
  }
}

