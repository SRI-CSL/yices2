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
 * DEPENDENCY TABLES
 */

#include "utils/dep_tables.h"
#include "utils/index_vectors.h"
#include "utils/memalloc.h"

/*
 * Initialization:
 * - n = initial size
 */
void init_dep_table(dep_table_t *table, uint32_t n) {
  int32_t **tmp;

  if (n >= DEP_TABLE_MAX_SIZE) {
    out_of_memory();
  }

  tmp = NULL;
  if (n > 0) {
    tmp = (int32_t **) safe_malloc(n * sizeof(int32_t *));
  }

  table->dep = tmp;
  table->nelems = 0;
  table->size = n;
}



/*
 * Deletion: free memory
 */
void delete_dep_table(dep_table_t *table) {
  uint32_t i, n;

  n = table->nelems;
  for (i=0; i<n; i++) {
    delete_index_vector(table->dep[i]);
  }
  safe_free(table->dep);
  table->dep = NULL;
}


/*
 * Reset: empty the table
 */
void reset_dep_table(dep_table_t *table) {
  uint32_t i, n;

  n = table->nelems;
  for (i=0; i<n; i++) {
    delete_index_vector(table->dep[i]);
  }

  table->nelems = 0;
}


/*
 * Make the table large enough to have nelems = i+1
 * - i must be non-negative and larger than table->size
 */
static void dep_table_resize(dep_table_t *table, int32_t i) {
  uint32_t n;

  assert(0 <= i && i >= table->size);

  n = table->size;
  if (n == 0) { // initial allocation: try the default size
    n = DEP_TABLE_DEF_SIZE;
  } else {    // try 50% larger than the current size
    n += (n >> 1);
  }
  if (n <= i) {
    n = i+1;
  }

  if (n >= DEP_TABLE_MAX_SIZE) {
    out_of_memory();
  }

  table->dep = (int32_t **) safe_realloc(table->dep, n * sizeof(int32_t *));
  table->size = n;
}


/*
 * Increase nelems to i+1
 * - i must be non-negative and larger than table->nelems
 * - make dep larger if that's needed
 */
static void dep_table_increase_nelems(dep_table_t *table, int32_t i) {
  uint32_t j, n;

  assert(0 <= i && i >= table->nelems);

  if (table->size <= i) {
    dep_table_resize(table, i);
  }

  n = i + 1;
  assert(table->nelems < n && n <= table->size);

  for (j=table->nelems; j<n; j++) {
    table->dep[j] = NULL;
  }
  table->nelems = n;
}


/*
 * Add j as dependent of i
 */
void add_dependent(dep_table_t *table, int32_t i, int32_t j) {
  assert(0 <= i);

  if (i >= table->nelems) {
    dep_table_increase_nelems(table, i);
  }

  add_index_to_vector(table->dep + i, j);
}
