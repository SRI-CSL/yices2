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

/*
 * This is a data structure to store dependencies between integer indices.
 * Given n integers, the table stores an array dep[i] for all
 * i between 0 and n, where dep[i] is a vector of integers.
 *
 * This is intended to store a dependency graph: in dep[i] are
 * all the vertices that depend on i.
 */

#ifndef __DEP_TABLES_H
#define __DEP_TABLES_H

#include <stddef.h>
#include <stdint.h>
#include <assert.h>


/*
 * Data structure:
 * - size = size of the dep array
 * - nelems = number of elements for which dep[i] is initialized
 * - dep = array of vectors (we use index_vectors)
 *
 * We always have 0 <= nelems <= size.
 * - dep[i] is initialized for 0 <= i < nelems
 * - dep[i] is not initialized for nelems <= i < size.
 */
typedef struct dep_table_s {
  int32_t **dep;
  uint32_t nelems;
  uint32_t size;
} dep_table_t;


#define DEP_TABLE_DEF_SIZE 100
#define DEP_TABLE_MAX_SIZE (UINT32_MAX/sizeof(int32_t *))


/*
 * Initialize table:
 * - n = initial size. If n = 0 nothing is allocated yet.
 */
extern void init_dep_table(dep_table_t *table, uint32_t n);


/*
 * Delete: free all memory used by this table
 */
extern void delete_dep_table(dep_table_t *table);


/*
 * Empty the table: this frees all vectors stored in dep[i]
 * but keeps array dep (with its current size).
 */
extern void reset_dep_table(dep_table_t *table);


/*
 * Add a dependency from i to j:
 * - this adds j to dep[i].
 * - i must be non-negative
 */
extern void add_dependent(dep_table_t *table, int32_t i, int32_t j);


/*
 * Return the vector of dependents for i
 * - i must be non-negative
 * - the result is NULL if i has no dependents
 * - otherwise, the result is an index vector so all operations
 *   defined in index_vector.h can be used to examine its content.
 */
static inline int32_t *get_dependents(dep_table_t *table, int32_t i) {
  assert(0 <= i);
  return (i < table->nelems) ? table->dep[i] : NULL;
}


#endif /* __DEP_TABLES_H */
