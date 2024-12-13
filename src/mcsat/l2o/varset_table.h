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
 * Table for hash-consing of set of variables
 * Adapted from pprod_table
 */

#ifndef __VARSET_TABLE_H
#define __VARSET_TABLE_H

#include <stdint.h>

#include "yices.h"
#include "utils/bitvectors.h"
#include "utils/indexed_table.h"
#include "utils/int_hash_tables.h"
#include "utils/int_hash_sets.h"

typedef struct varset_table_elem_s {
  union {
    indexed_table_elem_t elem;
    int_hset_t *vars_set;
  };
} varset_table_elem_t;

/*
 * - varsets stores the sets of variables.
 * - mark[i] is used during garbage collection.
 *
 * Other components:
 * - htbl = hash table for hash consing
 */
typedef struct varset_table_s {
  indexed_table_t varsets;
  byte_t *mark;

  int_htbl_t htbl;
} varset_table_t;


/*
 * Default and maximal sizes
 */
#define VARSET_TABLE_DEF_SIZE 64
#define VARSET_TABLE_MAX_SIZE (UINT32_MAX/sizeof(int_hset_t *))


/*
 * Initialization: create an empty table.
 * - n = initial size. If n=0, the default is used.
 */
extern void init_varset_table(varset_table_t *table, uint32_t n);


/*
 * Delete the table and all the sets of variables it contains.
 */
extern void delete_varset_table(varset_table_t *table);


/*
 * Empty the table
 */
extern void reset_varset_table(varset_table_t *table);


/*
 * Add the set of variables a
 * - a must be closed
 * - if there's an element b equal to a already in the table, then return b,
 * - otherwise, create a new element equal to a and store it in
 *   the table.
 */
extern int32_t add_varset(varset_table_t *table, int_hset_t *a);


extern int_hset_t* get_varset(varset_table_t *table, uint32_t i);


/*
 * Find the index of vars_set in table
 * - return -1 if vars_set is not in the table
 */
extern int32_t find_varset_id(varset_table_t *table, int_hset_t *vars_set);

/*
 * DELETION AND GARBAGE COLLECTION
 */

/*
 * Remove vars_set from the table and free the corresponding pprod_t object.
 * - vars_set must be present in the table (and must be distinct from empty_vars_set,
 *   end_vars_set, or any tagged variable).
 */
extern void delete_varset(varset_table_t *table, int_hset_t *vars_set);

/*
 * Mark vars_set to prevent its deletion during garbage collection
 * - vars_set must be present in the table
 */
extern void varset_table_set_gc_mark(varset_table_t *table, int_hset_t *vars_set);

/*
 * Call the garbage collector:
 * - delete every varset not marked
 * - then clear all the marks
 */
extern void varset_table_gc(varset_table_t *table);


#endif /* __VARSET_TABLE_H */
