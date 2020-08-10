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
 * EMATCHED INSTANCES
 */

#ifndef __EMATCH_INSTANCE_H
#define __EMATCH_INSTANCE_H


#include "context/context_types.h"

/*
 * PATTERNS
 */

/*
 * Single instance match
 */
typedef struct instance_s {
  term_t *vdata;            // variables to be replaced
  occ_t *odata;             // occurrences in egraph that replaces variables

  uint32_t nelems;          // size of vdata/odata
  int32_t compile_idx;      // index of yield instruction in compile instruction table
} instance_t;


/*
 * Instance table
 */
typedef struct instance_table_s {
  uint32_t size;
  uint32_t ninstances;
  instance_t *data;

  int_htbl_t htbl;  // hash table mapping instance hash to index in table
} instance_table_t;

#define DEF_INSTANCE_TABLE_SIZE  20
#define MAX_INSTANCE_TABLE_SIZE  (UINT32_MAX/8)



/*
 * Initialize: default size
 */
extern void init_instance_table(instance_table_t *table);

/*
 * Empty the table: delete all instance objects
 */
extern void reset_instance_table(instance_table_t *table);

 /*
 * Delete the table
 */
extern void delete_instance_table(instance_table_t *table);

/*
 * Allocate a new instance index i of instance size n
 * - vdata/odata are not initialized
 */
extern int32_t instance_table_alloc(instance_table_t *table, uint32_t n);


/*
 * Create or retrieve the instance
 */
extern int32_t mk_instance(instance_table_t *table, int32_t compile_idx, uint32_t n, term_t *vdata, occ_t *odata);





#endif /* __EMATCH_INSTANCE_H */
