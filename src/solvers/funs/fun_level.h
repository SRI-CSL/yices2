/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * SUPPORT FOR STRATIFICATION
 */

/*
 * The code here defines an ordering on types to sort variables/arrays in
 * successive levels:
 * - fun_level[tau] = 0 if tau is atomic
 * - fun_level[tuple(tau_1 ... tau_n)] = max fun_level[tau_i] for i=1 to n
 * - fun_level[(-> tau_1 ...tau_n)] = 1 + max fun_level[tau_i] for i=1 to n
 *
 * The function/array solver must process variables in increasing level.
 * This is required to properly handle things like A: (-> (-> bool bool) T).
 * The index type for A is itself a (finite) function type. When the solver
 * builds a value for A, it will look at egraph classes of type (-> bool bool).
 * If there are more than four such class, the value for A will be wrong. This
 * won't happen if we process arrays/functions of type (-> bool bool) first.
 */

#ifndef __FUN_LEVEL_H
#define __FUN_LEVEL_H

#include <stdint.h>

#include "terms/types.h"

/*
 * level[i] = level of type i for (i=0 ... ntypes-1)
 * level[i] = -1 if not known
 * size = size of the level array
 */
typedef struct flevel_table_s {
  type_table_t *types;
  int32_t *level;
  uint32_t size;
} flevel_table_t;


#define DEF_FLEVEL_TABLE_SIZE 32
#define MAX_FLEVEL_TABLE_SIZE (UINT32_MAX/sizeof(uint32_t))

/*
 * Initialize: types = the relevant type table
 * Nothing is allocated yet.
 */
extern void init_flevel_table(flevel_table_t *table, type_table_t *types);

/*
 * Delete: free memory
 */
extern void delete_flevel_table(flevel_table_t *table);

/*
 * Compute and return the level of type tau
 * - tau must be a valid table in table->types
 */
extern uint32_t flevel(flevel_table_t *table, type_t tau); 


#endif /* __FUN_LEVEL_H */
