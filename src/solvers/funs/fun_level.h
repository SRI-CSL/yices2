/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2020 SRI International.
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
