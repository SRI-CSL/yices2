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
 * Data structures for computing the free variables that occur in a term.
 */

/*
 * We use a hash table to map term indices to sets of variables.  A
 * variable set is stored as an array of terms, sorted in increasing
 * order.  We use int_array_hsets for hash-consing of the sets of
 * variables: so if t1 and t2 have the same set of variables,
 * we have varset(t1) == varset(t2) (pointer equality).
 */

#ifndef __FREE_VAR_COLLECTOR_H
#define __FREE_VAR_COLLECTOR_H

#include <stdint.h>
#include <stdbool.h>

#include "terms/terms.h"
#include "utils/int_harray_store.h"
#include "utils/ptr_hash_map.h"
#include "utils/ptr_stack.h"


/*
 * Collector structure:
 * - terms = pointer to the attached term table
 * - map: stores the mapping from term indices to sets
 * - store: stores the sets themselves and provides hash-consing
 * - stack for allocation of arrays
 */
typedef struct fvar_collector_s {
  term_table_t *terms;
  ptr_hmap_t map;
  int_harray_store_t store;
  ptr_stack_t stack;
} fvar_collector_t;



/*
 * Initialization:
 * - ttbl = the attached term table
 */
extern void init_fvar_collector(fvar_collector_t *collect, term_table_t *ttbl);


/*
 * Delete all memory used
 */
extern void delete_fvar_collector(fvar_collector_t *collect);


/*
 * Reset: empty the whole thing.
 */
extern void reset_fvar_collector(fvar_collector_t *collect);


/*
 * Compute the set of free variables in term t:
 * - t must be defined in collect->terms
 * - the set is returned as a harray structure a (cf. int_array_hsets)
 *   a->nelems = size of the set = n
 *   a->data[0 ... n-1] = variables of t listed in increasing order
 */
extern harray_t *get_free_vars_of_term(fvar_collector_t *collect, term_t t);


/*
 * Check whether t is a ground term:
 * - side effect: this computes the set of free variables of t
 */
extern bool term_is_ground(fvar_collector_t *collect, term_t t);


/*
 * Cleanup after term deletion:
 * - if t is deleted, then the mapping from t --> vars of t is removed
 * - also all sets that contain deleted variables are removed from store.
 */
extern void cleanup_fvar_collector(fvar_collector_t *collect);



#endif /* __FREE_VAR_COLLECTOR_H */
