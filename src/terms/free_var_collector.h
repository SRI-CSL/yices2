/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Data structures for computing the free variables that occur in a term.
 */

/*
 * We use a hash table to map term indices to sets of variables.  A
 * variable set is stored as an array of terms, sorted in increasing
 * order.  We use int_array_hsets for hash-consing of the sets of
 * variables: so if t1 and t2 have the same set of variables,
 * we have varsets(t1) == varset(t2) (pointer equality).
 */

#ifndef __FREE_VAR_COLLECTOR_H
#define __FREE_VAR_COLLECTOR_H

#include <stdint.h>
#include <stdbool.h>

#include "utils/ptr_hash_map.h"
#include "utils/int_array_hsets.h"
#include "utils/int_vectors.h"
#include "utils/int_hash_sets.h"
#include "utils/ptr_stack.h"
#include "terms/terms.h"


/*
 * Collector structure:
 * - terms = pointer to the attached term table
 * - map: stores the mapping from term indices to sets
 * - store: stores the sets themselves and provides hash-consing
 * Auxiliary components:
 * - stack for allocation of arrays
 * - aux, buffer: for computing unions of sets
 */
typedef struct fvar_collector_s {
  term_table_t *terms;
  ptr_hmap_t map;
  int_array_hset_t store;
  ptr_stack_t stack;
  ivector_t buffer;
  int_hset_t aux;
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
