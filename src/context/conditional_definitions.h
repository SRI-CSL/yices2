/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PROCESS ASSERTIONS OF THE FORM (condition => term = constant)
 */

/*
 * The condition is required to be a Boolean combination of uninterpreted terms (e.g.,
 * something like (and x (not y)) where x and y are Boolean variables).
 *
 * If we have several clauses of the form
 *  (c1 => t = k1)
 *  (c2 => t = k2)
 *  ...
 *
 * Then we may be able to learn global constraints on t. In particular, benchmarks
 * in the QF_LRA/miplib family use encodings like this
 *    (x2 and x3 => tmp1 = 2)
 *    (not x2 and x3 => tmp1 = 1)
 *    (x2 and not x3 => tmp1 = 1)
 *    (not x2 and not x3 => tmp1 = 0).
 *
 * We can convert this to one constraint:
 *    tmp1 = 1.x2 + 1.x3  where x2 and x3 are now { 0, 1 } variables
 */


#ifndef __CONDITIONAL_DEFINITIONS_H
#define __CONDITIONAL_DEFINITIONS_H

#include <stdint.h>
#include <stdbool.h>

#include "context/context_types.h"
#include "utils/int_array_hsets.h"
#include "utils/int_vectors.h"
#include "utils/ptr_stack.h"
#include "utils/ptr_vectors.h"
#include "utils/simple_cache.h"


/*
 * Data structure to check that a term is a combination of Boolean
 * variables and to compute the set of variables.
 * - set of variables are stored using int_array_hset.
 * - we keep a cache that mapped term to the set
 * + a pointer stack for recursive exploration of terms
 * + a counter to abort exploration of large terms
 */
typedef struct bool_var_collector_s {
  context_t *ctx;
  term_table_t *terms;
  int_array_hset_t *store;
  simple_cache_t cache;
  ptr_stack_t stack;
  ivector_t buffer;
  uint32_t budget;
} bool_var_collector_t;



/*
 * Record to store a conditional definition
 * - term = defined term
 * - value = constant term
 * - vset = Boolean variables occurring in the conditions
 * - nconds = number of terms in cond
 * - cond = array of terms
 *
 * The array cond[0 ... nconds-1] is interpreted as a
 * conjunction of terms. The record represents the
 * formula:
 *    (cond[0] /\ ... /\ cond[nconds-1] => term = value)
 */
typedef struct cond_def_s {
  term_t term;
  term_t value;
  harray_t *vset;
  uint32_t nconds;
  term_t cond[0]; // real size = nconds
} cond_def_t;

#define MAX_COND_DEF_CONJUNCTS (UINT32_MAX/sizeof(term_t))


/*
 * Data structure to collect conditional definitions
 * - pointers to the relevant context and term table
 * - cdefs = vector of conditional definitions
 * - store = for building sets
 * - collector = for finding Boolean variables
 * - cache = for constructing truth-tables
 */
typedef struct cond_def_collector_s {
  context_t *ctx;
  term_table_t *terms;
  pvector_t cdefs;
  int_array_hset_t store;
  bool_var_collector_t collect;

  simple_cache_t cache;

  // auxiliary structures
  ivector_t assumptions;
  ivector_t aux;

  rational_t coeff[6];
  rational_t base;
  rational_t q_aux;

} cond_def_collector_t;



/*
 * OPERATIONS
 */

/*
 * Initialize a collector
 * - ctx = relevant context
 */
extern void init_cond_def_collector(cond_def_collector_t *c, context_t *ctx);


/*
 * Delete: free all memory
 */
extern void delete_cond_def_collector(cond_def_collector_t *c);


/*
 * Attempt to convert f to a conjunction of conditional definitions
 * - add the definitions to c->cdefs
 */
extern void extract_conditional_definitions(cond_def_collector_t *c, term_t f);

/*
 * Process all conditional definitions in c->cdefs
 */
extern void analyze_conditional_definitions(cond_def_collector_t *c);


#endif /* __CONDITIONAL_DEFINITIONS_H */
