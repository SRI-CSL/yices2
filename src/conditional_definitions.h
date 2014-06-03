/*
 * ATTEMPT TO LEARN CONSTRAINTS ON VARIABLES FROM CONDITIONAL DEFINITONS
 */

/*
 * In this module, a conditional definition is a formula of the form (condition => (term = constant))
 */

#ifndef __CONDITIONAL_DEFINITIONS_H
#define __CONDITIONAL_DEFINITIONS_H

#include <stdint.h>
#include <stdbool.h>

#include "int_vectors.h"
#include "int_queues.h"
#include "int_hash_sets.h"
#include "ptr_vectors.h"
#include "context.h"


/*
 * Record to store a conditional definition
 * - term = defined term
 * - value = constant term
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
  uint32_t nconds;
  term_t cond[0]; // real size = nconds
} cond_def_t;


// Bound on the number of conjuncts we want to consider
#define MAX_COND_DEF_CONJUNCTS 10


/*
 * Data structure to collect conditional definitions
 * - pointers to the relevant context and term table
 * - cdefs = vector of conditional definitons
 */
typedef struct cond_def_collector_s {
  context_t *ctx;
  term_table_t *terms;
  pvector_t cdefs;

  // auxiliary structures
  ivector_t assumptions;
  int_queue_t queue;
  int_hset_t cache;
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
 * - add the defintions to c->cdefs
 */
extern void extract_conditional_definitions(cond_def_collector_t *c, term_t f);


#endif /* __CONDITIONAL_DEFINITIONS_H */
