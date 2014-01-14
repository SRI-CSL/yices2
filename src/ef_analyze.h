/*
 * Process a term t as part of ef-solving:
 * - check whether t is quantifier free
 * - collect the variables of t (treated as universal variables)
 * - collect the uninterpreted constaints of t (treated as existential variables).
 */

#ifndef __EF_ANALYZE_H
#define __EF_ANALYZE_H

#include <stdint.h>

#include "int_queues.h"
#include "int_vectors.h"
#include "int_hash_sets.h"
#include "terms.h"


/*
 * Data structure:
 * - terms = term table where all terms are defined
 * - queue = queue to explore terms/subterms
 * - cache = set of already visited terms
 */
typedef struct ef_analyzer_s {
  term_table_t *terms;
  int_queue_t queue;
  int_hset_t cache;
} ef_analyzer_t;


/*
 * Initialize the data structure
 */
extern void init_ef_analyzer(ef_analyzer_t *ef, term_table_t *terms);


/*
 * Reset: empty cache and queue
 */
extern void reset_ef_analyzer(ef_analyzer_t *ef);


/*
 * Free all memory used
 */
extern void delete_ef_analyzer(ef_analyzer_t *ef);


/*
 * Process term t
 * - return true if t is quantifier free
 * - return false otherwise
 * - collect the variables of t in vector uvar (univeral vars)
 * - collect the uninterpreted constants of t in vector evar (existential vars)
 */
extern bool ef_analyze(ef_analyzer_t *ef, term_t t, ivector_t *uvar, ivector_t *evar);


#endif /* __EF_ANALYZE_H */
