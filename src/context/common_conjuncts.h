/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * COMMON CONJUNCTS IN A SET OF FORMULAS
 *
 * Given n formulas f[0] ... f[n-1], where each f[i] is seen as
 * conjunction of formuals. This module computes the sub-formulas that
 * are common to all f[i].
 *
 * This is useful to rewrite assertions like
 *   (OR (AND A B_1) (AND A B_2) ... (AND A B_n))
 * to
 *   (AND A (OR B_1 B_2 ... B_n))
 */

#ifndef __COMMON_CONJUNCTS_H
#define __COMMON_CONJUNCTS_H 

#include <stdint.h>

#include "terms/terms.h"
#include "utils/int_vectors.h"
#include "utils/int_queues.h"
#include "utils/int_hash_sets.h"


/*
 * Data structure to collect conjuncts in a formula
 * - queue for breadth-first exploration
 * - hash_set to mark the formulas already seen
 * - two auxiliary vectors to store intermediate results
 */
typedef struct bfs_explorer_s {
  term_table_t *terms;
  int_queue_t queue;
  int_hset_t hset;
  ivector_t aux1;
  ivector_t aux2;
} bfs_explorer_t;


/*
 * Initialization: use default sizes for queue, hset, and aux vector
 */
extern void init_bfs_explorer(bfs_explorer_t *explorer, term_table_t *terms);


/*
 * Reset: empty queue and hset
 */
extern void reset_bfs_explorer(bfs_explorer_t *explorer);


/*
 * Delete: free memory
 */
extern void delete_bfs_explorer(bfs_explorer_t *explorer);


/*
 * Compute the conjuncts of formula f
 * - the conjuncts are stored in vector v
 * - v is reset first
 */ 
extern void bfs_get_conjuncts(bfs_explorer_t *explorer, term_t f, ivector_t *v);


/*
 * Compute the disjuncts of formula f
 * - store them in vector v
 */
extern void bfs_get_disjuncts(bfs_explorer_t *explorer, term_t f, ivector_t *v);


/*
 * Compute the common conjuncts of formulas f[0 ... n-1]
 * - n must be positive
 * - store the common conjuncts in vector v (sorted)
 * - v is reset first
 */
extern void bfs_get_common_conjuncts(bfs_explorer_t *explorer, term_t *f, uint32_t n, ivector_t *v);


/*
 * Common factors of a disjunction.
 * 
 * If f is of the form (or a[0] ... a[n-1]), this function collects all
 * the subformulas that are common conjuncts of a[0] ... a[n-1].
 * So we have a[i] = (and (common-factors b[i]))
 *    and f is equivalent to (and common-factors (or b[0] ... b[n-1])))
 *
 * If f is not of the form (or ...), then the unique common factor is f itself.
 * This function stores f in v in this case.
 */
extern void bfs_factor_disjunction(bfs_explorer_t *explorer, term_t f, ivector_t *v);


#endif /* __COMMON_CONJUNCTS_H */
