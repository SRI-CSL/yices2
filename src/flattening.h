/*
 * Flattening of formulas
 * ----------------------
 *
 * Given a formula f, we can convert it to conjuncts or disjuncts:
 *
 * Flattening to conjuncts: return n formulas c_1 ... c_n such that
 *   f == (and c_1 ... c_n)
 *
 * Flattening to disjuncts: return n formulas d_1 ... d_n such that
 *   f == (or d_1 ... d_n)
 *
 * Optional flattening
 * -------------------
 *  (ite C A B) can be flattened to (and (or (not C) A) (or C B))
 *                           or  to (or (and C A) (and (not C) B))
 * 
 *  (iff A B) can be flattened to (and (or (not A) B) (or A (not B)))
 *                          or to (or  (and A B) (and (not A) (not B)))
 *
 */

#ifndef __FLATTENING_H
#define __FLATTENING_H

#include <stdint.h>
#include <stdbool.h>

#include "int_queues.h"
#include "int_vectors.h"
#include "int_hash_sets.h"
#include "term_manager.h"

/*
 * Data structure for flattening:
 * - terms = term table where all terms reside
 * - manager = term manager
 * - queue = terms to visit (BFS)
 * - cache = terms already visited
 * - resu = vector of conjuntcs or disjuncts
 */
typedef struct flattener_s {
  term_table_t *terms;
  term_manager_t *manager;
  int_queue_t queue;
  int_hset_t cache;
  ivector_t resu;
} flattener_t;


/*
 * Initialization:
 * - mngr = the relevant term manager
 */
extern void init_flattener(flattener_t *flat, term_manager_t *mngr);

/*
 * Reset: empty all internal structures.
 * keep manager and terms
 */
extern void reset_flattener(flattener_t *flat);

/*
 * Delete all
 */
extern void delete_flattener(flattener_t *flat);


/*
 * Flatten formula f to conjuncts
 * - f must be defined in flat->terms
 * - flags f_ite and f_iff control optional flattening:
 *
 *   if f_ite is true, then (ite C A B) is converted to 
 *       (and (=> C A)(=> (not C) B))
 *   (otherwise, (ite C A B) is kept as is)
 *
 *   if f_iff is true, then (iff A B) is converted to
 *       (and (=> A B)(=> B A))
 *   (otherwise, (iff A B) is kept)
 *
 * - if f is not a Boolean term, the result is f itself
 *
 * - the result is stored in flat->resu:
 *   flat->resu.size = number of conjuncts
 *   flat->resu.data = array of conjuncts
 */
extern void flatten_to_conjuncts(flattener_t *flat, term_t f, bool f_ite, bool f_iff);


/*
 * Flatten formula f to disjuncts
 *
 * if f_ite is true, then (ite C A B) is converted to
 *     (or (and C A) (and (not C) B))
 *
 * if f_iff true, then (iff A B) is converted to
 *     (or (and A B) (and (not A) (not B)))
 *
 * the result is stored in flat->resu
 */
extern void flatten_to_disjuncts(flattener_t *flat, term_t f, bool f_ite, bool f_iff);


/*
 * Flatten array f[0 ... n-1]:
 * - this builds an array of conjuncts equivalent to (and f[0] ... f[n-1])
 */
extern void flatten_array_to_conjuncts(flattener_t *flat, uint32_t n, term_t *f, bool f_ite, bool f_iff);


/*
 * Flatten array f[0 ... n-1]:
 * - this builds an array of disjuncts equivalent to (or  f[0] ... f[n-1])
 */
extern void flatten_array_to_disjuncts(flattener_t *flat, uint32_t n, term_t *f, bool f_ite, bool f_iff);



#endif /* __FLATTENING_H */
