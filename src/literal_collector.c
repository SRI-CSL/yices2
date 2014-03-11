/*
 * SUPPORT FOR COMPUTING IMPLICANTS
 */

/*
 * Given a model M and a formula f such that M satisfies f, we want to
 * compute an implicant for f. The implicant is a set/conjunction of
 * literals p_1 .... p_n such that:
 *  1) every p_i is true in M
 *  2) p_1 /\ p_2 /\ ... /\ p_n => f (is valid)
 *
 * To deal with if-then-else, we generalize the problem as follows:
 * - given a model M and a term t, collect a set of literals
 *   p_1 .... p_n and a term u such that
 *   1) every p_i is true in M
 *   2) p_1 /\ p_2 /\ ... /\ p_n => (t == u)
 * - informally, u is the result of simplifying t modulo p_1 ... p_n
 * - example:
 *   processing  2 + (ite (< x y) x y) may return
 *    literal: (< x y)
 *    simplified term: 2 + x
 *    if (< x y) is true in M
 *
 * Then to get the implicant for a formula f, we process f, the simplified
 * term should be true and the set of literals collected imply f.
 *
 */

#include "literal_collector.h"

/*
 * Initialization: prepare collector for model mdl
 * - collect->env is not touched.
 */
void init_lit_collector(lit_collector_t *collect, model_t *mdl) {
  collect->model = mdl;
  init_evaluator(&collect->eval, mdl);
  init_term_manager(&collect->manager, mdl->terms);
  init_int_hmap(&collect->cache, 0);
  init_int_hset(&collect->lit_set, 0);
  init_istack(&collect->stack);
}


/*
 * Delete everything
 */
void delete_lit_collector(lit_collector_t *collect) {
  delete_evaluator(&collect->eval);
  delete_term_manager(&collect->manager);
  delete_int_hmap(&collect->cache);
  delete_int_hset(&collect->lit_set);
  delete_istack(&collect->stack);
}


/*
 * Reset: empty the lit_set and the cache
 */
void reset_lit_collector(lit_collector_t *collect) {
  int_hmap_reset(&collect->cache);
  int_hset_reset(&collect->lit_set);
  reset_istack(&collect->stack);
}

