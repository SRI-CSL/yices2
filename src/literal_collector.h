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

#ifndef __LITERAL_COLLECTOR_H
#define __LITERAL_COLLECTOR_H

#include <stdint.h>
#include <setjmp.h>

#include "int_stack.h"
#include "int_hash_sets.h"
#include "int_hash_map.h"
#include "model_eval.h"
#include "term_manager.h"


/*
 * Collector structure:
 * - model = the relevant model
 * - evaluator = initialized for the model
 * - manager = for creating the simplified terms (if any)
 * - cache = keeps the simplified form of all visited terms
 * - lit_set = set of literals
 * - stack for recursive processing of terms
 * - env = jump buffer for exceptions
 */
typedef struct lit_collector_s {
  model_t *model;
  evaluator_t eval;
  term_manager_t manager;
  int_hmap_t cache;
  int_hset_t lit_set;
  int_stack_t stack;
  jmp_buf env;
} lit_collector_t;



/*
 * Initialization for model mdl
 */
extern void init_lit_collector(lit_collector_t *collect, model_t *mdl);


/*
 * Delete: free all memory
 */
extern void delete_lit_collector(lit_collector_t *collect);


/*
 * Reset: empty the lit_set and the cache
 */
extern void reset_lit_collector(lit_collector_t *collect);


/*
 * Process term t:
 * - return a negative error code if something goes wrong
 * - return the simplified form of t otherwise
 * - collect literals in collect->lit_set (the current literals are kept
 *   and more may be added)
 */
extern term_t lit_collector_process(lit_collector_t *collect, term_t t);



#endif /* __LITERAL_COLLECTOR_H */
