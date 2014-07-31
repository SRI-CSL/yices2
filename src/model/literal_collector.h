/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

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
 *   3) u is atomic:
 *      if t is Boolean, u is either true_term or false_term
 *      otherwise u a term with no if-then-else subterms
 *      (e.g., u is an arithmetic term with no if-then-elses).
 *
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
 *
 * Options
 * -------
 * Several options control the type of atoms/literals produced:
 *
 * - ELIM_ARITH_NEQ0: eliminate arithmetic disequalities.
 *   If atom (= t 0) is false in the model, then we normally add its
 *   negation (not (t = 0)) to the set of literals.
 *   is replaced by either (< t 0) or (> t 0), whichever is true in the model.
 *
 * - ELIM_ARITH_NEQ: eliminate binary arithmetic disequalities.
 *   If atom (= t1 t2) is false, then rewrite it to either (< t1 t2) or (> t1 t2)
 *
 * - ELIM_ARITH_DISTINCT: generalize ELIM_ARITH_NEQ to distinct
 *   If (distinct t1 t2 .... t_n) is true, then order the t_i's in increasing
 *   order (based on their value in the model) and generate
 *    (< t1 t2) (< t2 t3) ... (< t_{n-1} t_n)
 *
 * - ELIM_NOT_DISTINCT: if (distinct t_1 ... t_n) is false, then search for
 *   t_i and t_j that are equal in the model and generate (eq t_i t_j)
 *
 * - KEEP_BOOL_EQ: treat (eq t1 t2) as an atom if t1 or t2 is a
 *   Boolean variable. By default, Boolean equalities are treated as iff:
 *    (eq t1 t2) is interpreted as (or (and t1 t2) (and (not t1) (not t2)))
 *
 * Mode
 * ----
 * The mode determines how Boolean terms are treated.
 *
 * By default, all Boolean terms are treated as formulas and are
 * reduced to true or false. In some cases, it may make more sense to
 * treat a Boolean terms as a term.
 *
 * Examples:
 * - if KEEP_BOOL_EQ is active, then we want to treat t as a term in (= x t).
 *   (rather than reducing t to true or false then tread (= x t) as either
 *    (= x true) or (= x false)).
 * - if an uninterpreted function is applied to Booleans as in (P t1 t2)
 *   then it's probably more useful to keep t1 and t2 as terms rather than
 *   constructing (P true false) say.
 * - on the other hand, we always want to reduce (ite c a b) so we treat
 *   c as a formula in this context (i.e., we reduce it to true/false).
 */

#ifndef __LITERAL_COLLECTOR_H
#define __LITERAL_COLLECTOR_H

#include <stdint.h>
#include <setjmp.h>
#include <assert.h>

#include "utils/int_stack.h"
#include "utils/int_hash_sets.h"
#include "utils/int_hash_map.h"
#include "model/model_eval.h"
#include "terms/term_manager.h"
#include "utils/int_vectors.h"


/*
 * Error codes returned by lit_collector_process:
 * - any error code defined in model_eval.h can be returned
 *   (i.e., from -2 to -7)
 * - additional code for get_implicant: return -8 if an
 *   input formual is false in the model
 */
enum {
  MDL_EVAL_FORMULA_FALSE = -8,
};


/*
 * Option codes: each option sets a bit in a 32bit option word
 */
#define ELIM_ARITH_NEQ0     ((uint32_t) 0x1)
#define ELIM_ARITH_NEQ      ((uint32_t) 0x2)
#define ELIM_ARITH_DISTINCT ((uint32_t) 0x4)
#define ELIM_NOT_DISTINCT   ((uint32_t) 0x8)
#define KEEP_BOOL_EQ        ((uint32_t) 0x10)

/*
 * Mask: five low-order bits
 */
#define LIT_COLLECTOR_OPTION_MASK  ((uint32_t) 0x1F)

/*
 * Default: all options are disabled
 */
#define LIT_COLLECTOR_DEFAULT_OPTIONS ((uint32_t) 0)


/*
 * Collector structure:
 * - terms = the relevant term table
 * - model = the relevant model
 * - evaluator = initialized for the model
 * - manager = for creating the simplified terms (if any)
 * - tcache = simplified form of all visited terms
 * - fcache = simplified form of all visited formulas
 * - lit_set = set of literals
 * - stack for recursive processing of terms
 * - options = option word
 * - bool_are_terms = the mode (true means: treat Booleans like ordinary terms)
 * - env = jump buffer for exceptions
 *
 * NOTE: a Boolean term may be visited twice: once as a term and once as
 * a formula. To deal with this, we use two different caches:
 * - tcache is the default cache: it's used for all non-Boolean terms
 * - tcache is also used for a Boolean term t (when bool_are_terms is true)
 * - fcache is used for Boolean terms when bool_are_terms is false.
 */
typedef struct lit_collector_s {
  term_table_t *terms;
  model_t *model;
  evaluator_t eval;
  term_manager_t manager;
  int_hmap_t tcache;
  int_hmap_t fcache;
  int_hset_t lit_set;
  int_stack_t stack;
  uint32_t options;
  bool bool_are_terms;
  jmp_buf env;
} lit_collector_t;



/*
 * Initialization for model mdl + default options
 */
extern void init_lit_collector(lit_collector_t *collect, model_t *mdl);


/*
 * Delete: free all memory
 */
extern void delete_lit_collector(lit_collector_t *collect);


/*
 * Reset: empty the lit_set and the caches
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



/*
 * Set/clear options (must be done before calling lit_collector_process)
 */
static inline void lit_collector_set_option(lit_collector_t *collect, uint32_t opt) {
  assert((opt & ~LIT_COLLECTOR_OPTION_MASK) == 0);
  collect->options |= opt;
}

static inline void lit_collector_clear_option(lit_collector_t *collect, uint32_t opt) {
  assert((opt & ~LIT_COLLECTOR_OPTION_MASK) == 0);
  collect->options &= ~opt;
}

/*
 * Check which option(s) are enabled
 */
static inline bool lit_collector_option_enabled(lit_collector_t *collect, uint32_t opt) {
  return (collect->options & opt) != 0;
}


/*
 * Get all the literals in collect->lit_set: store them in vector_v
 * - this modifies the collect->lit_set data structure
 * - lit_collector_process should not be called after this (unless
 *   reset_lit_collector is called first).
 */
extern void lit_collector_get_literals(lit_collector_t *collect, ivector_t *v);



/*
 * Given a model mdl and a set of formulas a[0 ... n-1] satisfied by mdl,
 * compute an implicant for a[0] /\ a[1] /\ ... /\ a[n-2].
 * - all terms in a must be Boolean and all of them must be true in mdl
 * - if there's a error, the function returns a negative code
 *   and leaves v unchanged
 * - otherwise, the function retuns 0 and add the literals forming the
 *   implicant to vector v  (v is not reset).
 *
 * - options = bit mask to enable/disable the optional processing.
 */
extern int32_t get_implicant(model_t *mdl, uint32_t options, uint32_t n, const term_t *a, ivector_t *v);



#endif /* __LITERAL_COLLECTOR_H */
