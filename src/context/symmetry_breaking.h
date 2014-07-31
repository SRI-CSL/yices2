/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SUPPORT FOR BREAKING SYMMETRIES IN UF FORMULAS
 */

#ifndef __SYMMETRY_BREAKING_H
#define __SYMMETRY_BREAKING_H

#include <stdint.h>
#include <setjmp.h>

#include "utils/int_vectors.h"
#include "utils/int_queues.h"
#include "utils/int_hash_sets.h"
#include "utils/int_stack.h"
#include "utils/csets.h"
#include "terms/term_manager.h"

#include "context/context.h"



/*
 * RANGE CONSTRAINTS
 */

/*
 * An assertion f is a range constraint if it's equivalent to
 * a formula of the form (or (= t c_1) .... (= t c_n))
 * where c_1 ... c_n are distinct uninterpreted constants
 * and t is a term.
 *
 * We collect such assertions into an array of range-constraint records:
 * - each record stores the terms [c1 ... c_n]
 *   + a set of terms t_1 .... t_m  and a set of indices i_1 .... i_m
 * - for each index i_j in { i_1 ,.... i_m }, the
 *   assertion ctx->top_formula[i_j] is a range constraint
 *   equivalent to (or (= t_j c1) .... (= t_j c_n))
 * - every c_i and every t_j is a root term in ctx->intern
 *
 * We want to be able to check inclusion between sets of constants in
 * different constraints. To accelerate this, we store a 32bit hash
 * used as a bit map:
 * - bit i of hash is 1 if there's a constant c_j such that (c_j mod 32) = i
 */

/*
 * Range-constraint record:
 * - cst[0 ... nc - 1] = the constants
 * - trm[0 ... nt - 1] = the terms
 *   idx[0 ... nt - 1] = the corresponding indices
 * - num_constants = nc number of constants
 * - hash = bit map
 * - num_terms = nt = number of terms
 *   size = size of arrays trm and idx
 * The constants in cst are sorted (in increasing order).
 */
typedef struct rng_record_s {
  term_t *cst;
  term_t *trm;
  uint32_t *idx;
  uint32_t num_constants;
  uint32_t hash;
  uint32_t num_terms;
  uint32_t size;
} rng_record_t;

#define DEF_RNG_RECORD_SIZE 20
#define MAX_RNG_RECORD_SIZE (UINT32_MAX/sizeof(term_t))


/*
 * Array/vector of these records
 */
typedef struct rng_vector_s {
  rng_record_t *data;
  uint32_t nelems;
  uint32_t size;
}  rng_vector_t;

#define DEF_RNG_VECTOR_SIZE 2
#define MAX_RNG_VECTOR_SIZE (UINT32_MAX/sizeof(rng_record_t))



/*
 * SUBSTITUTION
 */

/*
 * To check whether a set of assertions is invariant by permutations
 * of a set of constants {c_0. ,,, c_n}, we check invariance for
 * - the permutation that swaps c_0 and c_1
 * - the cicular permuation c_0 := c_1, ...., c_n := c_0
 *
 * We need to apply such substitutions in the assertion context (i,e.,
 * by taking into account the internalization table). We use the following
 * data structure to store a substitution and its results.
 * - array subst[t] = result of applying the substitution to term index t
 *    or -1 if it's not computed yet.
 * - nterms = initialization bound: for any t in 0 ... nterms, subst[t] is
 *   defined or initialized (i.e, NULL_TERM)
 * - size = full size of the array.
 * Subst is a mapping from term indices to terms
 *
 * Auxiliary data structures:
 * - mngr = term manager for term construction/simplification
 * - stack for allocation of integer arrays (in recursive calls)
 * - env = jmp buffer to exception handling
 */
typedef struct ctx_subst_s {
  intern_tbl_t *intern;
  term_table_t *terms;
  term_t *subst;
  uint32_t nterms;
  uint32_t size;
  term_manager_t mngr;
  int_stack_t stack;
  jmp_buf env;
} ctx_subst_t;

#define DEF_CTX_SUBST_SIZE 100
#define MAX_CTX_SUBST_SIZE (UINT32_MAX/sizeof(term_t))


/*
 * Arrays used during symmetry breaking
 *
 * Given a fixed set of constants C0 (obtained from a rng_record_t),
 * we keep three subsets of C0:
 * - available = constants that don't occur in any symmetry breaking clause
 * - used = complement of available = set of constants already used
 * - removed = auxiliary set: this is a subset of available that's added
 *             to used at every iteration
 *
 * We use the following data structures:
 * - constants = fixed array of constants
 * - num_constants = size of this array
 * - available = set of indices in [0 ... num_constants - 1] (as a cset)
 * - removed = set of indices in [0 ... num_constants - 1] (as a cset too)
 * - used = array of constants
 * - num_used = number of elements in this array
 *
 * Initially:
 * - available := full set
 * - removed := empty set
 * - used := empty array
 *
 * At each iteration: we select a term t and generate a symmetry breaking
 * clause for t. The sets are updated as follows:
 * - removed := available \inter constants of t
 *         a := a constant of available that's not in removed
 * - used := used \union removed
 * - available := available \minus removed
 *
 * Set of candidates:
 * - we store the set of candidate terms in an array candidates
 * - num_candidates = number of elements in this array
 * - for each i in [0 ... num_candidates - 1], we keep
 *    cost[i] = cost of candidates[i]
 *    hash[i] = hash code for accelerating processing of candidates[i]
 *
 * - cost[i] is the size of the set of constants of candidates[i]
 *   that also occur in 'available'. If term t = candidates[i] is
 *   selected then we'll remove cost[i]+1 constants from 'available' and
 *   move them to 'used'.
 *
 * - hash[i] is a 32bit hash of the set of constants occurring in
 *   candidates[i] and in 'available'. In each iteration, we check
 *   whether (hash[i] & removed->hash) is 0. If so, cost[i] and hash[i]
 *   don't change.
 */
typedef struct sym_breaker_sets_s {
  // fixed part
  term_t *constants;
  uint32_t num_constants;

  // subsets
  cset_t available;
  cset_t removed;
  term_t *used;
  uint32_t num_used;
  uint32_t used_size;

  // candidate set + scores
  term_t *candidates;
  uint32_t *cost;
  uint32_t *hash;
  uint32_t num_candidates;
  uint32_t candidate_size;

  // auxilairy vector to compute constants of a term
  ivector_t aux;
} sym_breaker_sets_t;


#define MAX_SBREAK_SET_SIZE (UINT32_MAX/sizeof(term_t))


/*
 * Symmetry breaker
 * - pointers to the relevant context + term table
 * - vector of range constraint descriptors
 * - substitution
 * - auxiliary structures to explore terms
 */
typedef struct sym_breaker_s {
  context_t *ctx;
  term_table_t *terms;

  // vector of range_constraints
  rng_vector_t range_constraints;

  // array for sorting and removing subsumed constraints
  rng_record_t **sorted_constraints;
  uint32_t num_constraints; // size of this array

  // sets used for symmetry breaking
  sym_breaker_sets_t sets;

  // auxiliary structures
  int_queue_t queue;
  int_hset_t cache;
  ivector_t aux;
} sym_breaker_t;




/*
 * OPERATIONS
 */

/*
 * Initialize sym_breaker
 * - ctx = relevant context
 */
extern void init_sym_breaker(sym_breaker_t *breaker, context_t *ctx);


/*
 * Delete it: free all memory it uses
 */
extern void delete_sym_breaker(sym_breaker_t *breaker);


/*
 * Collect all domain constraints from ctx->top_formulas
 * - all constraints found are added the range_constraint record
 */
extern void collect_range_constraints(sym_breaker_t *breaker);


/*
 * Check whether the assertions are invariant by permutation of
 * constants in record r.
 */
extern bool check_assertion_invariance(sym_breaker_t *breaker, rng_record_t *r);


/*
 * Check whether r1's constant set is included (strictly) in r2's constant set
 */
extern bool range_record_subset(rng_record_t *r1, rng_record_t *r2);


/*
 * Copy r into set structure s
 * - constants of r are stored in s->cst
 * - s->used_cst is reset
 * - terms of r are stored in s->candidates
 */
extern void breaker_sets_copy_record(sym_breaker_sets_t *s, rng_record_t *r);


/*
 * Add candidates of r into s
 * - this should be done only if r->cst is a subset of s->cst
 */
extern void breaker_sets_add_record(sym_breaker_sets_t *s, rng_record_t *r);


/*
 * Break symmetries using s
 */
extern void break_symmetries(sym_breaker_t *breaker, sym_breaker_sets_t *s);




#endif /* __SYMMETTY_BREAKING_H */
