/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TERM SUBSTITUTION
 */

/*
 * Substitution on terms:
 * - the substitution is defined by a hash map that stores
 *   a mapping from variables to terms.
 * - a cache stores the result of applying the substitution to
 *   (non-leaf) terms
 * - to deal with quantifiers: we may need to rename variables.
 *   This is supported by 'renaming_context'
 * - we also include a integer stack to allocate temporary
 *   integer arrays.
 */

#ifndef __TERM_SUBSTITUTION_H
#define __TERM_SUBSTITUTION_H

#include <stdint.h>
#include <stdbool.h>
#include <setjmp.h>

#include "terms/renaming_context.h"
#include "terms/subst_cache.h"
#include "terms/term_manager.h"
#include "utils/int_hash_map.h"
#include "utils/int_stack.h"
#include "utils/int_vectors.h"


/*
 * Structure:
 * - mngr = relevant term manager
 * - terms = relevant term table (must be mngr->terms)
 * - map = base substitution: variable --> term
 * - cache
 * - stack = array stack
 * - rctx: renaming context, allocated lazily
 * - env: jump buffer for exceptions
 */
typedef struct term_subst_s {
  term_manager_t *mngr;
  term_table_t *terms;
  int_hmap_t map;
  subst_cache_t cache;
  int_stack_t stack;
  renaming_ctx_t *rctx;
  jmp_buf env;
} term_subst_t;



/*
 * Check whether arrays v and t define a valid substitution:
 * - v and t must be arrays of n terms
 * - this returns true if forall i, v[i] is a variable or uninterpreted term,
 *   and the type of t[i] is a subtype of v[i]'s type.
 */
extern bool good_term_subst(term_table_t *terms, uint32_t n, const term_t *v, const term_t *t);


/*
 * Initialize subst to store the mapping defined by v and t
 * - mngr = attached term manager
 * - v must be an array of n variables or uninterpreted terms
 *   defined in ttbl
 * - t must be an array of n terms defined in ttbl
 * - the substitution replaces v[i] by t[i]
 *
 * Array v should not contain duplicates. If it does
 * the last occurrence of a variable x is what counts.
 * E.g., if v[i] = v[j] = x and i<j then x is replaced by t[j]
 * not by t[i].
 *
 * The type of t[i] must be a subtype of v[i]'s type.
 *
 * The jump buffer env is not initialized.
 */
extern void init_term_subst(term_subst_t *subst, term_manager_t *mngr,
                            uint32_t n, const term_t *v, const term_t *t);



/*
 * Reset the substitution
 * - empty the cache
 * - clears the mapping (subst->map)
 */
extern void reset_term_subst(term_subst_t *subst);


/*
 * Extend subst:
 * - add more mappings: v[i] to t[i]
 * - the new mapping must not conflict with the current mapping in subst
 *   (i.e., v[i] must not be mapped to anything in subst->map)
 * - all v[i] must be distinct
 * - the type of t[i] must be a subtype of v[i]'s type
 * - if the reset flag is true, also resets the cache.
 */
extern void extend_term_subst(term_subst_t *subst, uint32_t n, const term_t *v, const term_t *t, bool reset);


/*
 * Variant: add a single mapping: v to t
 */
static inline void extend_term_subst1(term_subst_t *subst, term_t v, term_t t, bool reset) {
  extend_term_subst(subst, 1, &v, &t, reset);
}


/*
 * Check whether v is in the domain of the substitution
 * - v must be a variable or uninterpreted term
 */
extern bool term_subst_var_in_domain(term_subst_t *susbt, term_t v);


/*
 * Get what's mapped to v in the current substitution
 * - v must be a variable or uninterpreted term
 * - return NULL_TERM if v is in the domain of subst->map
 * - return subst->map[v] otherwise
 */
extern term_t term_subst_var_mapping(term_subst_t *subst, term_t v);


/*
 * Get the domain of the substitution:
 * - every variable or uninterpreted that's in subst->map is added to vector d
 * - d is reset first
 */
extern void term_subst_domain(term_subst_t *subst, ivector_t *d);


/*
 * Apply the substitution to term t
 * - t must be a valid term in the subst's term manager
 * - return the resulting term
 * - return -1 (NULL_TERM) if the result can't be constructed
 *   (because of a degree overflow).
 * - return -2 if something else goes wrong (symptom of a bug somewhere)
 *
 * IMPORTANT:
 * ---------
 * It's possible to call apply_term_subst on several terms
 *  t_1 .... t_n provided none of these terms contain any fresh
 * variables introduced by the substitution.
 *
 * For example: this sequence is not recommended
 *   t1 = apply_term_subst(subst, t0);
 *   t2 = apply_term_susbt(subst, t1);
 * because t1 may contain fresh variables introduced by apply_subst.
 */
extern term_t apply_term_subst(term_subst_t *subst, term_t t);


/*
 * Delete the structure: free all memory used
 */
extern void delete_term_subst(term_subst_t *subst);


/*
 * Apply beta-reduction to t (only at the top-level).
 * - if t is not of the from (apply (lambda (x_1 ... x_n) u) t_1 ... t_n) then
 *   it's returned unchanged
 * - otherwise, apply the substitution [x_1 := t_1, ... x_n := t_n] to u and return
 *   the result
 *
 * Possible error codes are the same as in apply_term_subst:
 * - return -1 (NULL_TERM) if the substitution causes a degree overflow
 * - return -2 if an exception is raised (bug somewhere)
 */
extern term_t beta_reduce(term_manager_t *mngr, term_t t);



#endif /* __TERM_SUBSTITUTION_H */
