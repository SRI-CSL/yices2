/*
 * TERM SUBSTITUTION
 */

/*
 * Subsitution on terms:
 * - the substitution is defined by a hash map that stores
 *   a mapping from variables to terms.
 * - a cache stores the result of applying the substitution to
 *   (non-leaf) terms
 * - to deal with quantifiers: we may need to rename variables.
 *   This is supported by 'renaming_context'
 *   We also use an auxiliary data structure to detect ground terms.
 */

#ifndef __TERM_SUBSTITUTION_H
#define __TERM_SUBSTITUTION_H

#include <stdint.h>
#include <stdbool.h>

#include "int_hash_map.h"
#include "subst_cache.h"
#include "renaming_context.h"
#include "free_var_collector.h"

/*
 * Structure:
 * - terms = relevant term table
 * - map = base substitution: variable --> term 
 * - cache
 * - rctx: renaming context, is allocated lazily
 * - fvar: free-variable collector, allocated lazily too
 */
typedef struct term_subst_s {
  term_table_t *terms;
  int_hmap_t map;
  subst_cache_t cache;
  renaming_ctx_t *rctx;
  fvar_collector_t *fvar;
} term_subst_t;


/*
 * Initialize for mapping defined by v and t
 * - ttbl = attached term table
 * - v must be an array of n variables defined in ttbl
 * - t must be an array of n terms defined in ttbl
 * - the substitution replaces v[i] by t[i]
 *
 * Array v should not contain duplicates. If it does
 * the last occurrence of a variable x is what counts.
 * E.g., if v[i] = v[j] = x and i<j then x is replaced by t[j]
 * not by t[i].
 *
 * The type of t[i] must be a subtype of v[i]'s type.
 */
extern void init_term_subst(term_subst_t *subst, term_table_t *ttbl,
			    uint32_t n, term_t *v, term_t *t);


/*
 * Delete the structure: free all memory used
 */
extern void delete_term_subst(term_subst_t *subst);


/*
 * Lookup the term mapped to x (taking renaming into account)
 * - x must be a variable
 * - if there's a renaming, lookup x in the renaming context
 * - if x is not renamed, lookup x in the map
 * - if x is not renamed and not in the map, then return x
 */
extern term_t get_subst_of_var(term_subst_t *subst, term_t x);


/*
 * Check whether the result of subst(t) is stored in the cache
 * - t must be a valid term in subst->terms
 * - this takes the renaming context into account
 * - return NULL_TERM (-1) is the result is not in the cache
 */
extern term_t get_cached_subst(term_subst_t *subst, term_t t);


/*
 * Add u as subst(t) in the cache
 * - t and u must be valid terms in subst->terms
 * - there must not be an existing value for t in the cache
 * - this takes the renaming context into account (cf. subst_cache.h)
 */
extern void cache_subst_result(term_subst_t *subst, term_t t, term_t u);


/*
 * Extend the current renaming context: by renamings for v[0 .. n-1]
 * (cf. renaming_context.h)
 * - v[0] ... v[n-1] must all be variables in subst->terms
 * - this allocates and initializes the renaming data structure if needed
 */
extern void subst_push_renaming(term_subst_t *subst, uint32_t n, term_t *v);


/*
 * Remove the last n variable renaming (cf. renaming_context.h)
 * - the current renaming must exist and have at least n variables
 */
extern void subst_pop_renaming(term_subst_t *subst, uint32_t n);


/*
 * Check whether term t is ground
 * - t must be a valid term in subst->terms
 * - allocate and initialize the variable collector structure if needed
 */
extern bool subst_term_is_ground(term_subst_t *subst, term_t t);



#endif /* __TERM_SUBSTITUTION_H */
