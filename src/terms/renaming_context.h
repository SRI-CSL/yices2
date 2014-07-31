/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Variable renaming for substitutions
 *
 * The data structure combines subst_context and renaming
 * to store a mapping from variables to (fresh) variables.
 */

#ifndef __RENAMING_CONTEXT_H
#define __RENAMING_CONTEXT_H

#include <stdint.h>

#include "terms/subst_context.h"
#include "terms/variable_renaming.h"

/*
 * Structure:
 * - subst stores the mapping from variables to variables
 * - rename is used to create fresh variables
 * - hash is either NULL or the hash code of subst
 */
typedef struct renaming_ctx_s {
  subst_ctx_t subst;
  renaming_t rename;
  harray_t *hash;
} renaming_ctx_t;


/*
 * Initialization:
 * - ttbl = attached term table
 * - n = initial size of the substitution table
 *   if n=0, the default size (defined in subst_context.h) is used.
 */
extern void init_renaming_ctx(renaming_ctx_t *ctx, term_table_t *ttbl, uint32_t n);


/*
 * Deletion
 */
extern void delete_renaming_ctx(renaming_ctx_t *ctx);


/*
 * Reset: empty the ctx
 */
extern void reset_renaming_ctx(renaming_ctx_t *ctx);


/*
 * Extend the renaming:
 * - replace variables in v[0 ... n-1] by n fresh variables.
 * - the variables are processed in order from v[0] to v[n-1]
 * - v should not contain duplicates
 */
extern void renaming_ctx_push_vars(renaming_ctx_t *ctx, uint32_t n, term_t *v);


/*
 * Collect the n fresh variables introduced by the previous operation
 * into array a
 * - a must be large enough for n variables
 */
static inline void renaming_ctx_collect_new_vars(renaming_ctx_t *ctx, uint32_t n, term_t *a) {
  subst_ctx_collect_bindings(&ctx->subst, n, a);
}

/*
 * Remove the last n variable renamings
 * - n must be no more than the total number of renamings stored in ctx
 */
extern void renaming_ctx_pop_vars(renaming_ctx_t *ctx, uint32_t n);


/*
 * Get the hash code of the current renaming (cf. subst_context.h)
 * - two equivalent contexts have the same hash code
 */
extern harray_t *renaming_ctx_hash(renaming_ctx_t *ctx);


/*
 * Lookup variable x in the context:
 * - return NULL_TERM (i.e., -1) if x is not renamed
 * - return the variable mapped to x in ctx otherwise
 */
static inline term_t renaming_ctx_lookup(renaming_ctx_t *ctx, term_t x) {
  return subst_ctx_lookup(&ctx->subst, x);
}


/*
 * Check whether the context is empty
 */
static inline bool renaming_ctx_is_empty(renaming_ctx_t *ctx) {
  return subst_ctx_is_empty(&ctx->subst);
}

#endif /* __RENAMING_CONTEXT_H */
