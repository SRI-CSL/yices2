/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Substitution context: stored as a mapping from int32_t indices
 * (variable indices) to int32_t indices (term indices). These
 * indices are assumed non-negative,
 *
 * This provides a scoping mechanism: a lookup operation for x returns
 * the most recent value mapped to x. Adding a new binding for x masks
 * the previous binding. Bindings are removed in a FIFO manner and
 * removing the current binding of x restores the previous one.
 *
 * The mapping is stored as an array. Each lookup operation
 * requires linear time, so this should not be used to
 * store large mappings.
 */

#ifndef __SUBST_CONTEXT_H
#define __SUBST_CONTEXT_H

#include <assert.h>
#include <stdint.h>
#include <stdbool.h>

#include "utils/int_vectors.h"
#include "utils/int_array_hsets.h"
#include "utils/int_bv_sets.h"


/*
 * Binding elements: pairs variable, term
 */
typedef struct ctx_binding_s {
  int32_t var;
  int32_t term;
} ctx_binding_t;


/*
 * Substitution context:
 * - array of bindings
 * - an optional hash-set for converting bindings to a hash-consed array.
 * - auxiliary buffer and bit array
 *   This set is used to build a normal form (two equivalent contexts
 *   are represented as the same array).
 */
typedef struct subst_ctx_s {
  ctx_binding_t *data;   // array of bindings
  uint32_t size;         // size of array data
  uint32_t nelems;       // actual number of bindings stored in data

  ivector_t buffer;      // to convert the context to an array
  int_bvset_t *vset;     // set of variables in the context

  int_array_hset_t *hset;
} subst_ctx_t;


#define DEF_SUBST_CTX_SIZE 50
#define MAX_SUBST_CTX_SIZE (UINT32_MAX/sizeof(ctx_binding_t))


/*
 * Initialize a substitution context
 * - n = initial size. If n=0 the default size is used.
 */
extern void init_subst_ctx(subst_ctx_t *ctx, uint32_t n);


/*
 * Delete
 */
extern void delete_subst_ctx(subst_ctx_t *ctx);


/*
 * Empty: remove all bindings
 * - if reset_hset is true, then ctx->hset is emptied too
 *   otherwise, ctx->hset is not changed.
 */
extern void reset_subst_ctx(subst_ctx_t *ctx, bool reset_hset);


/*
 * Add binding [x --> t] to the context
 * - this masks any previous binding of x
 * - x and t must be non-negative
 */
extern void subst_ctx_push_binding(subst_ctx_t *ctx, int32_t x, int32_t t);


/*
 * Remove the last n bindings from the context
 * - n must be at least ctx->nelems
 */
static inline void subst_ctx_pop_bindings(subst_ctx_t *ctx, uint32_t n) {
  assert(n <= ctx->nelems);
  ctx->nelems -= n;
}


/*
 * Collect the values of the last n bindings in array a
 * - n must be at least ctx->nelems
 * - a must be large enough to store n integers
 * - if the last n bindings were [x_1 --> t1, ... x_n --> t_n]
 *   in that order, then this function stores t_1 ... t_n in a[0 ... n-1]
 */
extern void subst_ctx_collect_bindings(subst_ctx_t *ctx, uint32_t n, int32_t *a);


/*
 * Check whether the context is empty
 */
static inline bool subst_ctx_is_empty(subst_ctx_t *ctx) {
  return ctx->nelems == 0;
}


/*
 * Get the term bound to x in the context
 * - x must be non-negative
 * - return -1 if x is not bound
 */
extern int32_t subst_ctx_lookup(subst_ctx_t *ctx, int32_t x);


/*
 * Hash consing: stores the current context (ignoring the
 * masked bindings) into an integer array, then return a copy
 * of this array (using hash-consing).
 * - the array is constructed by storing the bindings as
 *   pairs [variable, term], sorted in order of
 *   increasing variable index.
 * - two equivalent contexts then have the same representation
 *
 * The result is a pointer to a harray structure d
 *   d->nelems = 2 * number of bindings
 *   d->data[2 * i] = variable for the i-th binding
 *   d->data[2 * i + 1] = term for the i-th binding
 */
extern harray_t *subst_ctx_hash(subst_ctx_t *ctx);


#endif /* __SUBST_CONTEXT_H */
