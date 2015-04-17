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
 */

#include "terms/subst_context.h"
#include "utils/memalloc.h"
#include "utils/prng.h"


/*
 * Initialize a substitution context
 * - n = initial size. If n=0 the default size is used.
 */
void init_subst_ctx(subst_ctx_t *ctx, uint32_t n) {
  if (n == 0) {
    n = DEF_SUBST_CTX_SIZE;
  }

  if (n > MAX_SUBST_CTX_SIZE) {
    out_of_memory();
  }

  ctx->data = (ctx_binding_t *) safe_malloc(n * sizeof(ctx_binding_t));
  ctx->size = n;
  ctx->nelems = 0;

  init_ivector(&ctx->buffer, 0);
  ctx->vset = NULL;
  ctx->hset = NULL;
}


/*
 * Get the internal hset.
 * - allocate and initialize it if needed
 */
static int_array_hset_t *subst_ctx_get_hset(subst_ctx_t *ctx) {
  int_array_hset_t *hset;

  hset = ctx->hset;
  if (hset == NULL) {
    hset = (int_array_hset_t *) safe_malloc(sizeof(int_array_hset_t));
    init_int_array_hset(hset, 0); // default size
    ctx->hset = hset;
  }

  return hset;
}


/*
 * Get the internal set of variables
 * - allocate and initialize it if needed
 */
static int_bvset_t *subst_ctx_get_vset(subst_ctx_t *ctx) {
  int_bvset_t *vset;

  vset = ctx->vset;
  if (vset == NULL) {
    vset = (int_bvset_t *) safe_malloc(sizeof(int_bvset_t));
    init_int_bvset(vset, 0); // use default size
    ctx->vset = vset;
  }

  return vset;
}


/*
 * Make the data array 50% larger
 */
static void extend_subst_ctx(subst_ctx_t *ctx) {
  uint32_t n;

  n = ctx->size + 1;
  n += n >> 1;
  if (n > MAX_SUBST_CTX_SIZE) {
    out_of_memory();
  }

  ctx->data = (ctx_binding_t *) safe_realloc(ctx->data, n * sizeof(ctx_binding_t));
  ctx->size = n;
}


/*
 * Delete
 */
void delete_subst_ctx(subst_ctx_t *ctx) {
  safe_free(ctx->data);
  ctx->data = NULL;
  delete_ivector(&ctx->buffer);

  if (ctx->hset != NULL) {
    delete_int_array_hset(ctx->hset);
    safe_free(ctx->hset);
    ctx->hset = NULL;
  }

  if (ctx->vset != NULL) {
    delete_int_bvset(ctx->vset);
    safe_free(ctx->vset);
    ctx->vset = NULL;
  }
}



/*
 * Empty: remove all bindings
 * - if empty_hset is true, then ctx->hset is emptied too
 *   otherwise, ctx->hset is not changed.
 */
void reset_subst_ctx(subst_ctx_t *ctx, bool empty_hset) {
  ctx->nelems = 0;
  if (empty_hset && ctx->hset != NULL) {
    reset_int_array_hset(ctx->hset);
  }
  if (ctx->vset != NULL) {
    reset_int_bvset(ctx->vset);
  }
}


/*
 * Add binding [x --> t] to the context
 * - this masks any previous binding of x
 * - x and t must be non-negative
 */
void subst_ctx_push_binding(subst_ctx_t *ctx, int32_t x, int32_t t) {
  uint32_t i;

  assert(x >= 0 && t >= 0);

  i = ctx->nelems;
  if (i == ctx->size) {
    extend_subst_ctx(ctx);
  }
  assert(i < ctx->size);
  ctx->data[i].var = x;
  ctx->data[i].term = t;
  ctx->nelems = i+1;
}


/*
 * Collect the values of the last n bindings in array a
 * - n must be at least ctx->nelems
 * - a must be large enough to store n integers
 * - if the last n bindings were [x_1 --> t1, ... x_n --> t_n],
 *   in that order, then this function stores t_1 ... t_n in a[0 ... n-1]
 */
void subst_ctx_collect_bindings(subst_ctx_t *ctx, uint32_t n, int32_t *a) {
  uint32_t i, j;

  assert(n <= ctx->nelems);

  j = ctx->nelems - n;
  for (i=0; i<n; i++) {
    a[i] = ctx->data[j].term;
    j ++;
  }
}



/*
 * Get the term bound to x in the context
 * - x must be non-negative
 * - return -1 if x is not bound
 */
int32_t subst_ctx_lookup(subst_ctx_t *ctx, int32_t x) {
  uint32_t i;
  int32_t t;

  assert(x >= 0);

  t = -1;
  i = ctx->nelems;
  while (i > 0) {
    i --;
    if (ctx->data[i].var == x) {
      t = ctx->data[i].term;
      assert(t >= 0);
      break;
    }
  }

  return t;
}


/*
 * Sort an array of pairs:
 * - a is an array of k pairs <var, term>
 * - n = full size of array a = 2k
 * - each var occurs only once
 * - sort the array in increasing order of variables
 *
 * This uses a quick sort implementation.
 */
static void subst_ctx_sort_array(int32_t *a, uint32_t n) {
  uint32_t i, j;
  int32_t x, y, t;

  assert((n & 1) == 0);

  if (n > 2) {
    // random pivot
    i = random_uint(n) & ~1;
    assert((i & 1) == 0);

    /*
     * i is an even number:
     * a[i] is a variable x,
     * a[i+1] is the binding for x
     */
    x = a[i];
    t = a[i + 1];

    /*
     * swap the pivot pair (a[i], a[i+1]) and (a[0], a[1])
     */
    a[i] = a[0]; a[0] = x;
    a[i + 1] = a[1];
    a[1] = t; // could be removed?

    i = 0;
    j = n;
    do { j -= 2; } while (a[j] > x);
    do { i += 2; } while (i <= j && a[i] < x);

    while (i<j) {
      // swap (a[i], a[i+1]) and (a[j], a[j+1])
      y = a[i]; a[i] = a[j]; a[j] = y;
      y = a[i + 1]; a[i + 1] = a[j + 1]; a[j + 1] = y;

      do { j -= 2; } while (a[j] > x);
      do { i += 2; } while (a[i] < x);
    }

    // swap the pivot and  a[j], a[j+1]
    a[0] = a[j];
    a[j] = x;
    a[1] = a[j + 1];
    a[j + 1] = t;

    // recursively sort a[0...j-1] and a[j+2 ... n-1]
    subst_ctx_sort_array(a, j);
    j += 2;
    subst_ctx_sort_array(a + j, n - j);
  }
}


/*
 * For debugging: check whether array a is sorted
 * - n = 2k = full size of array a
 */
#ifndef NDEBUG
static bool subst_ctx_array_is_sorted(int32_t *a, uint32_t n) {
  uint32_t i;

  assert((n % 1) == 0);

  i = 2;
  while (i < n) {
    if (a[i-2] >= a[i]) return false;
    i += 2;
  }
  return true;
}
#endif


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
harray_t *subst_ctx_hash(subst_ctx_t *ctx) {
  int_array_hset_t *hset;
  int_bvset_t *vset;
  ivector_t *buffer;
  uint32_t i;
  int32_t x;


  vset = subst_ctx_get_vset(ctx);
  reset_int_bvset(vset);

  buffer = &ctx->buffer;
  ivector_reset(buffer);

  i = ctx->nelems;
  while (i > 0) {
    i --;
    x = ctx->data[i].var;
    if (int_bvset_add_check(vset, x)) {
      // rightmost occurrence of x in ctx->data
      // copy x + its binding in buffer
      ivector_push(buffer, x);
      ivector_push(buffer, ctx->data[i].term);
    }
  }

  // normalize: sort the buffer
  subst_ctx_sort_array(buffer->data, buffer->size);
  assert(subst_ctx_array_is_sorted(buffer->data, buffer->size));

  // hash-consing for the array buffer->data
  hset = subst_ctx_get_hset(ctx);
  return int_array_hset_get(hset, buffer->size, buffer->data);
}

