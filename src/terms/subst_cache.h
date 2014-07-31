/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * CACHE TO STORE RESULTS OF A SUBSTITUTION
 */

/*
 * A substitution is given by a mapping from variable indices to term
 * indices. To deal with quantifier (and lambda terms in the future),
 * we may have to rename variables during substitution. We keep
 * track of variable renamings using the 'subst_context' structure.
 *
 * A substitution cache stores the result of a substitution S applied
 * to a term t in a subst_context ctx.
 *
 * The cache is implemented as a pair of hash tables:
 * - A main hash table is used for the empty context (ctx = NULL).
 *   This table maps terms to terms.
 * - A secondary table maps pairs (term, context) to terms.
 *   In this table, context is just a void* pointer. This is enough
 *   since 'subst_context' uses hash-consing.
 *
 * All term/variable indices must be non-negative.
 */

#ifndef __SUBST_CACHE_H
#define __SUBST_CACHE_H

#include <stdint.h>

#include "utils/int_hash_map.h"


/*
 * Records stored in the secondary hash table
 * - key = pair (void*, int32_t)
 * - val = int32_t
 *
 * Empty records are marked by setting ptr to NULL.
 */
typedef struct sctx_hmap_rec_s {
  void *ptr;
  int32_t k;
  int32_t val;
} sctx_hmap_rec_t;


/*
 * Hash table components:
 * - data = the table proper
 * - size = its size (must be a power of 2)
 * - nelems = number of element stored
 * - resize_threshold = to trigger resizing
 */
typedef struct sctx_hmap_s {
  sctx_hmap_rec_t *data;
  uint32_t size;
  uint32_t nelems;
  uint32_t resize_threshold;
} sctx_hmap_t;


/*
 * Default and maximal sizes
 */
#define SCTX_HMAP_DEF_SIZE 64
#define SCTX_HMAP_MAX_SIZE (UINT32_MAX/sizeof(sctx_hmap_rec_t))

/*
 * Resize ratio: resize_threshold is set to RATIO * size
 */
#define SCTX_HMAP_RESIZE_RATIO 0.6



/*
 * Full cache: two hash tables
 * - the main table is always allocated
 * - the secondary table is allocated lazily
 */
typedef struct subst_cache_s {
  int_hmap_t prime;        // [term -> term]
  sctx_hmap_t *second;     // [term, ctx -> term]
} subst_cache_t;



/*
 * Initialize the cache:
 * - prime is initialized with its default size (cf. int_hash_map.h)
 * - second is NULL
 */
extern void init_subst_cache(subst_cache_t *cache);


/*
 * Delete: free memory
 */
extern void delete_subst_cache(subst_cache_t *cache);


/*
 * Empty the cache
 * - the main table is emptied (but keeps its current size)
 * - the secondary table is deleted
 */
extern void reset_subst_cache(subst_cache_t *cache);


/*
 * Read what's mapped to the pair (ctx, t)
 * - t must be non-negative
 * - return -1 if nothing is mapped to this pair
 */
extern int32_t subst_cache_lookup(subst_cache_t *cache, void *ctx, int32_t t);


/*
 * Add the mapping (ctx, t -> v) to the cache
 * - this must be a new mapping (i.e., the pair (ctx, t) must not occur
 *   as a key in the table).
 * - v must be non-negative
 */
extern void subst_cache_add(subst_cache_t *cache, void *ctx, int32_t t, int32_t v);



#endif /* __SUBST_CACHE_H */
