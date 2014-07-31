/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * CACHE TO STORE RESULTS OF A SUBSTITUTION
 */

#include <stdbool.h>
#include <assert.h>

#include "utils/memalloc.h"
#include "terms/subst_cache.h"



/*
 * HASH MAP FOR PAIRS (POINTER, INT32) --> INT32
 */

/*
 * For debugging: check whether n is 0 or a power of 2
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


/*
 * Initialize hmap:
 * - use the default size
 */
static void init_sctx_hmap(sctx_hmap_t *hmap) {
  sctx_hmap_rec_t *tmp;
  uint32_t i, n;

  n = SCTX_HMAP_DEF_SIZE;
  assert(is_power_of_two(n) && n <= SCTX_HMAP_MAX_SIZE);

  tmp = (sctx_hmap_rec_t *) safe_malloc(n * sizeof(sctx_hmap_rec_t));
  for (i=0; i<n; i++) {
    tmp[i].ptr = NULL;
  }

  hmap->data = tmp;
  hmap->size = n;
  hmap->nelems = 0;
  hmap->resize_threshold = (uint32_t) (n * SCTX_HMAP_RESIZE_RATIO);
}


/*
 * Delete: free all memory used
 */
static void delete_sctx_hmap(sctx_hmap_t *hmap) {
  safe_free(hmap->data);
  hmap->data = NULL;
}


/*
 * Hash code for a pair (ptr, k)
 */

/* Jenkins's lookup3 code (cf. hash_functions.c) */
#define rot(x,k) (((x)<<(k)) | ((x)>>(32-(k))))

#define final(a,b,c)      \
{                         \
  c ^= b; c -= rot(b,14); \
  a ^= c; a -= rot(c,11); \
  b ^= a; b -= rot(a,25); \
  c ^= b; c -= rot(b,16); \
  a ^= c; a -= rot(c,4);  \
  b ^= a; b -= rot(a,14); \
  c ^= b; c -= rot(b,24); \
}

static uint32_t hash_ptr_int(void *p, int32_t k) {
  uint64_t aux;
  uint32_t x, y, z;

  aux = (uint64_t) (((size_t) p) >> 3) ^ (((uint64_t) 0x98765432) << 32);

  x = (uint32_t) k;
  y = (uint32_t) (aux >> 32);
  z = (uint32_t) (aux & 0xFFFFFFFF);
  final(x, y, z);

  return z;
}



/*
 * Copy record r into a
 * - a must be an array of size 2^k for some k
 * - mask must be 2^k - 1
 * - there must be room for r into a
 */
static void sctx_hmap_clean_copy(sctx_hmap_rec_t *data, sctx_hmap_rec_t *r, uint32_t mask) {
  uint32_t i;

  i = hash_ptr_int(r->ptr, r->k) & mask;
  while (data[i].ptr != NULL) {
    i++;
    i &= mask;
  }

  data[i] = *r;
}



/*
 * Make the table twice as large. Keep its content
 */
static void sctx_hmap_extend(sctx_hmap_t *hmap) {
  sctx_hmap_rec_t *tmp, *r;
  uint32_t i, n, n2, mask;

  n = hmap->size;
  n2 = n << 1;
  if (n2 >= SCTX_HMAP_MAX_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n2));

  tmp = (sctx_hmap_rec_t *) safe_malloc(n2 * sizeof(sctx_hmap_rec_t));
  for (i=0; i<n2; i++) {
    tmp[i].ptr = NULL;
  }

  mask = n2 - 1;
  r = hmap->data;
  for (i=0; i<n; i++) {
    if (r->ptr != NULL) {
      // non-empy record: make a copy
      assert(r->k >= 0 && r->val >= 0);
      sctx_hmap_clean_copy(tmp, r, mask);
    }
    r ++;
  }

  safe_free(hmap->data);
  hmap->data = tmp;
  hmap->size = n2;
  hmap->resize_threshold = (uint32_t) (n2 * SCTX_HMAP_RESIZE_RATIO);
}



/*
 * Lookup (ptr, k) in hmap
 * - if there's a record for that pair, return the record's value
 * - otherwise return -1
 */
static int32_t sctx_hmap_find(sctx_hmap_t *hmap, void* p, int32_t k) {
  sctx_hmap_rec_t *r;
  uint32_t i, mask;


  assert(k >= 0 && p != NULL && hmap->nelems < hmap->size);

  mask = hmap->size - 1;
  i =  hash_ptr_int(p, k) & mask;
  for (;;) {
    r = hmap->data + i;
    if (r->ptr == NULL) return -1;
    if (r->ptr == p && r->k == k) return r->val;
    i ++;
    i &= mask;
  }
}


/*
 * Add mapping (ptr, k) --> v in hmap
 * - there must not be a record with the same key in the table
 */
static void sctx_hmap_add(sctx_hmap_t *hmap, void *p, int32_t k, int32_t v) {
  uint32_t i, mask;

  assert(p != NULL && k >= 0 && v >= 0 && hmap->nelems < hmap->size);
  assert(sctx_hmap_find(hmap, p, k) == -1);

  mask = hmap->size - 1;
  i = hash_ptr_int(p, k) & mask;
  while (hmap->data[i].ptr != NULL) {
    i ++;
    i &= mask;
  }

  hmap->data[i].ptr = p;
  hmap->data[i].k = k;
  hmap->data[i].val = v;
  hmap->nelems ++;

  if (hmap->nelems >= hmap->resize_threshold) {
    sctx_hmap_extend(hmap);
  }
}



/*
 * FULL CACHE
 */

/*
 * Initialize the cache:
 * - prime is initialized with its default size (cf. int_hash_map.h)
 * - second is NULL
 */
void init_subst_cache(subst_cache_t *cache) {
  init_int_hmap(&cache->prime, 0);
  cache->second = NULL;
}


/*
 * Get the secondary table
 * - allocate and initialize it if needed
 */
static sctx_hmap_t *subst_cache_get_second(subst_cache_t *cache) {
  sctx_hmap_t *tmp;

  tmp = cache->second;
  if (tmp == NULL) {
    tmp = (sctx_hmap_t *) safe_malloc(sizeof(sctx_hmap_t));
    init_sctx_hmap(tmp);
    cache->second = tmp;
  }

  return tmp;
}


/*
 * Delete: free memory
 */
void delete_subst_cache(subst_cache_t *cache) {
  delete_int_hmap(&cache->prime);
  if (cache->second != NULL) {
    delete_sctx_hmap(cache->second);
    safe_free(cache->second);
    cache->second = NULL;
  }
}


/*
 * Empty the cache
 * - the main table is emptied (but keeps its current size)
 * - the secondary table is deleted
 */
void reset_subst_cache(subst_cache_t *cache) {
  int_hmap_reset(&cache->prime);
  if (cache->second != NULL) {
    delete_sctx_hmap(cache->second);
    safe_free(cache->second);
    cache->second = NULL;
  }
}


/*
 * Read what's mapped to the pair (ctx, t)
 * - t must be non-negative
 * - return -1 if nothing is mapped to this pair
 */
int32_t subst_cache_lookup(subst_cache_t *cache, void *ctx, int32_t t) {
  int_hmap_pair_t *p;
  int32_t v;

  assert(t >= 0);

  v = -1;
  if (ctx == NULL) {
    p = int_hmap_find(&cache->prime, t);
    if (p != NULL) {
      v = p->val;
    }
  } else if (cache->second != NULL) {
    v = sctx_hmap_find(cache->second, ctx, t);
  }

  return v;
}


/*
 * Add the mapping (ctx, t -> v) to the cache
 * - this must be a new mapping (i.e., the pair (ctx, t) must not occur
 *   as a key in the table).
 * - v must be non-negative
 */
void subst_cache_add(subst_cache_t *cache, void *ctx, int32_t t, int32_t v) {
  int_hmap_pair_t *p;
  sctx_hmap_t *second;

  assert(t >= 0 && v >= 0);

  if (ctx == NULL) {
    p = int_hmap_get(&cache->prime, t);
    assert(p->val < 0); // new record
    p->val = v;
  } else {
    second = subst_cache_get_second(cache);
    sctx_hmap_add(second, ctx, t, v);
  }
}

