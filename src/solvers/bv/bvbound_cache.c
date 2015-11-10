/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Hash-table to cache the lower and upper bounds on a variable
 * x. There are four possible bounds for an n-bit variable x,
 * depending on whether x is interpreted as a signed (2's complement)
 * or unsigned integer.
 *
 * Each value stored in the cache is a record:
 * - var = variable x
 * - tag = which bound is considered
 * - data = the bound stored as an array of 32bit words
 * The bitsize of x is not stored (since it's available from the bv_vartable).
 */

#include <stdbool.h>
#include <stddef.h>

#include "solvers/bv/bvbound_cache.h"
#include "terms/bv_constants.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"


/*
 * For debugging: check whether n is a power of two
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif



/*
 * Initialize cache:
 * - n = initial size (must be a power of two)
 * - if n = 0, use the default size
 */
void init_bvbound_cache(bvbound_cache_t *cache, uint32_t n) {
  bvbound_t **tmp;
  uint32_t i;

  if (n == 0) {
    n = DEF_BVBOUND_CACHE_SIZE;
  }

  if (n >= MAX_BVBOUND_CACHE_SIZE) {
    out_of_memory();
  }

  assert(is_power_of_two(n));

  tmp = (bvbound_t **) safe_malloc(n * sizeof(bvbound_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  cache->data = tmp;
  cache->size = n;
  cache->nelems = 0;
  cache->ndeleted = 0;

  cache->resize_threshold = (uint32_t) (n * BVBOUND_CACHE_RESIZE_RATIO);
  cache->cleanup_threshold = (uint32_t) (n * BVBOUND_CACHE_CLEANUP_RATIO);
}


/*
 * Check whether an element of the data table is a valid pointer
 * (i.e., not NULL and not DELETED)
 * - we check whether b != 0 and b != 1
 */
static inline bool live_bvbound(bvbound_t *b) {
  return ((uintptr_t) b) >> 1 != 0;
}


/*
 * Delete the cache
 */
void delete_bvbound_cache(bvbound_cache_t *cache) {
  bvbound_t *d;
  uint32_t i, n;

  n = cache->size;
  for (i=0; i<n; i++) {
    d = cache->data[i];
    if (live_bvbound(d)) {
      safe_free(d);
    }
  }

  safe_free(cache->data);
  cache->data = NULL;
}


/*
 * Reset: empty the cache
 */
void reset_bvbound_cache(bvbound_cache_t *cache) {
  bvbound_t *d;
  uint32_t i, n;

  n = cache->size;
  for (i=0; i<n; i++) {
    d = cache->data[i];
    if (live_bvbound(d)) {
      safe_free(d);
    }
    cache->data[i] = NULL;
  }

  cache->nelems = 0;
  cache->ndeleted = 0;
}





/*
 * Convert bvbound's values to an unsigned 64bit number
 */
uint64_t bvbound_lower64(bvbound_t *b) {
  assert(1 <= b->bitsize && b->bitsize <= 64);
  if (b->bitsize <= 32) {
    return (uint64_t) b->data[0];
  } else {
    return ((uint64_t) b->data[0]) | (((uint64_t) b->data[1]) << 32);
  }
}

uint64_t bvbound_upper64(bvbound_t *b) {
  assert(1 <= b->bitsize && b->bitsize <= 64);
  if (b->bitsize <= 32) {
    return (uint64_t) b->data[1];
  } else {
    return ((uint64_t) b->data[2]) | (((uint64_t) b->data[3]) << 32);
  }
}




/*
 * Search for a bound with key (var, tag) in the cache
 * - return NULL if no matching record is found
 * - the table must not be full
 */
bvbound_t *find_bvbound(bvbound_cache_t *cache, bvbound_tag_t tag, int32_t x) {
  bvbound_t *d;
  uint32_t header;
  uint32_t mask, i;

  assert(cache->size > cache->nelems + cache->ndeleted);

  header = bvbound_header(x, tag);
  mask = cache->size - 1;
  i = jenkins_hash_uint32(header) & mask;
  for (;;) {
    d = cache->data[i];
    if (d == NULL || (d != DELETED_BVBOUND && d->header == header)) {
      return d;
    }
    i ++;
    i &= mask;
  }
}




/*
 * Build a new record: (tag, x, lower, higher)
 * - n = number of bits in variable x
 * - lower = lower bound on x
 * - upper = upper bound on x
 * The bounds are both normalized modulo 2^n (just a precaution).
 */
static bvbound_t *make_bvbound64(bvbound_tag_t tag, int32_t x, uint32_t n, uint64_t lower, uint64_t upper) {
  bvbound_t *b;
  uint32_t w;

  assert(1 <= n && n <= 64);

  w = (n + 31) >> 5;
  b = (bvbound_t *) safe_malloc(sizeof(bvbound_t) + 2 * w * sizeof(uint32_t));
  b->header = bvbound_header(x, tag);
  b->bitsize = n;

  if (n <= 32) {
    b->data[0] = (uint32_t) (lower & 0xffffffff);
    b->data[1] = (uint32_t) (upper & 0xffffffff);
    bvconst_normalize(b->data, n);
    bvconst_normalize(b->data + 1, n);
  } else {
    b->data[0] = (uint32_t) (lower & 0xffffffff);
    b->data[1] = (uint32_t) (lower >> 32);
    b->data[2] = (uint32_t) (upper & 0xffffffff);
    b->data[3] = (uint32_t) (upper >> 32);
    bvconst_normalize(b->data, n);
    bvconst_normalize(b->data + 1, n);
  }
  return b;
}



/*
 * Same thing for bounds given as arrays of uint32_t words
 */
static bvbound_t *make_bvbound(bvbound_tag_t tag, int32_t x, uint32_t n, uint32_t *lower, uint32_t *upper) {
  bvbound_t *b;
  uint32_t w, i;

  assert(1 <= n);

  w = (n + 31) >> 5;
  b = (bvbound_t *) safe_malloc(sizeof(bvbound_t) + 2 * w * sizeof(uint32_t));
  b->header = bvbound_header(x, tag);
  b->bitsize = n;

  for (i=0; i<w; i++) {
    b->data[i] = lower[i];
  }
  bvconst_normalize(b->data, n);
  for (i=0; i<w; i++) {
    b->data[w + i] = upper[i];
  }
  bvconst_normalize(b->data + w, n);

  return b;
}



/*
 * Store record pointer d into a clean array data
 * - mask = size of the array - 1 (the size must be a power of 2)
 * - the array must have room for d and must not contain a DELETED mark
 *   or a bound with the same (var, tag) as d
 */
static void bvbound_cache_clean_copy(bvbound_t **data, bvbound_t *d, uint32_t mask) {
  uint32_t i;

  i = jenkins_hash_uint32(d->header) & mask;
  while (data[i] != NULL) {
    i ++;
    i &= mask;
  }
  data[i] = d;
}


/*
 * Double the size, keep the content
 */
static void bvbound_cache_extend(bvbound_cache_t *cache) {
  bvbound_t **tmp;
  bvbound_t *d;
  uint32_t i, n, n2, mask;

  n = cache->size;
  n2 = n << 1;
  if (n2 >= MAX_BVBOUND_CACHE_SIZE) {
    out_of_memory();
  }
  tmp = (bvbound_t **) safe_malloc(n2 * sizeof(bvbound_t *));
  for (i=0; i<n2; i++) {
    tmp[i] = NULL;
  }

  mask = n2 - 1;
  for (i=0; i<n; i++) {
    d = cache->data[i];
    if (live_bvbound(d)) {
      bvbound_cache_clean_copy(tmp, d, mask);
    }
  }

  safe_free(cache->data);
  cache->data = tmp;
  cache->ndeleted = 0;
  cache->size = n2;

  cache->resize_threshold = (uint32_t)(n2 * BVBOUND_CACHE_RESIZE_RATIO);
  cache->cleanup_threshold = (uint32_t)(n2 * BVBOUND_CACHE_CLEANUP_RATIO);
}



/*
 * Remove all deleted elements
 */
static void bvbound_cache_cleanup(bvbound_cache_t *cache) {
  bvbound_t **tmp;
  bvbound_t *d;
  uint32_t i, n, mask;

  n = cache->size;
  tmp = (bvbound_t **) safe_malloc(n * sizeof(bvbound_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  mask = n-1;
  for (i=0; i<n; i++) {
    d = cache->data[i];
    if (live_bvbound(d)) {
      bvbound_cache_clean_copy(tmp, d, mask);
    }
  }

  safe_free(cache->data);
  cache->data = tmp;
  cache->ndeleted = 0;
}



/*
 * Add record d to the cache
 * - there must not be a record matching d already in the cache
 */
static void bvbound_cache_add(bvbound_cache_t *cache, bvbound_t *d) {
  bvbound_t *r;
  uint32_t mask, i;

  assert(cache->size > cache->nelems + cache->ndeleted);

  mask = cache->size - 1;
  i = jenkins_hash_uint32(d->header) & mask;
  for (;;) {
    r = cache->data[i];
    if (! live_bvbound(r)) break;
    assert(r->header != d->header);
    i ++;
    i &= mask;
  }

  // add d in cache->data[i];
  assert(r == cache->data[i] && (r == NULL || r == DELETED_BVBOUND));
  cache->data[i] = d;
  cache->nelems ++;
  if (r == DELETED_BVBOUND) {
    assert(cache->ndeleted > 0);
    cache->ndeleted --;
  } else if (cache->nelems + cache->ndeleted > cache->resize_threshold) {
    bvbound_cache_extend(cache);
  }
}



/*
 * Store bounds on x given as 64bit numbers
 * - n = number of bits of x (n must be positive and no more than 64)
 * - there must not be an existing bound on x with the same tag
 * return the bvbound object added to the table
 */
bvbound_t *cache_bvbound64(bvbound_cache_t *cache, bvbound_tag_t tag, int32_t x, uint32_t n, uint64_t lower, uint64_t upper) {
  bvbound_t *d;

  assert(find_bvbound(cache, tag, x) == NULL);
  d = make_bvbound64(tag, x, n, lower, upper);
  bvbound_cache_add(cache, d);

  return d;
}


/*
 * Same thing but the bounds are given as arrays of 32bit words
 * (cf. bv_constants.h)
 * - n must be positive
 * return the bvbound object added to the cache
 */
bvbound_t *cache_bvbound(bvbound_cache_t *cache, bvbound_tag_t tag, int32_t x, uint32_t n, uint32_t *lower, uint32_t *upper) {
  bvbound_t *d;

  assert(find_bvbound(cache, tag, x) == NULL);
  d = make_bvbound(tag, x, n, lower, upper);
  bvbound_cache_add(cache, d);

  return d;
}



/*
 * Remove bvbound with key (var, tag) from the cache
 */
static void remove_bvbound(bvbound_cache_t *cache, bvbound_tag_t tag, int32_t x) {
  bvbound_t *d;
  uint32_t header;
  uint32_t mask, i;

  assert(cache->size > cache->nelems + cache->ndeleted);

  mask = cache->size - 1;
  header = bvbound_header(x, tag);
  i = jenkins_hash_uint32(header) & mask;
  for (;;) {
    d = cache->data[i];
    if (d == NULL) return; // not in the cache
    if (d != DELETED_BVBOUND && d->header == header) break;
    i ++;
    i &= mask;
  }

  assert(d == cache->data[i] && d->header == header);
  safe_free(d);
  cache->data[i] = DELETED_BVBOUND;
  cache->nelems --;
  cache->ndeleted ++;
}




/*
 * Delete all records that refer to variable x
 */
void erase_bvbounds(bvbound_cache_t *cache, int32_t x) {
  remove_bvbound(cache, BVBOUND_UNSIGNED, x);
  remove_bvbound(cache, BVBOUND_SIGNED, x);
  if (cache->ndeleted > cache->cleanup_threshold) {
    bvbound_cache_cleanup(cache);
  }
}
