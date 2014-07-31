/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * FIXED-SIZE CACHE
 */

/*
 * Keys are non-negative 32bit integers
 * Values consist of a 32bit tag + a union that can
 * store an integer or a pointer.
 */

#ifndef __SIMPLE_CACHE_H
#define __SIMPLE_CACHE_H

#include <stdint.h>


/*
 * Entry in the cache
 * - key = 32bit integer (signed)
 * - tag = 32bit integer (signed)
 * - value = 64bit union type
 */
typedef struct simple_cache_entry_s {
  int32_t key;
  int32_t tag;
  union {
    void *ptr;
    int64_t i64;
    uint64_t u64;
    int32_t i32;
    uint32_t u32;
  } val;
} simple_cache_entry_t;


/*
 * Cache = an array of 2^k entries
 * - mask = 2^k - 1 (set at creation time)
 * - data = the array itself (contains 2^k entries)
 */
typedef struct simple_cache_s {
  uint32_t mask;
  simple_cache_entry_t *data;
} simple_cache_t;


#define DEF_SIMPLE_CACHE_SIZE 256
#define MAX_SIMPLE_CACHE_SIZE (UINT32_MAX/sizeof(simple_cache_entry_t))


/*
 * OPERATIONS
 */

/*
 * Initialize a cache of size n
 * - if n = 0, the default size is used
 * - otherwise n must be a power of two
 */
extern void init_simple_cache(simple_cache_t *cache, uint32_t n);


/*
 * Delete the cache: free memory
 */
extern void delete_simple_cache(simple_cache_t *cache);


/*
 * Empty the cache
 */
extern void reset_simple_cache(simple_cache_t *cache);


/*
 * Search for the entry with key = k
 * - k must be non-negative
 * - return NULL if there's no matching entry
 */
extern simple_cache_entry_t *simple_cache_find(simple_cache_t *cache, int32_t k);


/*
 * Get the entry for key k
 * - key must be non-negative
 */
extern simple_cache_entry_t *simple_cache_get(simple_cache_t *cache, int32_t k);


/*
 * Store data in a cache entry
 * - there's one store function for every type
 * - the caller is responsible for mapping tags and type of value
 */
extern void simple_cache_store_ptr(simple_cache_t *cache, int32_t k, int32_t tag, void *x);
extern void simple_cache_store_i64(simple_cache_t *cache, int32_t k, int32_t tag, int64_t x);
extern void simple_cache_store_u64(simple_cache_t *cache, int32_t k, int32_t tag, uint64_t x);
extern void simple_cache_store_i32(simple_cache_t *cache, int32_t k, int32_t tag, int32_t x);
extern void simple_cache_store_u32(simple_cache_t *cache, int32_t k, int32_t tag, uint32_t x);




#endif /* __SIMPLE_CACHE_H */
