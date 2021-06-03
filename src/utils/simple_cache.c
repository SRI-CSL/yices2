/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * FIXED-SIZE CACHE
 *
 * - keys are 32bit signed integers
 * - values consist of a tag + a union that can store an integer or a pointer
 * - unused entries are marked by setting the key to -1
 * - a write to the cache just overwrite whatever was in the entry before
 */

#include <assert.h>
#include <stdbool.h>

#include "memalloc.h"
#include "simple_cache.h"


/*
 * For debugging: check whether n is a power of two (or 0)
 */
#ifndef NDEBUG
static bool is_power_of_two(uint32_t n) {
  return (n & (n - 1)) == 0;
}
#endif


/*
 * Initialize cache
 * - n = number of entries
 * - if n == 0, we use the default size.
 */
void init_simple_cache(simple_cache_t *cache, uint32_t n) {
  simple_cache_entry_t *tmp;
  uint32_t i;

  if (n == 0) {
    n = DEF_SIMPLE_CACHE_SIZE;
  }
  if (n > MAX_SIMPLE_CACHE_SIZE) {
    out_of_memory(); // abort
  }

  assert(is_power_of_two(n));

  tmp = (simple_cache_entry_t *) safe_malloc(n * sizeof(simple_cache_entry_t));
  for (i=0; i<n; i++) {
    tmp[i].key = -1;
  }
  cache->mask = n - 1;
  cache->data = tmp;
}


/*
 * Delete
 */
void delete_simple_cache(simple_cache_t *cache) {
  safe_free(cache->data);
  cache->data = NULL;
}


/*
 * Empty
 */
void reset_simple_cache(simple_cache_t *cache) {
  uint32_t i, n;

  n = cache->mask;
  for (i=0; i<=n; i++) {
    cache->data[i].key = -1;
  }
}


/*
 * Hash function: 32 bits unsigned to 32 bits
 * Source: Jenkins hash
 * (http://www.burtleburtle.net/bob/hash/integer.html)
 */
static uint32_t hash_key(uint32_t x) {
  x = (x + 0x7ed55d16) + (x<<12);
  x = (x ^ 0xc761c23c) ^ (x>>19);
  x = (x + 0x165667b1) + (x<<5);
  x = (x + 0xd3a2646c) ^ (x<<9);
  x = (x + 0xfd7046c5) + (x<<3);
  x = (x ^ 0xb55a4f09) ^ (x>>16);
  return x;
}


/*
 * Entry for key k
 * - k must be non-negative
 */
simple_cache_entry_t *simple_cache_get(const simple_cache_t *cache, int32_t k) {
  uint32_t i;

  assert(k >= 0);
  i = hash_key(k) & cache->mask;
  return cache->data + i;
}

/*
 * Search for the entry with key k
 * - k must be non-negative
 * - return NULL if k is not in the cache
 */
simple_cache_entry_t *simple_cache_find(const simple_cache_t *cache, int32_t k) {
  simple_cache_entry_t *e;

  e = simple_cache_get(cache, k);
  if (e->key != k) {
    e = NULL;
  }
  return e;
}


/*
 * Store data in a cache entry
 * - k must be non-negative
 * - tag can be anything
 * - there's one store function for every type
 * - the caller is responsible for mapping tags and type of value
 */
void simple_cache_store_ptr(simple_cache_t *cache, int32_t k, int32_t tag, void *x) {
  simple_cache_entry_t *e;

  e = simple_cache_get(cache, k);
  e->key = k;
  e->tag = tag;
  e->val.ptr = x;
}

void simple_cache_store_i64(simple_cache_t *cache, int32_t k, int32_t tag, int64_t x) {
  simple_cache_entry_t *e;

  e = simple_cache_get(cache, k);
  e->key = k;
  e->tag = tag;
  e->val.i64 = x;
}

void simple_cache_store_u64(simple_cache_t *cache, int32_t k, int32_t tag, uint64_t x) {
  simple_cache_entry_t *e;

  e = simple_cache_get(cache, k);
  e->key = k;
  e->tag = tag;
  e->val.u64 = x;
}

void simple_cache_store_i32(simple_cache_t *cache, int32_t k, int32_t tag, int32_t x) {
  simple_cache_entry_t *e;

  e = simple_cache_get(cache, k);
  e->key = k;
  e->tag = tag;
  e->val.i32 = x;
}

void simple_cache_store_u32(simple_cache_t *cache, int32_t k, int32_t tag, uint32_t x) {
  simple_cache_entry_t *e;

  e = simple_cache_get(cache, k);
  e->key = k;
  e->tag = tag;
  e->val.u32 = x;
}

