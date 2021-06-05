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
 * SIMPLE CACHE
 */

/*
 * Each element in the cache is a triple <tag, x, y>
 * where x and y are 32bit signed integers and tag is 16 bit.
 * - this is enough for the egraph lemma generation
 *   (ackermann trick + expansion of non-distinct)
 * - the cache implements push and pop operations
 */

#include <stdbool.h>
#include <stddef.h>
#include <assert.h>

#include "utils/cache.h"
#include "utils/memalloc.h"



/**********************************
 *  ALLOCATION OF CACHE ELEMENTS  *
 *********************************/

/*
 * Initialize bank: don't allocate anything
 */
static void init_cache_bank(cache_bank_t *bank) {
  bank->capacity = 0;
  bank->nblocks = 0;
  bank->free_block = 0;
  bank->alloc_ptr = CACHE_BLOCK_SIZE;
  bank->block = NULL;
}

/*
 * Delete bank
 */
static void delete_cache_bank(cache_bank_t *bank) {
  uint32_t i;

  for (i=0; i<bank->nblocks; i++) {
    safe_free(bank->block[i]);
  }
  safe_free(bank->block);
  bank->block = NULL;
}


/*
 * Reset
 */
static inline void reset_cache_bank(cache_bank_t *bank) {
  bank->free_block = 0;
  bank->alloc_ptr = CACHE_BLOCK_SIZE;
}


/*
 * Increase the capacity by 50%
 */
static void extend_cache_bank(cache_bank_t *bank) {
  uint32_t n;

  n = bank->capacity;
  n += n>>1;
  if (n < DEF_CACHE_BANK_SIZE) {
    n = DEF_CACHE_BANK_SIZE;
  }
  if (n >= MAX_CACHE_BANK_SIZE) out_of_memory();

  bank->block = (cache_elem_t **) safe_realloc(bank->block, n * sizeof(cache_elem_t *));
  bank->capacity = n;
}


/*
 * Allocate an new block
 */
static void allocate_cache_block(cache_bank_t *bank) {
  uint32_t i, n;

  i = bank->nblocks;
  n = bank->capacity;
  assert(i <= n);
  if (i == n) {
    extend_cache_bank(bank);
    assert(i < bank->capacity);
  }
  bank->block[i] = (cache_elem_t *) safe_malloc(CACHE_BLOCK_SIZE * sizeof(cache_elem_t));
  bank->nblocks = i+1;
}


/*
 * Allocate a new element
 */
static cache_elem_t *alloc_cache_elem(cache_bank_t *bank) {
  uint32_t i, p;
  cache_elem_t *tmp;

  i = bank->free_block;
  p = bank->alloc_ptr;
  assert(p <= CACHE_BLOCK_SIZE);
  if (p == CACHE_BLOCK_SIZE) {
    // the current block is full or does not exist
    if (i >= bank->nblocks) {
      allocate_cache_block(bank);
      assert(i < bank->nblocks);
    }
    i ++;
    bank->free_block = i;
    p = 0;
  }
  assert(i > 0 && bank->block[i-1] != NULL);
  tmp = bank->block[i-1] + p;
  bank->alloc_ptr = p+1;

  return tmp;
}





/********************
 *  PUSH/POP STACK  *
 *******************/

/*
 * Initialize the stack: no memory allocated yet
 */
static void init_cache_stack(cache_levstack_t *stack) {
  stack->current_level = 0;
  stack->top_level = 0;
  stack->nmarks = 0;
  stack->size = 0;
  stack->data = NULL;
}


/*
 * Delete the stack
 */
static void delete_cache_stack(cache_levstack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Empty stack
 */
static void reset_cache_stack(cache_levstack_t *stack) {
  stack->current_level = 0;
  stack->top_level = 0;
  stack->nmarks = 0;
}


/*
 * Push mark <b, p> on top of the stack
 * - current_level must be larger than top_level
 */
static void push_cache_mark(cache_levstack_t *stack, uint32_t b, uint32_t p) {
  uint32_t i, k, n;

  assert(stack->current_level > stack->top_level);

  k = stack->current_level;
  i = stack->nmarks;
  n = stack->size;

  if (i == n) {
    // increase the size
    if (n < DEF_CACHE_STACK_SIZE) {
      n = DEF_CACHE_STACK_SIZE;
    } else {
      n += n>>1;
      if (n > MAX_CACHE_STACK_SIZE) out_of_memory();
    }
    stack->data = (cache_mark_t *) safe_realloc(stack->data, n * sizeof(cache_mark_t));
    stack->size = n;
  }

  assert(i < n);
  stack->data[i].level = k;
  stack->data[i].blk_id = b;
  stack->data[i].index = p;

  stack->nmarks = i + 1;
  stack->top_level = k;
}



/*
 * Remove the top mark
 */
static void pop_top_mark(cache_levstack_t *stack) {
  uint32_t i;

  assert(stack->nmarks > 0);

  i = stack->nmarks - 1;
  stack->nmarks = i;
  if (i == 0) {
    stack->top_level = 0;
  } else {
    stack->top_level = stack->data[i-1].level;
  }
}




/****************
 *  HASH TABLE  *
 ***************/

/*
 * Initialize to the default size
 */
static void init_cache_htbl(cache_htbl_t *table) {
  uint32_t i, n;
  cache_elem_t **tmp;

  n = DEF_CACHE_HTBL_SIZE;
  assert(n < MAX_CACHE_HTBL_SIZE);

  tmp = (cache_elem_t **) safe_malloc(n * sizeof(cache_elem_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  table->data = tmp;
  table->size = n;
  table->nelems = 0;
  table->ndeleted = 0;

  table->resize_threshold = (uint32_t) (n * CACHE_HTBL_RESIZE_RATIO);
  table->cleanup_threshold = (uint32_t) (n * CACHE_HTBL_CLEANUP_RATIO);
}


/*
 * Delete table
 */
static void delete_cache_htbl(cache_htbl_t *table) {
  safe_free(table->data);
  table->data = NULL;
}


/*
 * Reset: empty the table
 */
static void reset_cache_htbl(cache_htbl_t *table) {
  uint32_t i, n;

  n = table->size;
  for (i=0; i<n; i++) {
    table->data[i] = NULL;
  }
  table->nelems = 0;
  table->ndeleted = 0;
}


/*
 * Store pointer e into a clean array data
 * - mask = size of data - 1 (size must be a power of 2)
 * - e->hash must be set to the correct hash code
 * - data must not be full and must not contain deleted marks
 */
static void cache_htbl_clean_copy(cache_elem_t **data, cache_elem_t *e, uint32_t mask) {
  uint32_t j;

  j = e->hash & mask;
  while (data[j] != NULL) {
    j ++;
    j &= mask;
  }
  data[j] = e;
}


/*
 * Check whether pointer e is not NULL or DELETED_ELEM
 * - HACK: we rely on ((uintptr_t) NULL) == 0 and
 *  ((uintptr_t) DELETED_ELEM) == 1
 */
static inline bool live_element(cache_elem_t *e) {
  return (((uintptr_t) e) >> 1) != 0;
}


/*
 * Remove all deleted element from table
 */
static void cache_htbl_cleanup(cache_htbl_t *table) {
  cache_elem_t **tmp, *e;
  uint32_t i, n, mask;

  n = table->size;
  tmp = (cache_elem_t **) safe_malloc(n * sizeof(cache_elem_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }

  mask = n-1;
  for (i=0; i<n; i++) {
    e = table->data[i];
    if (live_element(e)) {
      cache_htbl_clean_copy(tmp, e, mask);
    }
  }

  safe_free(table->data);
  table->data = tmp;
  table->ndeleted = 0;
}


/*
 * Remove dead elements if the deletion threshold is reached
 */
static inline void cache_htbl_cleanup_if_needed(cache_htbl_t *table) {
  if (table->ndeleted > table->cleanup_threshold) {
    cache_htbl_cleanup(table);
  }
}


/*
 * Double the table size and remove dead elements
 */
static void cache_htbl_extend(cache_htbl_t *table) {
  cache_elem_t **tmp, *e;
  uint32_t i, n, new_size, mask;

  n = table->size;
  new_size = 2 * n;
  if (new_size >= MAX_CACHE_HTBL_SIZE) out_of_memory();
  tmp = (cache_elem_t **) safe_malloc(new_size * sizeof(cache_elem_t *));
  for (i=0; i<new_size; i++) {
    tmp[i] = NULL;
  }

  mask = new_size - 1;
  for (i=0; i<n; i++) {
    e = table->data[i];
    if (live_element(e)) {
      cache_htbl_clean_copy(tmp, e, mask);
    }
  }

  safe_free(table->data);
  table->data = tmp;
  table->ndeleted = 0;
  table->size = new_size;
  table->resize_threshold = (uint32_t)(new_size * CACHE_HTBL_RESIZE_RATIO);
  table->cleanup_threshold = (uint32_t)(new_size * CACHE_HTBL_CLEANUP_RATIO);
}


/*
 * Remove e from the table
 * - e must be present and e->hash must be valid
 */
static void cache_htbl_remove(cache_htbl_t *table, cache_elem_t *e) {
  uint32_t mask, j;

  mask = table->size - 1;
  j = e->hash & mask;
  while (table->data[j] != e) {
    j ++;
    j &= mask;
  }
  table->data[j] = DELETED_ELEM;
  table->nelems --;
  table->ndeleted ++;
}




/**********************
 *  CACHE OPERATIONS  *
 *********************/

/*
 * Initialize
 */
void init_cache(cache_t *cache) {
  init_cache_htbl(&cache->htbl);
  init_cache_stack(&cache->stack);
  init_cache_bank(&cache->bank);
}


/*
 * Delete everything
 */
void delete_cache(cache_t *cache) {
  delete_cache_bank(&cache->bank);
  delete_cache_stack(&cache->stack);
  delete_cache_htbl(&cache->htbl);
}


/*
 * Empty the cache
 */
void reset_cache(cache_t *cache) {
  reset_cache_htbl(&cache->htbl);
  reset_cache_stack(&cache->stack);
  reset_cache_bank(&cache->bank);
}



/*
 * Remove from htbl all objects in the bank
 * allocated after the mark <b, i>
 * - b = free_block at the time push_cache_mark was called
 * - i = alloc_ptr at the time push_cache_mark was called
 */
static void remove_level(cache_bank_t *bank, cache_htbl_t *htbl, uint32_t b, uint32_t i) {
  uint32_t n, p;
  cache_elem_t *blk;

  /*
   * n = current free_block
   * p = current alloc_ptr in block[n-1]
   */
  n = bank->free_block;
  p = bank->alloc_ptr;

  /*
   * restore free_block and alloc_ptr to what they where on
   * entry to the current level.
   */
  bank->free_block = b;
  bank->alloc_ptr = i;

  /*
   * We want to remove
   * elements from i to CACHE_BLOCK_SIZE - 1 in block[b-1]
   * elements from 0 to CACHE_CLOCK_SIZE - 1 in block[b] to block[n-2]
   * elements from 0 to p - 1 in block[n-1]
   */
  if (i == CACHE_BLOCK_SIZE) {
    // either b=0 or there's nothing to delete in block[b-1]
    i = 0;
    b ++;
  }

  assert(b>0);
  while (b<n) {
    blk = bank->block[b - 1];
    while (i<CACHE_BLOCK_SIZE) {
      cache_htbl_remove(htbl, blk+i);
      i ++;
    }
    i = 0;
    b ++;
  }

  // last block
  assert(b == n);
  blk = bank->block[b - 1];
  while (i<p) {
    cache_htbl_remove(htbl, blk+i);
    i ++;
  }
}


/*
 * Pop: delete all element created at the current level
 */
void cache_pop(cache_t *cache) {
  cache_levstack_t *stack;
  uint32_t i;

  stack = &cache->stack;
  assert(stack->current_level > 0);

  if (stack->current_level == stack->top_level) {
    assert(stack->nmarks > 0);
    i = stack->nmarks - 1;
    assert(stack->data[i].level == stack->current_level);
    remove_level(&cache->bank, &cache->htbl, stack->data[i].blk_id, stack->data[i].index);
    cache_htbl_cleanup_if_needed(&cache->htbl);
    pop_top_mark(stack);
  }

  stack->current_level --;
}


/*
 * Hash code for key <tag, x, y> (based on Jenkins's lookup3 code)
 */
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

static uint32_t hash_key(uint16_t tag, int32_t x, int32_t y) {
  uint32_t a, b, c;

  a = ((((uint32_t) x) & 0xFFFFFF) << 8) | (((uint32_t) tag) & 0xFF);
  b = ((((uint32_t) y) & 0xFFFFFF) << 8) | (((uint32_t) tag) >> 8);
  c = 0xdeadbeef;
  final(a, b, c);

  return c;
}


/*
 * Check whether e has key <tag, x, y>
 */
static inline bool elem_matches(const cache_elem_t *e, uint16_t tag, int32_t x, int32_t y) {
  return e->tag == tag && e->data[0] == x && e->data[1] == y;
}

/*
 * Search for a cached element of key <tag, x, y>
 * - return NULL if it's not in the table
 */
cache_elem_t *cache_find(const cache_t *cache, uint16_t tag, int32_t x, int32_t y) {
  const cache_htbl_t *htbl;
  uint32_t j, h, mask;
  cache_elem_t *e;

  htbl = &cache->htbl;
  assert(htbl->nelems + htbl->ndeleted < htbl->size);

  mask = htbl->size - 1;
  h = hash_key(tag, x, y);
  j = h & mask;
  for (;;) {
    e = htbl->data[j];
    if (e == NULL || (e != DELETED_ELEM && e->hash == h && elem_matches(e, tag, x, y))) {
      return e;
    }
    j ++;
    j &= mask;
  }
}



/*
 * Add a mark to the stack if current_level>top_level
 */
static void push_mark_if_needed(cache_levstack_t *stack, cache_bank_t *bank) {
  if (stack->current_level > stack->top_level) {
    push_cache_mark(stack, bank->free_block, bank->alloc_ptr);
  }
}

/*
 * Find or add a cache element <tag, x, y>
 * - if the element is new, then its flag is initialized to NEW_CACHE_ELEM (i.e., 0)
 */
cache_elem_t *cache_get(cache_t *cache, uint16_t tag, int32_t x, int32_t y) {
  cache_htbl_t *htbl;
  uint32_t k, j, h, mask;
  cache_elem_t *e;

  htbl = &cache->htbl;
  assert(htbl->nelems + htbl->ndeleted < htbl->size);

  mask = htbl->size - 1;
  h = hash_key(tag, x, y);
  j = h & mask;
  for (;;) {
    e = htbl->data[j];
    if (e == NULL) goto add;
    if (e == DELETED_ELEM) break;
    if (e->hash == h && elem_matches(e, tag, x, y)) goto found;
    j ++;
    j &= mask;
  }

  // htbl->data[j] = where new descriptor can be added
  k = j;
  for (;;) {
    k ++;
    k &= mask;
    e = htbl->data[k];
    if (e == NULL) {
      htbl->ndeleted --;
      goto add;
    }
    if (e != DELETED_ELEM && e->hash == h && elem_matches(e, tag, x, y)) goto found;
  }

 add:
  push_mark_if_needed(&cache->stack, &cache->bank);

  e = alloc_cache_elem(&cache->bank);
  e->hash = h;
  e->flag = NEW_CACHE_ELEM;
  e->tag = tag;
  e->data[0] = x;
  e->data[1] = y;

  htbl->data[j] = e;
  htbl->nelems ++;
  if (htbl->nelems + htbl->ndeleted > htbl->resize_threshold) {
    cache_htbl_extend(htbl);
  }

 found:
  return e;
}
