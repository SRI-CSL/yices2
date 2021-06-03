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

#ifndef __CACHE_H
#define __CACHE_H

#include <stdint.h>

/*
 * Each record in the cache stores
 * - a triple <tag, data[0], data[1]>
 * - the hash code for that triple
 * + a 16bit status flag
 */
typedef struct cache_elem_s {
  uint32_t hash;
  uint16_t flag;
  uint16_t tag;
  int32_t data[2];
} cache_elem_t;

// initial flag value for newly created elements
#define NEW_CACHE_ELEM 0


/*
 * Structure for allocation of records:
 * - block is an array of size 'capacity'
 * - for 0 <= i < nblocks:
 *   block[i] is a pointer to an allocated block (an array of
 *     CACHE_BLOCK_SIZE records)
 * - for nblocks <= i < capacity: block[i] is not initialized
 * - for 0 <= i < free_block: block[i] contains data
 * - for free_block <= i < nblocks, block[i] is empty
 * If the bank is empty, then free_blocks = 0
 * Otherwise, free_block > 0 and records are allocated in block[free_block-1]
 * - alloc_ptr = index of the first available slot in block[free_block-1]
 * - for 0 <= i < free_block - 1, block[i] is full
 */
typedef struct cache_bank_s {
  uint32_t capacity;
  uint32_t nblocks;
  uint32_t free_block;
  uint32_t alloc_ptr;
  cache_elem_t **block;
} cache_bank_t;

#define CACHE_BLOCK_SIZE 120

#define DEF_CACHE_BANK_SIZE 4
#define MAX_CACHE_BANK_SIZE (UINT32_MAX/sizeof(cache_elem_t*))


/*
 * Stack of allocation marks for push/pop operations
 * - each element in the stack has a level k>0
 *   and keeps a pointer to the first record allocated at that level
 *   the pointer consists of a pair <block id, index in block>
 * - the stack elements are in data[0 ... nmarks-1]
 * - current_level = current allocation level (incremented by push)
 * - top_level = 0 if the stack is empty
 *   otherwise top_level = maximal level in stack = data[nmarks-1].level
 */
typedef struct cache_mark_s {
  uint32_t level;
  uint32_t blk_id;
  uint32_t index;
} cache_mark_t;

typedef struct cache_levstack_s {
  uint32_t current_level;
  uint32_t top_level;
  uint32_t nmarks;
  uint32_t size;
  cache_mark_t *data;
} cache_levstack_t;

#define DEF_CACHE_STACK_SIZE 10
#define MAX_CACHE_STACK_SIZE (UINT32_MAX/sizeof(cache_mark_t))


/*
 * Hash table (see int_hash_table, etc.)
 */
typedef struct cache_htbl_s {
  cache_elem_t **data;  // hash table proper
  uint32_t size;        // its size (power of 2)
  uint32_t nelems;      // number of elements
  uint32_t ndeleted;
  uint32_t resize_threshold;
  uint32_t cleanup_threshold;
} cache_htbl_t;


/*
 * Marker for deleted elements
 */
#define DELETED_ELEM ((cache_elem_t *) 1)

/*
 * DEF_CACHE_HTBL_SIZE must be a power of 2, smaller than MAX_CACHE_HTBL_SIZE
 */
#define DEF_CACHE_HTBL_SIZE 32
#define MAX_CACHE_HTBL_SIZE (UINT32_MAX/sizeof(cache_elem_t*))
#define CACHE_HTBL_RESIZE_RATIO  0.6
#define CACHE_HTBL_CLEANUP_RATIO 0.2


/*
 * Full cache
 */
typedef struct cache_s {
  cache_htbl_t htbl;
  cache_levstack_t stack;
  cache_bank_t bank;
} cache_t;




/***********************
 *  CREATION/DELETION  *
 **********************/

/*
 * Initialize the cache: memory for stack and bank is not
 * allocated yet.
 */
extern void init_cache(cache_t *cache);

/*
 * Delete all objects stored in the table and all allocated memory
 */
extern void delete_cache(cache_t *cache);

/*
 * Empty the table and set current_level to 0
 */
extern void reset_cache(cache_t *cache);

/*
 * Push
 */
static inline void cache_push(cache_t *cache) {
  cache->stack.current_level ++;
}

/*
 * Pop: delete all objects created at the current level
 * then decrement current_level. Should not be called at level 0.
 */
extern void cache_pop(cache_t *cache);


/*
 * Set level: same effect as calling push n times from the initial state.
 * - this is used to ensure consistency between cache->current_level
 *   and solver->base_level (solver may be the simplex solver) if the cache
 *   is created when the solver has non-zero base_level
 */
static inline void cache_set_level(cache_t *cache, uint32_t n) {
  cache->stack.current_level = n;
}


/**********************
 *  CACHE OPERATIONS  *
 *********************/

/*
 * Find a cache element for <tag, x, y>
 * - return NULL if there's no matching element in the hash table
 */
extern cache_elem_t *cache_find(const cache_t *cache, uint16_t tag, int32_t x, int32_t y);

/*
 * Find or store element <tag, x, y> in the cache
 * - a pointer to the existing or new element is returned
 * - for a new element, the flag is set to 0 (i.e., NEW_CACHE_ELEM)
 *   (the caller should set the flag to something else)
 */
extern cache_elem_t *cache_get(cache_t *cache, uint16_t tag, int32_t x, int32_t y);


#endif /* __CACHE_H */
