/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Pool for allocating mpq numbers in a thread-safe manner.
 */
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "utils/locks.h"
#include "utils/memalloc.h"
#include "terms/mpq_pool.h"

/*
 * A pool is a list of blocks, each block stores 64 mpz_t objects.
 * The pool is protected by a lock.
 */

/*
 * MPZ_BLOCK_SIZE is 2^MPZ_BLOCK_LOG
 */
#define MPZ_BLOCK_LOG  6
#define MPZ_BLOCK_SIZE 64

/*
 * DEBUG flag. Must be 0 when we use hellgrind
 */
#define DEBUG 0


/*
 * Block
 */
typedef struct mpz_pool_block mpz_pool_block_t;

struct mpz_pool_block {
  mpz_pool_block_t *next;
  mpz_t             bank[MPZ_BLOCK_SIZE];
};


/*
 * Pool structure
 */
typedef struct mpz_pool {
  lock_t             lock;         /* a lock protecting the pool                        */
  mpz_pool_block_t  *block;        /* the initial block                                 */
  mpz_pool_block_t  *last_block;   /* the last block  (for appending)                   */
  uint32_t           block_count;  /* the current number of blocks                      */
  uint32_t           capacity;     /* the capacity (length of) the pool array           */
  uint32_t           count;        /* the current number of mpzs in use                 */
  int32_t            start;        /* the start of the free list  (BD's trick)          */
} mpz_pool_t;


/*
 * Global pool.
 */
static mpz_pool_t the_mpz_pool;


/*
 * For an index i in the pool:
 * - block_index(i) = index of the block that contains i (i.e., i/1024)
 * - block_offset(i) = position of i in the block (i.e., i%1024)
 */
static inline uint32_t block_index(int32_t i) {
  assert(i >= 0);
  return ((uint32_t) i) >> MPZ_BLOCK_LOG;
}

static inline uint32_t block_offset(int32_t i) {
  assert(i >= 0);
  return ((uint32_t) i) & (MPZ_BLOCK_SIZE - 1);
}


/*
 * Allocate a pool block
 */
static mpz_pool_block_t *alloc_mpz_pool_block(void){
  mpz_pool_block_t *tmp;
  uint32_t i;

  tmp = (mpz_pool_block_t *) safe_malloc(sizeof(mpz_pool_block_t));
  tmp->next = NULL;
  for (i=0; i<MPZ_BLOCK_SIZE; i++) {
    mpz_init2(tmp->bank[i], 64);
  }
  return tmp;
}

/*
 * Initialize the pool
 */
static void init_mpz_pool(void){
  mpz_pool_block_t *b;

  create_lock(&the_mpz_pool.lock);

  b = alloc_mpz_pool_block();
  the_mpz_pool.block = b;
  the_mpz_pool.last_block = b;
  the_mpz_pool.block_count = 1;
  the_mpz_pool.capacity = MPZ_BLOCK_SIZE;
  the_mpz_pool.count = 0;
  the_mpz_pool.start = -1;
}


/*
 * Fetch an mpz number by its index i 
 */
mpz_ptr fetch_mpz(int32_t i) {  
  mpz_pool_block_t *block;
  uint32_t block_id;
  uint32_t index;

  block_id = block_index(i);
  index = block_offset(i);

#if POOL_DEBUG
  // This assert can fail if another thread writes to the_mpz_pool.block_count
  assert(0 <= block_id && block_id < the_mpz_pool.block_count);
#endif

  block = the_mpz_pool.block;
  while (block_id > 0) {
    block = block->next;
    block_id--;
  }
  return block->bank[index];
}


/*
 * Add a new block to the pool
 * - the caller must owe the pool's lock
 */
static void _o_grow_mpz_pool(void){
  mpz_pool_block_t* new_block;
  uint32_t new_capacity;

  new_capacity = the_mpz_pool.capacity + MPZ_BLOCK_SIZE;
  if (new_capacity > (UINT32_MAX/2)) {
    out_of_memory();
  }
  new_block = alloc_mpz_pool_block();

  the_mpz_pool.last_block->next = new_block;
  the_mpz_pool.last_block = new_block;
  the_mpz_pool.block_count += 1;
  the_mpz_pool.capacity = new_capacity;
}


/*
 * Reclaim a pool block
 * - the caller must own the lock
 */
static void _o_free_mpz_pool_block(mpz_pool_block_t* block){
  uint32_t i;

  for (i=0; i<MPZ_BLOCK_SIZE; i++) {
    mpz_clear(block->bank[i]);
  }
  free(block->bank);
}


/*
 * Reclaim the linked list of blocks
 * - the caller must own the lock
 */
static void _o_free_mpz_pool_blocks(void){
  mpz_pool_block_t *current_block, *next_block;

  current_block = the_mpz_pool.block;
  while (current_block != NULL) {
    next_block = current_block->next;
    _o_free_mpz_pool_block(current_block);
    safe_free (current_block);
    current_block = next_block;
  }
}

/*
 * Reclaim the pool
 * - the caller must hold the lock
 */
static void _o_free_mpz_pool(void) {
  _o_free_mpz_pool_blocks();
  the_mpz_pool.block = NULL;
  the_mpz_pool.last_block = NULL;
  the_mpz_pool.block_count = 0;
  the_mpz_pool.capacity = 0;
  the_mpz_pool.count = 0;
  the_mpz_pool.start = -1;
}


/*
 * Free-list operations
 */
static inline int32_t _o_free_list_next(int32_t i) {
  int32_t index;
  mpz_ptr next;

  next = fetch_mpz(i);
  index = mpz_get_si(next);
  assert(-1 <= index && index < (int32_t)the_mpz_pool.capacity);
  return index;
}

static inline void _o_free_list_insert(int32_t i) {
  mpz_ptr insert;

  assert(0 <= i && i < the_mpz_pool.capacity);
  assert(-1 <= the_mpz_pool.start && the_mpz_pool.start < (int32_t) the_mpz_pool.capacity);

  insert = fetch_mpz(i);
  mpz_set_si(insert, the_mpz_pool.start);
  the_mpz_pool.start = i;
}


/*
 * Allocate an mpz number: return the index
 */
static int32_t _o_alloc_mpz(void) {
  int32_t n;

  n = the_mpz_pool.start;
  if (n >= 0) {
    the_mpz_pool.start = _o_free_list_next(n);
  } else {
    n = the_mpz_pool.count;
    if (n >= the_mpz_pool.capacity) {
      _o_grow_mpz_pool();
    }
    the_mpz_pool.count = n + 1;
  }

  return n;
}


/*
 * Free allocated mpz number of index i
 */
void _o_free_mpz(int32_t i) {
  _o_free_list_insert(i);
}

/*
 * Init the pool (Pool API)
 */
void mpz_pool_init(void){
  init_mpz_pool();
}


/*
 * Borrow an mpz_t from the pool (Pool API)
 */
int32_t mpz_pool_borrow(mpz_ptr *q){
  int32_t i;

  get_lock(&the_mpz_pool.lock);
  i = _o_alloc_mpz();
  if (q != NULL) {
    *q = fetch_mpz(i);
  }
  release_lock(&the_mpz_pool.lock);

  return i;
}


/*
 * Return a mpz_t to the pool (Pool API)
 */
void mpz_pool_return(int32_t index){
  get_lock(&the_mpz_pool.lock);
  _o_free_mpz(index);
  release_lock(&the_mpz_pool.lock);
}

/*
 * Shutdown the pool (Pool API)
 */
void mpz_pool_shutdown(void){
  get_lock(&the_mpz_pool.lock);
  _o_free_mpz_pool();
  release_lock(&the_mpz_pool.lock);
  destroy_lock(&the_mpz_pool.lock);
}

