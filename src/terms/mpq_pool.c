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
 * A pool is a list of blocks, each block stores 1024 mpq_t objects.
 * The pool is protected by a lock.
 */

/*
 * MPQ_BLOCK_SIZE is 2^MPQ_BLOCK_LOG
 */
#define MPQ_BLOCK_LOG  10
#define MPQ_BLOCK_SIZE 1024

/*
 * DEBUG flag. Must be 0 when we use hellgrind
 */
#define DEBUG 0


/*
 * Block
 */
typedef struct mpq_pool_block mpq_pool_block_t;

struct mpq_pool_block {
  mpq_pool_block_t *next;
  mpq_t             bank[MPQ_BLOCK_SIZE];
};


/*
 * Pool structure
 */
typedef struct mpq_pool {
  lock_t             lock;         /* a lock protecting the pool                        */
  mpq_pool_block_t  *block;        /* the initial block                                 */
  mpq_pool_block_t  *last_block;   /* the last block  (for appending)                   */
  uint32_t           block_count;  /* the current number of blocks                      */
  uint32_t           capacity;     /* the capacity (length of) the pool array           */
  uint32_t           count;        /* the current number of mpqs in use                 */
  int32_t            start;        /* the start of the free list  (BD's trick)          */
} mpq_pool_t;


/*
 * Global pool
 */
static mpq_pool_t the_mpq_pool;


/*
 * For an index i in the pool:
 * - block_index(i) = index of the block that contains i (i.e., i/1024)
 * - block_offset(i) = position of i in the block (i.e., i%1024)
 */
static inline uint32_t block_index(int32_t i) {
  assert(i >= 0);
  return ((uint32_t) i) >> MPQ_BLOCK_LOG;
}

static inline uint32_t block_offset(int32_t i) {
  assert(i >= 0);
  return ((uint32_t) i) & (MPQ_BLOCK_SIZE - 1);
}


/*
 * Initialize q to hold 64bit integers (initially)
 * - q must not be initialized.
 */
static void init_mpq64(mpq_t q) {
  mpz_ptr num_q, den_q;

  num_q = mpq_numref(q);
  den_q = mpq_denref(q);
  mpz_init2(num_q, 64);
  mpz_init2(den_q, 64);
  mpz_set_ui(den_q, 1);
}


/*
 * Allocate a pool block
 */
static mpq_pool_block_t *alloc_mpq_pool_block(void){
  mpq_pool_block_t *tmp;
  uint32_t i;

  tmp = (mpq_pool_block_t *) safe_malloc(sizeof(mpq_pool_block_t));
  tmp->next = NULL;
  for (i=0; i<MPQ_BLOCK_SIZE; i++) {
    init_mpq64(tmp->bank[i]);
  }
  return tmp;
}

/*
 * Initialize the pool
 */
static void init_mpq_pool(void){
  mpq_pool_block_t *b;

  create_lock(&the_mpq_pool.lock);

  b = alloc_mpq_pool_block();
  the_mpq_pool.block = b;
  the_mpq_pool.last_block = b;
  the_mpq_pool.block_count = 1;
  the_mpq_pool.capacity = MPQ_BLOCK_SIZE;
  the_mpq_pool.count = 0;
  the_mpq_pool.start = -1;
}


/*
 * Fetch an mpq number by its index i 
 */
mpq_ptr fetch_mpq(int32_t i) {  
  mpq_pool_block_t *block;
  uint32_t block_id;
  uint32_t index;

  block_id = block_index(i);
  index = block_offset(i);

#if DEBUG
  // This assert can fail if another thread writes to the_mpq_pool.block_count
  assert(0 <= block_id && block_id < the_mpq_pool.block_count);
#endif

  block = the_mpq_pool.block;
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
static void _o_grow_mpq_pool(void){
  mpq_pool_block_t* new_block;
  uint32_t new_capacity;

  new_capacity = the_mpq_pool.capacity + MPQ_BLOCK_SIZE;
  if (new_capacity > (UINT32_MAX/2)) {
    out_of_memory();
  }
  new_block = alloc_mpq_pool_block();

  the_mpq_pool.last_block->next = new_block;
  the_mpq_pool.last_block = new_block;
  the_mpq_pool.block_count += 1;
  the_mpq_pool.capacity = new_capacity;
}


/*
 * Reclaim a pool block
 * - the caller must own the lock
 */
static void _o_free_mpq_pool_block(mpq_pool_block_t* block){
  uint32_t i;

  for (i=0; i<MPQ_BLOCK_SIZE; i++) {
    mpq_clear(block->bank[i]);
  }
  free(block->bank);
}


/*
 * Reclaim the linked list of blocks
 * - the caller must own the lock
 */
static void _o_free_mpq_pool_blocks(void){
  mpq_pool_block_t *current_block, *next_block;

  current_block = the_mpq_pool.block;
  while (current_block != NULL) {
    next_block = current_block->next;
    _o_free_mpq_pool_block(current_block);
    safe_free (current_block);
    current_block = next_block;
  }
}

/*
 * Reclaim the pool
 * - the caller must hold the lock
 */
static void _o_free_mpq_pool(void) {
  _o_free_mpq_pool_blocks();
  the_mpq_pool.block = NULL;
  the_mpq_pool.last_block = NULL;
  the_mpq_pool.block_count = 0;
  the_mpq_pool.capacity = 0;
  the_mpq_pool.count = 0;
  the_mpq_pool.start = -1;
}


/*
 * Free-list operations
 */
static inline int32_t _o_free_list_next(int32_t i) {
  int32_t index;
  mpq_ptr next;

  next = fetch_mpq(i);
  index = mpz_get_si(mpq_numref(next));
  assert(-1 <= index && index < (int32_t)the_mpq_pool.capacity);
  return index;
}

static inline void _o_free_list_insert(int32_t i) {
  mpq_ptr insert;

  assert(0 <= i && i < the_mpq_pool.capacity);
  assert(-1 <= the_mpq_pool.start && the_mpq_pool.start < (int32_t) the_mpq_pool.capacity);

  insert = fetch_mpq(i);
  mpz_set_si(mpq_numref(insert), the_mpq_pool.start);
  the_mpq_pool.start = i;
}


/*
 * Allocate an mpq number: return the index
 */
static int32_t _o_alloc_mpq(void) {
  int32_t n;

  n = the_mpq_pool.start;
  if (n >= 0) {
    the_mpq_pool.start = _o_free_list_next(n);
  } else {
    n = the_mpq_pool.count;
    if (n >= the_mpq_pool.capacity) {
      _o_grow_mpq_pool();
    }
    the_mpq_pool.count = n + 1;
  }

  return n;
}


/*
 * Free allocated mpq number of index i
 */
void _o_free_mpq(int32_t i) {
  _o_free_list_insert(i);
}

/*
 * Init the pool (Pool API)
 */
void mpq_pool_init(void){
  init_mpq_pool();
}


/*
 * Borrow an mpq_t from the pool (Pool API)
 */
int32_t mpq_pool_borrow(mpq_ptr *q){
  int32_t i;

  get_lock(&the_mpq_pool.lock);
  i = _o_alloc_mpq();
  if (q != NULL) {
    *q = fetch_mpq(i);
  }
  release_lock(&the_mpq_pool.lock);

  return i;
}


/*
 * Return a mpq_t to the pool (Pool API)
 */
void mpq_pool_return(int32_t index){
  get_lock(&the_mpq_pool.lock);
  _o_free_mpq(index);
  release_lock(&the_mpq_pool.lock);
}

/*
 * Shutdown the pool (Pool API)
 */
void mpq_pool_shutdown(void){
  get_lock(&the_mpq_pool.lock);
  _o_free_mpq_pool();
  release_lock(&the_mpq_pool.lock);
  destroy_lock(&the_mpq_pool.lock);
}

