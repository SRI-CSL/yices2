#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "memalloc.h"
#include "mpq_pool.h"
#include "mpq_aux.h"
#include "yices_locks.h"

/*
 * The major difference between mpz_pool and mpq_pool is the tuning here.
 * mpqs are much more numerous than mpzs. The latter are of the same order
 * as the number of threads.
 */
#define INITIAL_MPQ_POOL_CAPACITY 1024
#define MAX_MPQ_POOL_SIZE         (UINT32_MAX/sizeof(mpq_t))
#define MPQ_BLOCK_SIZE            1024

// undefine for helgrinding; define for debugging 
//#define POOL_DEBUG 

typedef struct mpq_pool_block *mpq_pool_block_ptr;

/* our pool will be a linked list of mpq_pool_block_t blocks; so we never worry about realloc issues */
typedef struct mpq_pool_block {
  mpq_pool_block_ptr next;
  mpq_t*             bank;
} mpq_pool_block_t;

typedef struct mpq_pool {
  yices_lock_t        lock;         /* a lock protecting the pool                        */
  mpq_pool_block_ptr  block;        /* the initial block                                 */
  mpq_pool_block_ptr  last_block;   /* the last block  (for appending)                   */
  uint32_t            block_count;  /* the current number of blocks                      */
  uint32_t            capacity;     /* the capacity (length of) the pool array           */
  uint32_t            count;        /* the current number of mpqs in use                 */
  int32_t             start;        /* the start of the free list  (BD's trick)          */
} mpq_pool_t;

/*  the prefix _o_ indicates that the calling thread *MUST* own the the_mpq_pool.lock already    */

static mpq_pool_t the_mpq_pool;

/*
 * Allocate a pool block
 */
static mpq_pool_block_t* alloc_mpq_pool_block(void){
  uint32_t i;

  mpq_pool_block_t* retval  = (mpq_pool_block_t *) safe_malloc(sizeof(mpq_pool_block_t));

  retval->next = NULL;

  retval->bank = (mpq_t *) safe_malloc(MPQ_BLOCK_SIZE * sizeof(mpq_t));

  for(i = 0; i < MPQ_BLOCK_SIZE; i++){
    mpq_init2(retval->bank[i], 64);
  }

  return retval;
}

/*
 * Initialize the pool
 */
static int32_t init_mpq_pool(void){

  create_yices_lock(&(the_mpq_pool.lock));

  the_mpq_pool.block = alloc_mpq_pool_block();
  the_mpq_pool.last_block = the_mpq_pool.block;
  the_mpq_pool.block_count = 1;
  the_mpq_pool.capacity = MPQ_BLOCK_SIZE;
  the_mpq_pool.count = 0;
  the_mpq_pool.start = -1;

  return 0;

}

/*
 * Fetch an mpq number by its index i  (the assert could fail because of a write to the_mpq_pool.block_count by another thread)
 */
mpq_ptr fetch_mpq(int32_t i) {
  int32_t block_id = i / MPQ_BLOCK_SIZE;
  int32_t index = i % MPQ_BLOCK_SIZE;

#ifdef POOL_DEBUG
  assert(0 <= block_id && block_id < the_mpq_pool.block_count);
#endif

  mpq_pool_block_ptr  block = the_mpq_pool.block;
  while(block_id > 0){
    block = block->next;
    block_id--;
  }
  return block->bank[index];
}

/*
 * Add a new block to the pool
 */
static int32_t _o_grow_mpq_pool(void){
  mpq_pool_block_t* new_block;
  int32_t new_capacity = the_mpq_pool.capacity + MPQ_BLOCK_SIZE;

  if (  new_capacity >= MAX_MPQ_POOL_SIZE ) {
    out_of_memory();
  }

  new_block = alloc_mpq_pool_block();

  the_mpq_pool.last_block->next = new_block;
  the_mpq_pool.last_block = new_block;

  the_mpq_pool.block_count += 1;
  the_mpq_pool.capacity = new_capacity;

  return 0;
}

/*
 * Reclaim a pool block
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
 */
static void _o_free_mpq_pool_blocks(void){
  mpq_pool_block_t* current_block  = the_mpq_pool.block;
  while(current_block != NULL){
    mpq_pool_block_t* next = current_block->next;
    _o_free_mpq_pool_block( current_block );
    free ( current_block );
    current_block = next;
  }
}

/*
 * Reclaim the pool. N.B. any use of the pool after this will lead to tears
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
 *
 */
static inline int32_t _o_free_list_next(int32_t i) {
  int32_t index;
  mpq_ptr next = fetch_mpq(i);
  index = mpz_get_si(mpq_numref(next));
  assert(-1 <= index && index < (int32_t)the_mpq_pool.capacity);
  return index;
}

static inline void _o_free_list_insert(int32_t i) {
  assert(0 <= i && i < the_mpq_pool.capacity);
  assert(-1 <= the_mpq_pool.start && the_mpq_pool.start < (int32_t) the_mpq_pool.capacity);
  mpq_ptr insert = fetch_mpq(i);
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
    assert(-1 <= the_mpq_pool.start && the_mpq_pool.start < (int32_t) the_mpq_pool.capacity);
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
int32_t mpq_pool_init(void){

  if(init_mpq_pool() != 0){
    fprintf(stderr, "mpq_pool_init: init_mpq_pool failed\n");
    return -1;
  }


  return 0;
}


/*
 * Borrow an mpq_t from the pool (Pool API)
 */
int32_t mpq_pool_borrow(int32_t* indexp, mpq_ptr* qp){
  int32_t index;

  get_yices_lock(&(the_mpq_pool.lock));

  index = _o_alloc_mpq();
  *indexp = index;
  if(qp != NULL){
    *qp = fetch_mpq(index);
  }

  release_yices_lock(&(the_mpq_pool.lock));

  return 0;

}

/*
 * Return a mpq_t to the pool (Pool API)
 */
int32_t mpq_pool_return(int32_t index){

  get_yices_lock(&(the_mpq_pool.lock));

  _o_free_mpq(index);

  release_yices_lock(&(the_mpq_pool.lock));

  return 0;
}

/*
 * Shutdown the pool (Pool API)
 */
int32_t mpq_pool_shutdown(void){

  get_yices_lock(&(the_mpq_pool.lock));

  _o_free_mpq_pool();

  release_yices_lock(&(the_mpq_pool.lock));

  destroy_yices_lock(&(the_mpq_pool.lock));

  return 0;
}

