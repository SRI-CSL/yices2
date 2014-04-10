#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "memalloc.h"
#include "mpz_pool.h"
#include "mpq_aux.h"
#include "yices_locks.h"

/*
 * The major difference between mpz_pool and mpq_pool is the tuning here.
 * mpqs are much more numerous than mpzs. The latter are of the same order
 * as the number of threads.
 */
#define INITIAL_MPZ_POOL_CAPACITY 64
#define MAX_MPZ_POOL_SIZE         (UINT32_MAX/sizeof(mpz_t))
#define MPZ_BLOCK_SIZE            64

typedef struct mpz_pool_block *mpz_pool_block_ptr;

/* our pool will be a linked list of mpz_pool_block_t blocks; so we never worry about realloc issues */
typedef struct mpz_pool_block {
  mpz_pool_block_ptr next;
  mpz_t*             bank;
} mpz_pool_block_t;

typedef struct mpz_pool {
  yices_lock_t        lock;         /* a lock protecting the pool                        */
  mpz_pool_block_ptr  block;        /* the initial block                                 */
  mpz_pool_block_ptr  last_block;   /* the last block  (for appending)                   */
  uint32_t            block_count;  /* the current number of blocks                      */
  uint32_t            capacity;     /* the capacity (length of) the pool array           */
  uint32_t            count;        /* the current number of mpqs in use                 */
  int32_t             start;        /* the start of the free list  (BD's trick)          */
} mpz_pool_t;

/*  the prefix _o_ indicates that the calling thread *MUST* own the the_mpz_pool.lock already    */

static mpz_pool_t the_mpz_pool;

/*
 * Allocate a pool block
 */
static mpz_pool_block_t* alloc_mpz_pool_block(void){
  uint32_t i;

  mpz_pool_block_t* retval  = (mpz_pool_block_t *) safe_malloc(sizeof(mpz_pool_block_t));

  retval->next = NULL;

  retval->bank = (mpz_t *) safe_malloc(MPZ_BLOCK_SIZE * sizeof(mpz_t));

  for(i = 0; i < MPZ_BLOCK_SIZE; i++){
    mpz_init2(retval->bank[i], 64);
  }

  return retval;
}

/*
 * Initialize the pool
 */
static int init_mpz_pool(void){

  create_yices_lock(&(the_mpz_pool.lock));

  the_mpz_pool.block = alloc_mpz_pool_block();
  the_mpz_pool.last_block = the_mpz_pool.block;
  the_mpz_pool.block_count = 1;
  the_mpz_pool.capacity = MPZ_BLOCK_SIZE;
  the_mpz_pool.count = 0;
  the_mpz_pool.start = -1;

  return 0;

}

/*
 * Fetch an mpz number by its index i
 */
mpz_ptr fetch_mpz(int32_t i) {
  int32_t block_id = i / MPZ_BLOCK_SIZE;
  int32_t index = i % MPZ_BLOCK_SIZE;

  assert(0 <= block_id && block_id < the_mpz_pool.block_count);

  mpz_pool_block_ptr  block = the_mpz_pool.block;
  while(block_id > 0){
    block = block->next;
    block_id--;
  }
  return block->bank[index];
}

/*
 * Add a new block to the pool
 */
static int _o_grow_mpz_pool(void){
  mpz_pool_block_t* new_block;
  int32_t new_capacity = the_mpz_pool.capacity + MPZ_BLOCK_SIZE;

  if (  new_capacity >= MAX_MPZ_POOL_SIZE ) {
    out_of_memory();
  }

  new_block = alloc_mpz_pool_block();

  the_mpz_pool.last_block->next = new_block;
  the_mpz_pool.last_block = new_block;

  the_mpz_pool.block_count += 1;
  the_mpz_pool.capacity = new_capacity;

  return 0;
}

/*
 * Reclaim a pool block
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
 */
static void _o_free_mpz_pool_blocks(void){
  mpz_pool_block_t* current_block  = the_mpz_pool.block;
  while(current_block != NULL){
    mpz_pool_block_t* next = current_block->next;
    _o_free_mpz_pool_block( current_block );
    free ( current_block );
    current_block = next;
  }
}

/*
 * Reclaim the pool. N.B. any use of the pool after this will lead to tears
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
 *
 */
static inline int32_t _o_free_list_next(int32_t i) {
  mpz_ptr next = fetch_mpz(i);
  return mpz_get_si(next);
}

static inline void _o_free_list_insert(int32_t i) {
  assert(0 <= i && i < the_mpz_pool.capacity);
  assert(-1 <= the_mpz_pool.start && the_mpz_pool.start < (int32_t) the_mpz_pool.capacity);
  mpz_ptr insert = fetch_mpz(i);
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
    assert(-1 <= the_mpz_pool.start && the_mpz_pool.start < (int32_t) the_mpz_pool.capacity);
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
int mpz_pool_init(void){

  if(init_mpz_pool() != 0){
    fprintf(stderr, "mpz_pool_init: init_mpz_pool failed\n");
    return -1;
  }


  return 0;
}


/*
 * Borrow an mpz_t from the pool (Pool API)
 */
int mpz_pool_borrow(int32_t* indexp,  mpz_ptr* zp){
  int32_t index;

  get_yices_lock(&(the_mpz_pool.lock));

  index = _o_alloc_mpz();
  *indexp = index;
  if(zp != NULL){
    *zp = fetch_mpz(index);
  }

  release_yices_lock(&(the_mpz_pool.lock));

  return 0;

}

/*
 * Return a mpz_t to the pool (Pool API)
 */
int mpz_pool_return(int32_t index){

  get_yices_lock(&(the_mpz_pool.lock));

  _o_free_mpz(index);

  release_yices_lock(&(the_mpz_pool.lock));

  return 0;
}

/*
 * Shutdown the pool (Pool API)
 */
int mpz_pool_shutdown(void){

  get_yices_lock(&(the_mpz_pool.lock));

  _o_free_mpz_pool();

  release_yices_lock(&(the_mpz_pool.lock));

  destroy_yices_lock(&(the_mpz_pool.lock));

  return 0;
}

