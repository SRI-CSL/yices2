/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SPARSE ARRAYS FOR REGISTERING ROOTS
 */

/*
 * For garbage collection, we must keep track of root terms and types (i.e.,
 * terms and types that the application wants to keep).
 *
 * For this purpose, we use reference counting. When a term/type is registered
 * as a root, we increment a counter for this term/type. We store the counts
 * in a sparse array structure.
 *
 * The array is divided in blocks of equal size
 * (block size = 64 for now) and we use one bit per block to record whether
 * the block is used or not.
 * - a block marked as dirty, is not initialized and its content shouldn't be read
 * - if a block is clean then all elements in the block have a valid value
 * - a block is initialized (all elements set to 0) on the first write into
 *   that block
 *
 * So the reference count for i is 0 if i is in a dirty block or
 * a->data[i] otherwise.  We keep track of the total number of roots (i.e.,
 * the number of i such that refcount for i is positive) in a->nelems.
 *
 * Overflow of a->data[i] is unlikely, but we take care of it anyway:
 * - if a->data[i] reaches UINT32_MAX then the ref counter is frozen
 *   incrementing or decrementing the ref counter for i does nothing.
 */

#ifndef __SPARSE_ARRAYS_H
#define __SPARSE_ARRAYS_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "utils/bitvectors.h"


/*
 * Data structure:
 * - data = the array proper
 * - clean = bit vector for marks:
 *   block i is dirty if clean[i] is 0
 *   block i is clean if clean[i] is 1
 * - nblocks = number of blocks
 * - nelems = number of elements i such that a[i] > 0
 */
typedef struct sparse_array_s {
  uint32_t *data;
  byte_t *clean;
  uint32_t nblocks;
  uint32_t nelems;
} sparse_array_t;


/*
 * Block size: must be a power of two
 */
#define BSIZE_NBITS 6u
#define BSIZE (1u<<BSIZE_NBITS)


/*
 * Default array size = 32 blocks
 */
#define DEF_SPARSE_ARRAY_NBLOCKS 32u
#define DEF_SPARSE_ARRAY_SIZE (DEF_SPARSE_ARRAY_NBLOCKS * BSIZE)


/*
 * Maximal number of blocks: block indices are in [0, MAX_NBLOCKS - 1]
 */
#define MAX_SPARSE_ARRAY_SIZE (UINT32_MAX/sizeof(uint32_t))
#define MAX_NBLOCKS ((MAX_SPARSE_ARRAY_SIZE>>BSIZE_NBITS) + 1)


// block in which index i resides
static inline uint32_t block_of_index(uint32_t i) {
  return i >> BSIZE_NBITS;
}

// start and end indices of block k
static inline uint32_t block_start(uint32_t k) {
  assert(k < MAX_NBLOCKS);
  return k << BSIZE_NBITS;
}

static inline uint32_t block_end(uint32_t k) {
  return block_start(k) + (BSIZE - 1);
}



/*
 * MAIN OPERATIONS
 */

/*
 * Initialize a:
 * - n = minimal size requested (number of elements in a)
 * - if n is 0, the default size is used
 * - all blocks are marked as dirty
 */
extern void init_sparse_array(sparse_array_t *a, uint32_t n);


/*
 * Delete: free all memory
 */
extern void delete_sparse_array(sparse_array_t *a);


/*
 * Reset: mark all blocks as dirty
 */
extern void reset_sparse_array(sparse_array_t *a);


/*
 * Increment the ref counter a[i]
 */
extern void sparse_array_incr(sparse_array_t *a, uint32_t i);


/*
 * Decrement a[i]: the ref counter must be positive (so i must be in a clean block).
 */
extern void sparse_array_decr(sparse_array_t *a, uint32_t i);


/*
 * Get the ref counter for i
 * - return 0 if i is in a dirty block or outside a->data
 */
extern uint32_t sparse_array_read(sparse_array_t *a, uint32_t i);


/*
 * ITERATOR
 */

/*
 * Call f(aux, i) for all elements of a such that a[i] > 0
 */
typedef void (*sparse_array_iterator_t)(void *aux, uint32_t i);

extern void sparse_array_iterate(sparse_array_t *a, void *aux, sparse_array_iterator_t f);



#endif /* __SPARSE_ARRAYS_H */
