/*
 * SPARSE ARRAYS
 */

/*
 * A sparse array stores an integer array indexed from 0 to n-1 where
 * n may be large but we assume that most elements are never written
 * or read.
 *
 * To support this, we divide the array in consecutive blocks of equal size
 * (block size = 64 for now) and we use one bit per block to record whether
 * the block is used or not.
 * - a block marked as dirty, is not initialized and its content shouldn't be read
 * - if a block is clean then all elements in the block have a valid value
 * - a block is initialized (all elements set to 0) on the first write into
 *   that block
 */

#ifndef __SPARSE_ARRAYS_H
#define __SPARSE_ARRAYS_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "bitvectors.h"


/*
 * Data structure:
 * - data = the array proper
 * - dirty = bit vector for the dirty bits
 * - nblocks = number of blocks
 */
typedef struct sparse_array_s {
  uint32_t *data;
  byte_t *dirty;
  uint32_t nblocks;
} sparse_array_t;


/*
 * Block size: must be a power of two
 */
#define BSIZE_NBITS 6u
#define BSIZE (1u<<BSIZE_NBITS)


/*
 * Default array size = 32 blocks
 */
#define DEF_SPARSE_ARRAY_SIZE (32 * BSIZE)


/*
 * Maximal number of blocks: block indices are in [0, MAX_NBLOCKS - 1]
 */
#define MAX_NBLOCKS ((UINT32_MAX>>BSIZE_NBITS) + 1)

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
 * - n = minimal size requested
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
 * Store x into a[i]:
 * - resize the array if necessary
 * - initialize i's block if that block is dirty: all elements are set to 0
 * - then store x
 */
extern void sparse_array_write(sparse_array_t *a, uint32_t i, uint32_t x);


/*
 * Read the value mapped to i:
 * - return 0 if i is in a dirty block or outside the array
 */
extern uint32_t sparse_array_read(sparse_array_t *a, uint32_t i);


/*
 * Increment a[i]:
 * - if i is in a dirty block, this has the same behavior 
 *   as writing '1' in a[i]
 */
extern void sparse_array_incr(sparse_array_t *a, uint32_t i);


/*
 * Decrement a[i]
 * - if i is in a dirty block, this write UINT32_MAX in a[i]
 */
extern void sparse_array_decr(sparse_array_t *a, uint32_t i);


/*
 * Check whether i is in a clean block (i.e., value[i] is defined)
 */
extern bool sparse_array_clean_idx(sparse_array_t *a, uint32_t i);



/*
 * ITERATOR
 */

/*
 * Call f(aux, i) for all elements of a such that a[i] > 0
 */
typedef void (*sparse_array_iterator_t)(void *aux, uint32_t i);

extern void sparse_array_iterate_pos(sparse_array_t *a, void *aux, sparse_array_iterator_t f);



#endif /* __SPARSE_ARRAYS_H */
