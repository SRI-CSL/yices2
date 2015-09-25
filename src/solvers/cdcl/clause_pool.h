/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * CLAUSE POOL
 */

#ifndef __CLAUSE_POOL_H
#define __CLAUSE_POOL_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

/*
 * Clauses are stored in a big array of integers.
 *
 * Each clause consists of
 * - header: clause length + auxiliary data
 * - for a learned clause, the auxiliary data is the clause's activity.
 * - for a problem clause, the auxiliary data is a bitmask to accelerate
 *   subsumption checks.
 * - the rest is an array of literals
 * - the first two elements of this array are the watched literals.
 *
 * The pool is divided into three regions:
 * - data[0 ... learned-1]           contains the problem clauses
 * - data[learned_base ... size - 1] contains the learned clauses
 * - data[size ... capacity-1]       unused
 *
 * Each clause is identified by an index i:
 * - data[i]   is the clause length
 * - data[i+1] is the auxiliary data
 * - data[i+2] is the first watched literal
 * - data[i+3] is the second watched literal
 * - data[i+4 ... i+n+2] = rest of the clause = array of n-2 literals
 *   where n = data[i] = clause length.
 *
 * Each clause starts at an index that's a multiple of 4. This ensures
 * that header + two watched literals are in the same cache line
 * (CHECK THIS). 
 *
 * If a clause starts at index i, the next clause starts
 * at index j = ((i + data[i] + 2 + 3) & ~3). That's i + length of the
 * clause + size of the header rounded up to the next multiple of 4.
 *
 * Simplification/in-processing may delete or shrink a clause. This
 * introduces gaps in the data array.  To deal with these gaps, we add
 * padding blocks. A padding block at index i is a block of unused
 * elements in the array.  Its length is a multiple of four.  The
 * first two elements of a padding block are as follows: 
 * - data[i] = 0
 * - data[i+1] = length of the padding block.
 * This distinguishes padding blocks from clauses since a clause starts with 
 * data[i] >= 2.
 */


/*
 * Pool structure:
 * - data = where clauses are stored
 * - learned/size/capacity = integer indices that delimit the
 *   three regions
 * - available = number elements in the unused region
 * - counters to keep track of the number and total size of the
 *   clauses.
 *
 * - invariants:
 *     learned <= size <= capacity
 *     available = capacity - size
 *     learned, size, capacity, available are all mutiple of four.
 */
typedef struct clause_pool_s {
  uint32_t *data;
  uint32_t learned;
  uint32_t size;
  uint32_t capacity;
  uint32_t available;
  //  statistics
  uint32_t num_prob_clauses;      // number of problem clauses
  uint32_t num_prob_literals;     // sum of the length of these clauses
  uint32_t num_learned_clauses;   // number of learned clauses
  uint32_t num_learned_literals;  // sum of the length of these clauses
} clause_pool_t;


// clause index
typedef uint32_t cidx_t;



/*
 * GLOBAL OPERATIONS
 */

/*
 * Initialize: the initial size is 1Mb (2662144 elements)
 * Fails and calls 'out_of_memory()' if we can't allocate the initial array.
 */
extern void init_clause_pool(clause_pool_t *pool);

/*
 * Reset: empty the pool
 */
extern void reset_clause_pool(clause_pool_t *pool);

/*
 * Free memory
 */
extern void delete_clause_pool(clause_pool_t *pool);


/*
 * CLAUSE ALLOCATION/DELETION
 */

/*
 * The intended use is:
 * - init_clause_pool(pool)
 * - calls to clause_pool_alloc for the problem clauses.
 * - clause_pool_end_prob_clauses(pool)
 * - calls to clause_pool_alloc for the learned clauses.
 */

/*
 * Allocate an array of n integers in the pool and return its starts index
 * - store the length n in the first element of the array
 * - update the statistics: the new clause is considered to be a learned clause
 *   if pool->learned is positive. 
 *
 * If we're out of memory, this function fails and calls the exit function
 * 'out_of_memory' defined in utils/memalloc.c
 */
extern cidx_t clause_pool_alloc(clause_pool_t *pool, uint32_t n);

/*
 * Mark the end of the problem clauses:
 * - this sets pool->learned to a positive value
 * - corner case: if there are no problem clauses stored when
 *   this function is called, we add a padding block of size 4
 *   to force pool->learned to be positive.
 */
extern void clause_pool_end_prob_clauses(clause_pool_t *pool);

/*
 * Delete the clause that starts at index idx
 * - idx must be a valid clause start
 * - this function must not be called before clause_pool_end_prob_clause
 */
extern void clause_pool_delete(clause_pool_t *pool, cidx_t idx);

/*
 * Shrink the clause that starts at index idx to size n
 * - idx must be a valid clause start
 * - n must be more than two and less than or equal to the clause's current length
 * - this function must not be called before clause_pool_end_prob_clause
 */
extern void clause_pool_shrink(clause_pool_t *pool, cidx_t idx, uint32_t n);



/*
 * SCAN CLAUSES
 */

/*
 * First clause:
 * - returns pool->size if there are no clauses
 */
extern cidx_t clause_pool_first_clause(clause_pool_t *pool);

/*
 * Clause that follows idx
 * - this returns pool->size if idx is the last clause
 */
extern cidx_t clause_pool_next_clause(clause_pool_t *pool, cidx_t idx);


/*
 * Check whether idx is a problem or a learned clause.
 * These functions assume that clause_pool_end_prob_clauses has been
 * called.
 */
#ifndef NDEBUG
static inline bool good_clause_idx(clause_pool_t *pool, cidx_t idx) {
  return ((idx & 3) == 0) && idx < pool->size;
}
#endif

static inline bool is_problem_clause_idx(clause_pool_t *pool, cidx_t idx) {
  assert(good_clause_idx(pool, idx) && pool->learned > 0);
  return  idx < pool->learned;  
}

static inline bool is_learned_clause_idx(clause_pool_t *pool, cidx_t idx) {
  assert(good_clause_idx(pool, idx) && pool->learned > 0);
  return  idx >= pool->learned;
}


/*
 * Number of literals in clause
 */
static inline uint32_t clause_length(clause_pool_t *pool, cidx_t idx) {
  assert(good_clause_idx(pool, idx));
  return pool->data[idx];
}


#endif /* __CLAUSE_POOL_H */
