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
 * CLAUSE POOL
 */

#ifndef __CLAUSE_POOL_H
#define __CLAUSE_POOL_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "solvers/cdcl/sat_solver_base_types.h"


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
 *     learned, size, capacity, available are all multiple of four.
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
 * - several calls to add_problem_clause
 * - then calls to add_learned_clause
 */

/*
 * Add a problem or learned clause:
 * - n = number of literals
 * - a[0 ... n-1] = literals
 *
 * These function update the statistics and return the start index of the new clause.
 * - the clause's auxiliary data is initialized to 0
 */
extern cidx_t clause_pool_add_problem_clause(clause_pool_t *pool, uint32_t n, const literal_t *a);
extern cidx_t clause_pool_add_learned_clause(clause_pool_t *pool, uint32_t n, const literal_t *a);

/*
 * Delete the clause that starts at index idx
 * - idx must be a valid clause start
 */
extern void clause_pool_delete_clause(clause_pool_t *pool, cidx_t idx);

/*
 * Shrink the clause that starts at index idx to size n
 * - idx must be a valid clause start
 * - n must be more than two and less than or equal to the clause's current length
 */
extern void clause_pool_shrink_clause(clause_pool_t *pool, cidx_t idx, uint32_t n);



/*
 * ACCESS CLAUSE COMPONENTS
 */

/*
 * Check whether idx is a problem or a learned clause.
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


/*
 * Pointer to the beginning of clause cidx
 */
static inline uint32_t *clause_start(clause_pool_t *pool, cidx_t idx) {
  assert(good_clause_idx(pool, idx));
  return pool->data + idx;
}


/*
 * SCAN CLAUSES
 */

/*
 * First (problem) clause:
 * - returns pool->size if there are no clauses
 */
extern cidx_t clause_pool_first_clause(clause_pool_t *pool);

/*
 * First learned clause
 * - returns pool->size if there are no learned clauses
 */
extern cidx_t clause_pool_first_learned_clause(clause_pool_t *pool);

/*
 * Clause that follows idx
 * - this returns pool->size if idx is the last clause
 */
extern cidx_t clause_pool_next_clause(clause_pool_t *pool, cidx_t idx);



#endif /* __CLAUSE_POOL_H */
