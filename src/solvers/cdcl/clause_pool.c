/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * CLAUSE POOL
 */
#include <stdlib.h>

#include "solvers/cdcl/clause_pool.h"
#include "utils/memalloc.h"


/*
 * Pool capacity
 */

/*
 * A pool is an array of 32bit integers and we store its size as a
 * 32bit unsigned integer. The maximal size we can use is define
 * by the following macro. We assume that SIZE_MAX is at least 2^32-1.
 *
 * This should give:
 * - MAX_ARRAY32_SIZE = 2^32/4 on 32bit machines
 * - MAX_ARRAY32_SIZE = 2^32-1 on 64bit machines
 */
#if SIZE_MAX < UINT32_MAX
#error "size_t is too small. Can't build for this platform."
#elif (SIZE_MAX/4) < UINT32_MAX
#define MAX_ARRAY32_SIZE (SIZE_MAX/4)
#else
#define MAX_ARRAY32_SIZE UINT32_MAX
#endif


/*
 * Initial and maximal capacity of a pool
 * - initial size = 1Mb
 */
#define DEF_CLAUSE_POOL_CAPACITY 262144
#define MAX_CLAUSE_POOL_CAPACITY (MAX_ARRAY32_SIZE & ~3)


/*
 * Capacity increase:
 * cap += ((cap >> 1) + (cap >> 6) + (cap >> 7) + 2048) & ~3
 *
 * Since the intiail capacity is 262144, we get an increasing
 * sequence: 262144, 401408, 613568,  ..., 4265187980,
 * which gets us close to 2^32.  The next increase after that
 * causes an arithmetic overflow.
 */
static inline uint32_t pool_cap_increase(uint32_t cap) {
  return ((cap >> 1) + (cap >> 6) + (cap >> 7) + 2048) & ~3;
}


/*
 * Maximal capacity after reset.
 * On a call to reset, we try to save memory by reducing
 * the pool capacity to this. This size is what we'd get
 * after 14 rounds on pool_cal_increase (about 126 MB).
 */
#define RESET_CLAUSE_POOL_CAPACITY 33155608



/*
 * Invariant we want to maintain
 */
#ifndef NDEBUG
static bool is_multiple_of_four(uint32_t x) {
  return (x & 3) == 0;
}

static bool clause_pool_invariant(clause_pool_t *pool) {
  return 
    pool->learned <= pool->size &&
    pool->size <= pool->capacity &&
    pool->available == pool->capacity - pool->size &&
    is_multiple_of_four(pool->learned) &&
    is_multiple_of_four(pool->size) &&
    is_multiple_of_four(pool->capacity);
}
#endif


/*
 * Global operations
 */
void init_clause_pool(clause_pool_t *pool) {
  uint32_t *tmp;

  tmp = (uint32_t *) malloc(DEF_CLAUSE_POOL_CAPACITY * sizeof(uint32_t));
  if (tmp == NULL) {
    out_of_memory();
  }

  pool->data = tmp;
  pool->learned = 0;
  pool->size = 0;
  pool->capacity = DEF_CLAUSE_POOL_CAPACITY;
  pool->available = DEF_CLAUSE_POOL_CAPACITY;

  pool->num_prob_clauses = 0;
  pool->num_prob_literals = 0;
  pool->num_learned_clauses = 0;
  pool->num_learned_literals = 0;

  assert(clause_pool_invariant(pool));
}

void delete_clause_pool(clause_pool_t *pool) {
  assert(clause_pool_invariant(pool));
  free(pool->data);
  pool->data = NULL;
}

void reset_clause_pool(clause_pool_t *pool) {
  uint32_t *tmp;

  assert(clause_pool_invariant(pool));

  if (pool->capacity > RESET_CLAUSE_POOL_CAPACITY) {
    free(pool->data);
    tmp = (uint32_t *) malloc(RESET_CLAUSE_POOL_CAPACITY * sizeof(uint32_t));
    if (tmp == NULL) {
      out_of_memory();
    }
    pool->data = tmp;
    pool->capacity = RESET_CLAUSE_POOL_CAPACITY;
  }

  pool->learned = 0;
  pool->size = 0;
  pool->available = pool->capacity;


  pool->num_prob_clauses = 0;
  pool->num_prob_literals = 0;
  pool->num_learned_clauses = 0;
  pool->num_learned_literals = 0;

  assert(clause_pool_invariant(pool));
}


/*
 * Make sure there's enough room for allocating n elements
 * - this should be called only when resize is required
 */
static void resize_clause_pool(clause_pool_t *pool, uint32_t n) {
  uint32_t min_cap, cap, increase;
  uint32_t *tmp;

  assert(clause_pool_invariant(pool));

  min_cap = pool->size + n;
  if (min_cap < n || min_cap > MAX_CLAUSE_POOL_CAPACITY) {
    // can't make the pool large enough
    out_of_memory();
  }

  cap = pool->capacity;
  do {
    increase = pool_cap_increase(cap);
    cap += increase;
    if (cap < increase) { // arithmetic overfow
      cap = MAX_CLAUSE_POOL_CAPACITY;
    }
  } while (cap < min_cap);

  tmp = (uint32_t *) realloc(pool->data, cap * sizeof(uint32_t));
  if (tmp == NULL) {
    out_of_memory();
  }

  pool->data = tmp;
  pool->capacity = cap;
  pool->available = cap - pool->size;

  assert(clause_pool_invariant(pool));
}


/*
 * Allocate an array of n integers in the pool and return its idx
 */
static cidx_t clause_pool_alloc_array(clause_pool_t *pool, uint32_t n) {
  cidx_t i;

  assert(clause_pool_invariant(pool));

  n = (n + 3) & ~3; // round up to the next multiple of 4
  if (n > pool->available) {
    resize_clause_pool(pool, n);
  }
  assert(n <= pool->available);

  i = pool->size;
  pool->size += n;
  pool->available -= n;

  assert(clause_pool_invariant(pool));

  return i;
}


/*
 * Allocate a clause of size n
 * - return its start index
 * - store the clause length
 * - update the statistics counters
 */
cidx_t clause_pool_alloc(clause_pool_t *pool, uint32_t n) {
  cidx_t i;

  i = clause_pool_alloc_array(pool, n);
  pool->data[i] = n;

  if (pool->learned == 0) {
    // problem clause
    pool->num_prob_clauses ++;
    pool->num_prob_literals += n;
  } else {
    // learned clause
    pool->num_learned_clauses ++;
    pool->num_learned_literals += n;
  }

  return i;
}


/*
 * Full size of a clause with n literals:
 * - 2 + n rounded up to the next multiple of four
 */
static inline uint32_t full_length(uint32_t n) {
  return (n + 5) & ~3;
}

/*
 * Full size of the clause that starts at index i
 */
static inline uint32_t clause_full_length(clause_pool_t *pool, uint32_t i) {
  assert(good_clause_idx(pool, i));
  return full_length(pool->data[i]);
}


/*
 * Check whether i is the start of a padding block
 */
static inline bool is_padding_start(clause_pool_t *pool, uint32_t i) {
  assert(i < pool->size && is_multiple_of_four(i));
  return pool->data[i] == 0;
}

/*
 * Length of the padding block that starts at index i
 */
static inline uint32_t padding_length(clause_pool_t *pool, uint32_t i) {
  assert(is_padding_start(pool, i));
  return pool->data[i+1];
}



/*
 * Store a padding block of size n at index i
 */
static void clause_pool_padding(clause_pool_t *pool, uint32_t i, uint32_t n) {
  uint32_t j;

  assert(i < pool->size && is_multiple_of_four(i) 
	 && is_multiple_of_four(n) && n > 0);

  j = i+n;

  if (j == pool->size) {
    // i is the last block
    pool->size = i;
    if (pool->learned == j) {
      pool->learned = i;
    }
  } else {
    if (is_padding_start(pool, j)) {
      // merge the two padding blocks
      n += padding_length(pool, j);
    }
    pool->data[i] = 0;
    pool->data[i+1] = n;
  }
}


/*
 * Delete the clause that start at index idx
 */
void clause_pool_delete(clause_pool_t *pool, cidx_t idx) {
  uint32_t n;

  assert(good_clause_idx(pool, idx) && pool->learned > 0);

  n = pool->data[idx]; // clause length
  clause_pool_padding(pool, idx, n);

  // update the statistics
  if (is_problem_clause_idx(pool, idx)) {
    assert(pool->num_prob_clauses > 0);
    assert(pool->num_prob_literals >= n);
    pool->num_prob_clauses --;
    pool->num_prob_literals -= n;
  } else {
    assert(pool->num_learned_clauses > 0);
    assert(pool->num_learned_literals >= n);
    pool->num_learned_clauses --;
    pool->num_learned_literals -= n;
  }
}


/*
 * Shrink clause idx: n = new size
 */
void clause_pool_shrink(clause_pool_t *pool, cidx_t idx, uint32_t n) {
  uint32_t old_n, old_len, new_len;

  assert(good_clause_idx(pool, idx) && pool->learned > 0 && 
	 n >= 2 && n <= clause_length(pool, idx));

  old_n = clause_length(pool, idx);
  old_len = full_length(old_n);
  new_len = full_length(n);

  assert(new_len <= old_len);
  if (new_len < old_len) {
    clause_pool_padding(pool, idx + new_len, old_len - new_len);
  }

  pool->data[idx] = n;

  if (is_problem_clause_idx(pool, idx)) {
    assert(pool->num_prob_clauses > 0);
    assert(pool->num_prob_literals >= old_n);
    pool->num_prob_literals -= (old_n - n);
  } else {
    assert(pool->num_learned_clauses > 0);
    assert(pool->num_learned_literals >= old_n);
    pool->num_learned_literals -= (old_n - n);
  }
}


/*
 * Mark the end of the problem clauses
 */
void clause_pool_end_prob_clauses(clause_pool_t *pool) {
  uint32_t s;

  assert(clause_pool_invariant(pool));

  s = pool->size;
  if (s == 0) {
    assert(pool->available >= 4);
    // add a padding block of size 4
    pool->data[0] = 0;
    pool->data[1] = 4;
    pool->size = 4;
    pool->available -= 4;
    s = 4;
  }
  pool->learned = s;
}


/*
 * Find the next clause, scanning from index i
 * - i may be the start of a clause or of a padding block
 */
static cidx_t next_clause_index(clause_pool_t *pool, cidx_t i) {
  while (i < pool->size && is_padding_start(pool, i)) {
    i += padding_length(pool, i);
  }
  return i;
}


/*
 * First clause
 */
cidx_t clause_pool_first_clause(clause_pool_t *pool) {
  return next_clause_index(pool, 0);
}


/*
 * Clause that follows idx
 */
cidx_t clause_pool_next_clause(clause_pool_t *pool, cidx_t idx) {
  assert(good_clause_idx(pool, idx));
  return next_clause_index(pool, idx + clause_full_length(pool, idx));
}
