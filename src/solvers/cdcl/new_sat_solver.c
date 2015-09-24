/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * STAND-ALONE SAT SOLVER
 */
#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>

#include "solvers/cdcl/new_sat_solver.h"
#include "utils/memalloc.h"


/*
 * CLAUSE POOL
 */

/*
 * Initial capacity of a pool = 262144 elements = 1 Mb.
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

static void init_clause_pool(clause_pool_t *pool) {
  uint32_t *tmp;

  tmp = (uint32_t *) malloc(DEF_CLAUSE_POOL_CAPACITY);
  if (tmp == NULL) {
    out_of_memory();
  }

  pool->data = tmp;
  pool->learned = 0;
  pool->size = 0;
  pool->capacity = DEF_CLAUSE_POOL_CAPACITY;
  pool->available = DEF_CLAUSE_POOL_CAPACITY;

  assert(clause_pool_invariant(pool));
}

static void delete_clause_pool(clause_pool_t *pool) {
  assert(clause_pool_invariant(pool));
  free(pool->data);
  pool->data = NULL;
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

  tmp = (uint32_t *) realloc(pool->data, cap);
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
static cidx_t clause_pool_alloc(clause_pool_t *pool, uint32_t n) {
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
 * Add a clause of n literals to the pool:
 * - l[0 ... n-1] = the literals
 * - return the clause idx
 * There must not be duplicates or complementary literals in l
 */
static cidx_t clause_pool_add_clause(clause_pool_t *pool, uint32_t n, literal_t *l) {
  clause_t *clause;
  cidx_t cidx;
  uint32_t i;

  assert(n <= MAX_CLAUSE_SIZE);

  cidx = clause_pool_alloc(pool, n+2);
  clause = clause_of_idx(pool, cidx);
  clause->len = n;
  clause->aux.d = 0;
  for (i=0; i<n; i++) {
    clause->c[i] = l[i];
  }
  return cidx;
}



/*
 * Test this
 */
void clause_pool_test(void) {
  clause_pool_t pool;
  uint32_t i, idx, n;

  init_clause_pool(&pool);

  i = 0;
  n = 3;
  for (i=0; i<1000; i++) {
    idx = clause_pool_alloc(&pool, n);
    printf("clause_pool_alloc: size = %"PRIu32", cidx = %"PRIu32", cap = %"PRIu32"\n",
	   n, idx, pool.capacity);
    n += (n >> 1) + 1;
    if (pool.capacity >= 4265187980) {
      if (n > (UINT32_MAX/20)) {
	n = 20;
      }
    } else {
      if (n > (UINT32_MAX/5)) {
	n = 5;
      }
    }
  }

  delete_clause_pool(&pool);
}
