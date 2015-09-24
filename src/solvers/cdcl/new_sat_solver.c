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
}

static void delete_clause_pool(clause_pool_t *pool) {
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

  min_cap = pool->size + n;
  if (min_cap < n || min_cap > MAX_CLAUSE_POOL_CAPACITY) {
    // can't make the pool large enough
    out_of_memory();
  }

  /*
   * cap is initially 262144.
   *
   * In each iteration of the loop we do
   *   cap += ((cap >> 1) + (cap >> 6) + (cap >> 7) + 2048) & ~3U
   *
   * This forms the series: 262144, 401408, 613568. ..., 4265187980,
   * which gets us close to 2^32-1.  The next iteration after that
   * causes an arithmetic overflow.
   */
  cap = pool->capacity;
  do {
    increase = ((cap >> 1) + (cap >> 6) + (cap >> 7) + 2048) & ~3U;
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
}


/*
 * Allocate an array of n integers in the pool and return its idx
 */
static cidx_t clause_pool_alloc(clause_pool_t *pool, uint32_t n) {
  cidx_t i;

  n = (n + 3) & ~3; // round up to the next multiple of 4
  if (n > pool->available) {
    resize_clause_pool(pool, n);
  }
  assert(n <= pool->available);

  i = pool->size;
  pool->size += n;
  pool->available -= n;

  return i;
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
