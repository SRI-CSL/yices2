/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of clause-pool alloc
 */

#include <stdio.h>
#include <inttypes.h>

#include "solvers/cdcl/clause_pool.h"

static void clause_pool_test(void) {
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

int main(void) {
  clause_pool_test();
  return 0;
}
