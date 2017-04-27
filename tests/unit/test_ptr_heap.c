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

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>

#include "utils/ptr_heap.h"


#ifdef MINGW

/*
 * random() does not exist on mingw but rand() does
 */
static inline int random(void) {
  return rand();
}

#endif


/*
 * Elements to store in the heap are pairs of integers
 */
typedef struct pair_s {
  int32_t first;
  int32_t second;
} pair_t;


/*
 * Test data
 */
#define TEST_SIZE 200

static pair_t test[TEST_SIZE];


/*
 * Heap
 */
static ptr_heap_t heap;



/*
 * Comparison = lexicographic ordering on pairs
 */
static bool compare(pair_t *p1, pair_t *p2) {
  return p1->first < p2->first || (p1->first == p2->first && p1->second <= p2->second);
}


/*
 * Print pair p
 */
static void print_pair(pair_t *p) {
  printf("(%2"PRId32", %2"PRId32")\n", p->first, p->second);
}


/*
 * Initialize test data with n random elements
 */
static void init_test_data(uint32_t n) {
  uint32_t i;

  assert(n <= TEST_SIZE);

  for (i=0; i<n; i++) {
    test[i].first = random() % 50;
    test[i].second = random() % 50;
  }
}


/*
 * Initialize test data with n equal elements
 */
static void init_test_data_constant(uint32_t n) {
  uint32_t i;
  int32_t x, y;

  assert(n <= TEST_SIZE);
  x = random() % 50;
  y = random() % 50;

  for (i=0; i<n; i++) {
    test[i].first = x;
    test[i].second = y;
  }
}



/*
 * Run a single test: n = size
 * - add test data to the heap
 * - extract all elements from the heap and print them
 */
static void run_test(uint32_t n) {
  pair_t *p, *q;
  uint32_t i;

  for (i=0; i<n; i++) {
    ptr_heap_add(&heap, test + i);
  }

  // extract the data
  q = NULL;
  i = 0;
  for (;;) {
    p = ptr_heap_get_min(&heap);
    if (p == NULL) break;
    print_pair(p);
    if (q != NULL && ! compare(q, p)) {
      printf("*** BUG: incorrect heap order ***\n");
    }
    q = p;
    i ++;
  }

  assert(i == n);
}



/*
 * Run some tests
 */
int main(void) {
  uint32_t i;

  init_ptr_heap(&heap, 0, (ptr_heap_cmp_fun_t) compare);
  for (i=0; i<10; i++) {
    printf("\n=== Test %"PRIu32" ===\n", i);
    init_test_data(i);
    run_test(i);
    assert(ptr_heap_is_empty(&heap));
  }

  for (i=10; i<20; i++) {
    printf("\n=== Test %"PRIu32" ===\n", i);
    init_test_data(20);
    run_test(20);
    assert(ptr_heap_is_empty(&heap));
  }


  for (i=20; i<30; i++) {
    printf("\n=== Test %"PRIu32" ===\n", i);
    init_test_data_constant(6);
    run_test(6);
    assert(ptr_heap_is_empty(&heap));
  }


  for (i=30; i<50; i++) {
    printf("\n=== Test %"PRIu32" ===\n", i);
    init_test_data(200);
    run_test(200);
    assert(ptr_heap_is_empty(&heap));
  }


  delete_ptr_heap(&heap);

  return 0;
}
