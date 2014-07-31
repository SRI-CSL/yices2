/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of the arrays with push/pop
 */

#include <inttypes.h>
#include <stdio.h>
#include <stdbool.h>

#include "utils/backtrack_arrays.h"
#include "utils/memalloc.h"


#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif



/*
 * Test arrays:
 * - each array is randomly constructed
 * - size[i] = its length
 * - array[i] = the array proper
 *   each element in array i is a pair (index, value)
 */
typedef struct test_elem_s {
  int32_t index;
  uint8_t value;
} test_elem_t;


#define NUM_ARRAYS 50

static uint32_t size[NUM_ARRAYS];
static test_elem_t *array[NUM_ARRAYS];


/*
 * Initialize n arrays with random data
 * - each array contains 20 pairs (index, value)
 * - indices are in the range [0 ... m-1]
 * - values  are in the range [1 ... 255]
 */
static void init_arrays(uint32_t n, uint32_t m) {
  test_elem_t *a;
  uint32_t i, j;

  assert(n <= NUM_ARRAYS && m > 0);

  for (i=0; i<n; i++) {
    a = (test_elem_t *) safe_malloc(20 * sizeof(test_elem_t));
    size[i] = 20;
    for (j=0; j<20; j++) {
      a[j].index = ((int32_t) random()) % m;
      a[j].value = 1 + ((uint8_t) (random() & 0xFF));
    }
    array[i] = a;
  }
}


/*
 * Delete array[0] ... array[n-1]
 */
static void delete_arrays(uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    safe_free(array[i]);
  }
}



/*
 * Get the largest index in array[0] ... array[n]
 */
static int32_t max_index(uint32_t n) {
  uint32_t i, j, p;
  test_elem_t *a;
  int32_t max;

  max = -1;
  for (i=0; i <= n; i++) {
    p = size[i];
    a = array[i];
    for (j=0; j<p; j++) {
      if (a[j].index > max) {
	max = a[j].index;
      }
    }
  }

  return max;
}


/*
 * Build an expanded array from the data in array[0] ... array[n-1]
 * - m = size of the expanded array
 */
static uint8_t *expand_arrays(uint32_t n, uint32_t m) {
  uint8_t *tmp;
  test_elem_t *a;
  uint32_t i, j, p;
  int32_t idx;

  tmp = (uint8_t *) safe_malloc(m * sizeof(uint8_t));
  for (i=0; i<m; i++) {
    tmp[i] = 0; // default value
  }

  for (i=0; i <= n; i++) {
    p = size[i];
    a = array[i];
    for (j=0; j<p; j++) {
      idx = a[j].index;
      if (idx < m) {
	tmp[idx] = a[j].value;
      }
    }
  }

  return tmp;
}


/*
 * Check whether backtrackable array b matches expanded array a
 * - m = size of a
 */
static bool equal_array(uint8_t *a, uint32_t m, uint8_array_t *b) {
  uint32_t i;

  for (i=0; i<m; i++) {
    if (a[i] != au8_read(b, i)) {
      return false;
    }
  }

  return true;
}


/*
 * Store array a into b
 * - n = number of records in a
 */
static void write_array(test_elem_t *a, uint32_t n, uint8_array_t *b) {
  uint32_t i;

  for (i=0; i<n; i++) {
    au8_write(b, a[i].index, a[i].value);
  }
}



/*
 * Print array a:
 * - n = number of record in a
 */
static void print_test_array(test_elem_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    printf(" a[%"PRId32"] := %"PRIu8"\n", a[i].index, a[i].value);
  }
}


/*
 * Print content of array b
 */
static void print_backtrackable_array(uint8_array_t *b) {
  uint32_t i, top;

  top = b->top;
  for (i=0; i<top; i++) {
    if (b->map[i] > 0) {
      printf(" b[%"PRId32"] = %"PRIu8"\n", i, b->map[i]);
    }
  }
}


/*
 * Print expanded array a of m elements
 */
static void print_expanded_array(uint8_t *a, uint32_t m) {
  uint32_t i;

  for (i=0; i<m; i++) {
    if (a[i] > 0) {
      printf(" c[%"PRId32"] = %"PRIu8"\n", i, a[i]);
    }
  }
}


/*
 * Full test:
 * - successively store array[0 ... n-1] into b
 * - use indices in the range 0 ... m-1
 * - then check whether pop works
 */
static void test_arrays(uint8_array_t *b, uint32_t n, uint32_t m) {
  uint32_t i;
  int32_t max;
  uint8_t *check;

  assert(n <= NUM_ARRAYS);

  reset_uint8_array(b);

  printf("Initial content\n");
  print_backtrackable_array(b);
  printf("\n\n");

  init_arrays(n, m);

  // phase 1: add arrays
  for (i=0; i<n; i++) {
    printf("Level %"PRIu32"\n", i);
    print_test_array(array[i], size[i]);
    printf("\n");
    write_array(array[i], size[i], b);
    printf("New content:\n");
    print_backtrackable_array(b);
    printf("\n");

    // double check
    max = max_index(i);
    assert(max >= 0);
    check = expand_arrays(i, max + 1);
    printf("Check:\n");
    print_expanded_array(check, max + 1);
    printf("\n");
    if (equal_array(check, max+1, b)) {
      printf("OK\n\n");
    } else {
      printf("BUG\n\n");
      abort();
    }
    safe_free(check);

    uint8_array_push(b);
  }

  // phase 2: backtrack to level n/2
  while (i > n/2) {
    i--;
    uint8_array_pop(b);
    printf("Backtracking to level %"PRIu32"\n", i);
    print_backtrackable_array(b);
    printf("\n");

    // double check
    max = max_index(i);
    assert(max >= 0);
    check = expand_arrays(i, max + 1);
    printf("Check:\n");
    print_expanded_array(check, max + 1);
    printf("\n");
    if (equal_array(check, max+1, b)) {
      printf("OK\n\n");
    } else {
      printf("BUG\n\n");
      abort();
    }
    safe_free(check);
  }

  // phase 3: rebuild all arrays until level n
  while (i < n) {
    printf("Level %"PRIu32"\n", i);
    print_test_array(array[i], size[i]);
    printf("\n");
    write_array(array[i], size[i], b);
    printf("New content:\n");
    print_backtrackable_array(b);
    printf("\n");

    // double check
    max = max_index(i);
    assert(max >= 0);
    check = expand_arrays(i, max + 1);
    printf("Check:\n");
    print_expanded_array(check, max + 1);
    printf("\n");
    if (equal_array(check, max+1, b)) {
      printf("OK\n\n");
    } else {
      printf("BUG\n\n");
      abort();
    }
    safe_free(check);

    uint8_array_push(b);
    i ++;
  }


  // phase 4: backtrack all the way
  while (i > 0) {
    i--;
    uint8_array_pop(b);
    printf("Backtracking to level %"PRIu32"\n", i);
    print_backtrackable_array(b);
    printf("\n");

    // double check
    max = max_index(i);
    assert(max >= 0);
    check = expand_arrays(i, max + 1);
    printf("Check:\n");
    print_expanded_array(check, max + 1);
    printf("\n");
    if (equal_array(check, max+1, b)) {
      printf("OK\n\n");
    } else {
      printf("BUG\n\n");
      abort();
    }
    safe_free(check);
  }

  delete_arrays(n);
}


/*
 * Global backtrackable array
 */
static uint8_array_t tst;


int main(void) {
  init_uint8_array(&tst, 0, 4);
  test_arrays(&tst, 50, 30);
  test_arrays(&tst, 50, 1000);
  delete_uint8_array(&tst);

  return 0;
}
