/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BASIC SORT FOR INTEGER ARRAYS
 */

#include "utils/int_array_sort.h"
#include "utils/prng.h"

static void qsort_int_array(int32_t *a, uint32_t n);

// insertion sort
static void isort_int_array(int32_t *a, uint32_t n) {
  uint32_t i, j;
  int32_t x, y;

  for (i=1; i<n; i++) {
    x = a[i];
    j = 0;
    while (a[j] < x) j ++;
    while (j < i) {
      y = a[j]; a[j] = x; x = y;
      j ++;
    }
    a[j] = x;
  }
}

static inline void sort_array(int32_t *a, uint32_t n) {
  if (n < 10) {
    isort_int_array(a, n);
  } else {
    qsort_int_array(a, n);
  }
}

// quick sort: requires n > 1
static void qsort_int_array(int32_t *a, uint32_t n) {
  uint32_t i, j;
  int32_t x, y;

  // x = random pivot
  i = random_uint(n);
  x = a[i];

  // swap x and a[0]
  a[i] = a[0];
  a[0] = x;

  i = 0;
  j = n;

  do { j--; } while (a[j] > x);
  do { i++; } while (i <= j && a[i] < x);

  while (i < j) {
    y = a[i]; a[i] = a[j]; a[j] = y;

    do { j--; } while (a[j] > x);
    do { i++; } while (a[i] < x);
  }

  // pivot goes into a[j]
  a[0] = a[j];
  a[j] = x;

  // sort a[0...j-1] and a[j+1 .. n-1]
  sort_array(a, j);
  j++;
  sort_array(a + j, n - j);
}


/*
 * External call
 */
void int_array_sort(int32_t *a, uint32_t n) {
  sort_array(a, n);
}
