/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SORT OF POINTER ARRAYS
 */

#include "utils/prng.h"
#include "utils/ptr_array_sort.h"

static void qsort_ptr_array(void **a, uint32_t n);

/*
 * Insertion sort
 */
static void isort_ptr_array(void **a, uint32_t n) {
  uint32_t i, j;
  void *x, *y;

  for (i=1; i<n; i++) {
    x = a[i];
    j = 0;
    while (a[j] < x) j ++;
    while (j < i) {
      y = a[j];
      a[j] = x;
      x = y;
      j++;
    }
    a[j] = x;
  }
}


/*
 * Sort: use either insertion or quick sort
 */
static inline void sort_array(void **a, uint32_t n) {
  if (n < 10) {
    isort_ptr_array(a, n);
  } else {
    qsort_ptr_array(a, n);
  }
}


/*
 * Quick sort: requires n > 1
 */
static void qsort_ptr_array(void **a, uint32_t n) {
  uint32_t i, j;
  void *x, *y;

  // x = random pivot
  i = random_uint(n);
  x = a[i];

  // swap x and a[0]
  a[i] = a[0];
  a[0] = x;

  i = 0;
  j = n;

  do { j --; } while (a[j] > x);
  do { i ++; } while (i <=j && a[i] < x);

  while (i < j) {
    y = a[i];
    a[i] = a[j];
    a[j] = y;

    do { j--; } while (a[j] > x);
    do { i++; } while (a[i] < x);
  }

  // store pivot into a[j]
  a[0] = a[j];
  a[j] = x;

  // sort subarrays
  sort_array(a, j);
  j ++;
  sort_array(a + j, n - j);
}


/*
 * External call
 */
void ptr_array_sort(void **a, uint32_t n) {
  sort_array(a, n);
}
