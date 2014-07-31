/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SORT AN INTEGER ARRAY WITH A USER-SUPPLIED ORDERING
 */

#include "utils/int_array_sort2.h"
#include "utils/prng.h"

static void qsort_int_array2(int32_t *a, uint32_t n, void *data, int_cmp_fun_t cmp);


// insertion sort
static void isort_int_array2(int32_t *a, uint32_t n, void *data, int_cmp_fun_t cmp) {
  uint32_t i, j;
  int32_t x, y;

  for (i=1; i<n; i++) {
    x = a[i];
    j = 0;
    while (cmp(data, a[j], x)) j ++; // while (a[j] < x) j++;
    while (j < i) {
      y = a[j]; a[j] = x; x = y;
      j ++;
    }
    a[j] = x;
  }
}

static inline void sort_array2(int32_t *a, uint32_t n, void *data, int_cmp_fun_t cmp) {
  if (n < 10) {
    isort_int_array2(a, n, data, cmp);
  } else {
    qsort_int_array2(a, n, data, cmp);
  }
}

// quick sort: requires n > 1
static void qsort_int_array2(int32_t *a, uint32_t n, void *data, int_cmp_fun_t cmp) {
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

  do { j--; } while (cmp(data, x, a[j]));            // do { j--; } while (x < a[j]);
  do { i++; } while (i <= j && cmp(data, a[i], x));  // do { i++; } while (a[i] < x);

  while (i < j) {
    y = a[i]; a[i] = a[j]; a[j] = y;

    do { j--; } while (cmp(data, x, a[j]));  // do { j--; } while (x < a[j]);
    do { i++; } while (cmp(data, a[i], x));  // do { j++; } while (a[i] < x);
  }

  // the pivot goes into a[j]
  a[0] = a[j];
  a[j] = x;

  // sort a[0...j-1] and a[j+1 .. n-1]
  sort_array2(a, j, data, cmp);
  j++;
  sort_array2(a + j, n - j, data, cmp);
}


/*
 * External call
 */
void int_array_sort2(int32_t *a, uint32_t n, void *data, int_cmp_fun_t cmp) {
  sort_array2(a, n, data, cmp);
}
