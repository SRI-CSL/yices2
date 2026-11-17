/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * SORT AN ARRAY OF POINTERS WITH USER-SUPPLIED ORDER
 */

#include "utils/prng.h"
#include "utils/ptr_array_sort2.h"

// Auxiliary structure to store cmp & random-number state
typedef struct ptr_sorter_s {
  void *data;
  ptr_cmp_fun_t cmp;
  uint32_t prng;
} ptr_sorter_t;

static inline bool cmp(const ptr_sorter_t *sorter, void *x, void *y) {
  return sorter->cmp(sorter->data, x, y);
}

static void qsort_ptr_array2(ptr_sorter_t *sorter, void **a, uint32_t n);


// insertion sort
static void isort_ptr_array2(const ptr_sorter_t *sorter, void **a, uint32_t n) {
  uint32_t i, j;
  void *x, *y;

  for (i=1; i<n; i++) {
    x = a[i];
    j = 0;
    while (cmp(sorter, a[j], x)) j ++; // while (a[j] < x) j++;
    while (j < i) {
      y = a[j]; a[j] = x; x = y;
      j ++;
    }
    a[j] = x;
  }
}

static inline void sort_ptr_array2(ptr_sorter_t *sorter, void **a, uint32_t n) {
  if (n < 10) {
    isort_ptr_array2(sorter, a, n);
  } else {
    qsort_ptr_array2(sorter, a, n);
  }
}

// quick sort: requires n > 1
static void qsort_ptr_array2(ptr_sorter_t *sorter, void **a, uint32_t n) {
  uint32_t i, j;
  void *x, *y;

  // x = random pivot
  i = random_uint(&sorter->prng, n);
  x = a[i];

  // swap x and a[0]
  a[i] = a[0];
  a[0] = x;

  i = 0;
  j = n;

  do { j--; } while (cmp(sorter, x, a[j]));            // do { j--; } while (x < a[j]);
  do { i++; } while (i <= j && cmp(sorter, a[i], x));  // do { i++; } while (a[i] < x);

  while (i < j) {
    y = a[i]; a[i] = a[j]; a[j] = y;

    do { j--; } while (cmp(sorter, x, a[j]));  // do { j--; } while (x < a[j]);
    do { i++; } while (cmp(sorter, a[i], x));  // do { j++; } while (a[i] < x);
  }

  // the pivot goes into a[j]
  a[0] = a[j];
  a[j] = x;

  // sort a[0...j-1] and a[j+1 .. n-1]
  sort_ptr_array2(sorter, a, j);
  j++;
  sort_ptr_array2(sorter, a + j, n - j);
}


/*
 * External call
 */
void ptr_array_sort2(void **a, uint32_t n, void *data, ptr_cmp_fun_t cmp) {
  ptr_sorter_t sorter;

  sorter.data = data;
  sorter.cmp = cmp;
  sorter.prng = PRNG_DEFAULT_SEED;

  sort_ptr_array2(&sorter, a, n);
}
