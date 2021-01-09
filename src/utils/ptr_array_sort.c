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

/*
 * SORT OF POINTER ARRAYS
 */

/*
 * We convert the pointers to (uintptr_t) then we sort the values
 * in increasing order.
 */

#include "utils/prng.h"
#include "utils/ptr_array_sort.h"

static void qsort_ptr_array(uint32_t *prng, void **a, uint32_t n);

/*
 * Insertion sort
 */
static void isort_ptr_array(void **a, uint32_t n) {
  uint32_t i, j;
  uintptr_t x, y;

  for (i=1; i<n; i++) {
    x = (uintptr_t) a[i];
    j = 0;
    while ((uintptr_t) a[j] < x) j ++;
    while (j < i) {
      y = (uintptr_t) a[j];
      a[j] = (void *) x;
      x = y;
      j++;
    }
    a[j] = (void *) x;
  }
}


/*
 * Sort: use either insertion or quick sort
 */
static inline void sort_array(uint32_t *prng, void **a, uint32_t n) {
  if (n < 10) {
    isort_ptr_array(a, n);
  } else {
    qsort_ptr_array(prng, a, n);
  }
}


/*
 * Quick sort: requires n > 1
 */
static void qsort_ptr_array(uint32_t *prng, void **a, uint32_t n) {
  uint32_t i, j;
  uintptr_t x, y;

  // x = random pivot
  i = random_uint(prng, n);
  x = (uintptr_t) a[i];

  // swap x and a[0]
  a[i] = a[0];
  a[0] = (void *) x;

  i = 0;
  j = n;

  do { j --; } while (((uintptr_t) a[j]) > x);
  do { i ++; } while (i <=j && (uintptr_t) a[i] < x);

  while (i < j) {
    y = (uintptr_t) a[i];
    a[i] = a[j];
    a[j] = (void *) y;

    do { j--; } while ((uintptr_t) a[j] > x);
    do { i++; } while ((uintptr_t) a[i] < x);
  }

  // store pivot into a[j]
  a[0] = a[j];
  a[j] = (void*) x;

  // sort subarrays
  sort_array(prng, a, j);
  j ++;
  sort_array(prng, a + j, n - j);
}


/*
 * External call
 */
void ptr_array_sort(void **a, uint32_t n) {
  uint32_t prng;
  prng = PRNG_DEFAULT_SEED;
  sort_array(&prng, a, n);
}
