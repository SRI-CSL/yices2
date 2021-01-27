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
 * SORT AN ARRAY OF UNSIGNED INTEGERS WITH A USER-SUPPLIED ORDERING
 */

#include "utils/uint_array_sort2.h"
#include "utils/prng.h"

// auxiliary structure to store comparison function + prng
typedef struct uint32_sorter_s {
  void *data;
  uint_cmp_fun_t cmp;
  uint32_t prng;
} uint32_sorter_t;

static inline bool cmp(const uint32_sorter_t *sorter, int32_t x, int32_t y) {
  return sorter->cmp(sorter->data, x, y);
}

static void qsort_uint_array2(uint32_sorter_t *sorter, uint32_t *a, uint32_t n);


// insertion sort
static void isort_uint_array2(const uint32_sorter_t *sorter, uint32_t *a, uint32_t n) {
  uint32_t i, j;
  uint32_t x, y;

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

static inline void sort_array2(uint32_sorter_t *sorter, uint32_t *a, uint32_t n) {
  if (n < 10) {
    isort_uint_array2(sorter, a, n);
  } else {
    qsort_uint_array2(sorter, a, n);
  }
}

// quick sort: requires n > 1
static void qsort_uint_array2(uint32_sorter_t *sorter, uint32_t *a, uint32_t n) {
  uint32_t i, j;
  uint32_t x, y;

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
  sort_array2(sorter, a, j);
  j++;
  sort_array2(sorter, a + j, n - j);
}


/*
 * External call
 */
void uint_array_sort2(uint32_t *a, uint32_t n, void *data, uint_cmp_fun_t cmp) {
  uint32_sorter_t sorter;

  sorter.data = data;
  sorter.cmp = cmp;
  sorter.prng = PRNG_DEFAULT_SEED;

  sort_array2(&sorter, a, n);
}
