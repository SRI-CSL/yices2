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

#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>
#include <assert.h>

#include "utils/prng.h"

typedef uint32_t bddvar_t;

/*
 * Sort an array of bdd variables by rank
 * - a = array of variables
 * - n = size of that array
 *
 * - isort: uses insertion sort (for small n)
 * - qsort: quick sort
 */
static void sort_by_rank(bddvar_t *a, uint32_t n, uint32_t *rank);

static void isort_by_rank(bddvar_t *a, uint32_t n, uint32_t *rank) {
  uint32_t i, j, r;
  bddvar_t x, y;

  for (i=1; i<n; i++) {
    x = a[i];
    r = rank[x];
    j = 0;
    while (rank[a[j]] < r) j ++;
    while (j < i) {
      y = a[j]; a[j] = x; x = y;
      j ++;
    }
    a[j] = x;
  }
}


// preconditions: n > 0
static void qsort_by_rank(bddvar_t *a, uint32_t n, uint32_t *rank) {
  uint32_t i, j, r;
  bddvar_t x, y;
  uint32_t seed = PRNG_DEFAULT_SEED;
  
  // x = randomly picked pivot
  i = random_uint(&seed, n);
  x = a[i];
  r = rank[x];

  // swap with a[0]
  a[i] = a[0];
  a[0] = x; // important

  i = 0;
  j = n;

  do { j--; } while (rank[a[j]] > r);
  do { i++; } while (i <= j && rank[a[i]] < r);

  while (i < j) {
    y = a[i]; a[i] = a[j]; a[j] = y;

    do { j--; } while (rank[a[j]] > r);
    do { i++; } while (rank[a[i]] < r);
  }

  // the pivot goes into a[j]
  a[0] = a[j];
  a[j] = x;

  sort_by_rank(a, j, rank);
  j ++;
  sort_by_rank(a + j, n - j, rank);
}

static void sort_by_rank(bddvar_t *a, uint32_t n, uint32_t *rank) {
  if (n <= 10) {
    isort_by_rank(a, n, rank);
  } else {
    qsort_by_rank(a, n, rank);
  }
}



/*
 * Print array of variable and rank
 */
static void print_vars(bddvar_t *a, uint32_t n, uint32_t *rank) {
  uint32_t i;

  for (i=0; i<n; i++) {
    printf("  %3"PRIu32" (r=%"PRIu32")\n", a[i], rank[a[i]]);
  }
  printf("\n");
}


/*
 * Check that array a is sorted
 */
static void check_sorted_array(bddvar_t *a, uint32_t n, uint32_t *rank) {
  uint32_t i;

  for (i=1; i<n; i++) {
    assert(rank[a[i-1]] <= rank[a[i]]);
  }
}

/*
 * Random ranks
 */
static void random_ranks(uint32_t n, uint32_t *rank) {
  uint32_t i;
  uint32_t seed = PRNG_DEFAULT_SEED;
  
  for (i=0; i<n; i++) {
    rank[i] = random_uint(&seed, 50);
  }
}

static uint32_t rank[50];
static bddvar_t var[50];


int main(void) {
  uint32_t i, n, m;

  n = 6;
  for (m=0; m<500; m++) {
    for (i=0; i<n-1; i++) var[i] = i+1;
    var[n-1] = 0;

    random_ranks(n, rank);

    printf("--- before ---\n");
    print_vars(var, n, rank);
    printf("--- qsort ---\n");
    sort_by_rank(var, n, rank);
    print_vars(var, n, rank);
    check_sorted_array(var, n, rank);

    if (m % 8 == 0) {
      n ++;
      if (n > 50) n = 6;
    }
  }
  return 0;
}
