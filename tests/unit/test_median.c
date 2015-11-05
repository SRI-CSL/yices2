/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Median of an integer array
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <assert.h>
#include <inttypes.h>

#include "utils/prng.h"


#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline long int random(void) {
  return rand();
}

#endif


/*
 * a must be an array of n+1 elements with a[n] as an end marker
 * - a[n] must be larger than any elemet in a[0 .. n-1]
 */
static int32_t median(int32_t *a, uint32_t n) {
  uint32_t low, high, half, i, j;
  int32_t pivot, aux;

  assert(n > 0);

  half = n/2;
  low = 0;
  high = n;

  do {
    // pick a random pivot in a[low ... high - 1]
    i = low + random_uint(high - low);
    pivot = a[i];

    // store pivot in a[low]
    a[i] = a[low];
    a[low] = pivot;

    i = low;
    j = high;
    for (;;) {
      do { j --; } while (a[j] > pivot);
      do { i ++; } while (a[i] < pivot);
      if (i >= j) break;
      aux = a[i]; a[i] = a[j]; a[j] = aux;
    }

    a[low] = a[j];
    a[j] = pivot;

    /*
     * At this point:
     * - a[0 ... j-1] <= pivot
     * - a[j] = pivot
     * - a[j+1 ... n-1] >= pivot
     * low < j < high and low < half < high
     */
    if (j < half) {
      low = j+1;
    } else {
      high = j;
    }
  } while (j != half);

  return a[half];
}


/*
 * Initialize array for testing
 */
static void constant_array(int32_t *a, int32_t n) {
  int32_t i, v;

  v = (int32_t) (random() % 100);
  for (i=0; i<n; i++) {
    a[i] = v;
  }
}

static void increasing_array(int32_t *a, int32_t n) {
  int32_t i, v;

  v = ((int32_t) (random() % 100)) - 50;
  for (i=0; i<n; i++) {
    a[i] = v;
    v += (int32_t) (random() % 4);
  }
}

static void decreasing_array(int32_t *a, int32_t n) {
  int32_t i, v;

  v = ((int32_t) (random() % 100)) - 50;
  for (i=0; i<n; i++) {
    a[i] = v;
    v -= (int32_t) (random() % 4);
  }
}

static void random_array(int32_t *a, int32_t n) {
  int32_t i;

  for (i=0; i<n; i++) {
    a[i] = ((int32_t) (random() % 1000)) - 500;
  }
}


static void print_array(int32_t *a, int32_t n) {
  int32_t i, l;

  l = 20;
  for (i=0; i<n; i++) {
    if (l == 0) {
      printf("\n\t");
      l = 20;
    }
    l --;
    printf(" %4"PRId32, a[i]);
  }
  printf("\n");
}


/*
 * Check whether x is a possible median for a
 */
static void check_median(int32_t x, int32_t *a, uint32_t n) {
  uint32_t b, u, e, i;

  b = 0;
  u = 0;
  e = 0;

  for (i=0; i<n; i++) {
    if (a[i] == x) {
      e ++;
    } else if (a[i] < x) {
      b ++;
    } else {
      u ++;
    }
  }

  printf("  below median: %"PRIu32"\n", b);
  printf("  equal median: %"PRIu32"\n", e);
  printf("  above median: %"PRIu32"\n", u);

  if (e == 0) {
    printf("BUG: median not in array\n\n");
  }

  if (n % 1 == 1) {
    i = (n/2) + 1;
    if (b >= i || u >= i) {
      printf("BUG: incorrect median (odd size)\n\n");
    }
  } else {
    i = n/2;
    if (b > i || u > i) {
      printf("BUG: incorrect median (even size)\n\n");
    }
  }
}


/*
 * Single test: print array and its median
 */
static void run_test(int32_t *a, uint32_t n) {
  int32_t x;

  printf("\nInput:  ");
  print_array(a, n);
  x = median(a, n);
  printf("Median:  %4"PRId32"\n", x);
  check_median(x, a, n);
}



/*
 * Global array for testing
 */
#define ASIZE 200

static int32_t test[ASIZE+1];


int main(void) {
  uint32_t i, size;

  // small arrays
  for (size = 1; size<6; size++) {
    test[size] = INT32_MAX;
    constant_array(test, size);
    run_test(test, size);
    increasing_array(test, size);
    run_test(test, size);
    decreasing_array(test, size);
    run_test(test, size);
    random_array(test, size);
    run_test(test, size);
    run_test(test, size);
    random_array(test, size);
    run_test(test, size);
    run_test(test, size);
  }


  size = ASIZE;
  test[size] = INT32_MAX;

  for (i=0; i<20; i++) {
    constant_array(test, size);
    run_test(test, size);
  }

  for (i=0; i<20; i++) {
    increasing_array(test, size);
    run_test(test, size);
  }

  for (i=0; i<20; i++) {
    decreasing_array(test, size);
    run_test(test, size);
  }

  for (i=0; i<200; i++) {
    random_array(test, size);
    run_test(test, size);
  }


  size = ASIZE-1;
  test[size] = INT32_MAX;

  for (i=0; i<20; i++) {
    constant_array(test, size);
    run_test(test, size);
  }

  for (i=0; i<20; i++) {
    increasing_array(test, size);
    run_test(test, size);
  }

  for (i=0; i<20; i++) {
    decreasing_array(test, size);
    run_test(test, size);
  }

  for (i=0; i<200; i++) {
    random_array(test, size);
    run_test(test, size);
  }

  return 0;
}
