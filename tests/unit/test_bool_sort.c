/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of sorting
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <inttypes.h>

#include <assert.h>

#include "utils/prng.h"

#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline int random(void) {
  return rand();
}

#endif


typedef int32_t term_t;

// random array of integers
static void random_terms(uint32_t n, term_t *a) {
  int i;

  for (i=0; i<n; i++) {
    a[i] = (random() % 100);
  }
}

static uint32_t bool_rank(term_t x) {
  assert(x >= 0);
  return x;
}

static void isort_terms(uint32_t n, term_t *a);
static void qsort_terms(uint32_t n, term_t *a);

static inline void sort_terms(uint32_t n, term_t *a) {
  if (n <= 10) {
    isort_terms(n, a);
  } else {
    qsort_terms(n, a);
  }
}

static void isort_terms(uint32_t n, term_t *a) {
  uint32_t i, j, r;
  term_t x, y;

  if (n < 2) return;

  for (i=1; i<n; i++) {
    x = a[i];
    r = bool_rank(x);
    j = 0;
    while (bool_rank(a[j]) < r) j++;
    while (j < i) {
      y = a[j]; a[j] = x; x = y;
      j ++;
    }
    a[j] = x;
  }
}

static void qsort_terms(uint32_t n, term_t *a) {
  uint32_t i, j, r;
  term_t x, y;

  //  assert(n > 1);
  //  if (n <= 1) return;

  // random pivot
  i = random_uint(n);
  x = a[i];
  r = bool_rank(x);

  // swap with a[0]
  a[i] = a[0];
  a[0] = x;

  i = 0;
  j = n;

  do { j--; } while (bool_rank(a[j]) > r);
  do { i++; } while (i <= j && bool_rank(a[i]) < r);

  while (i < j) {
    y = a[i]; a[i] = a[j]; a[j] = y;

    do { j--; } while (bool_rank(a[j]) > r);
    do { i++; } while (bool_rank(a[i]) < r);
  }

  // place pivot
  a[0] = a[j];
  a[j] = x;

  sort_terms(j, a); // a[0 ... j-1]
  j ++;
  sort_terms(n - j, a + j); // a[j+1 .. n-1]
}



static void print_terms(uint32_t n, term_t *a) {
  int i;

  for (i=0; i<n; i++) {
    if (i % 20 == 0) {
      if (i > 0) printf("\n");
      printf("  ");
    }
    printf("%02"PRId32, a[i]);
  }
  printf("\n");
}


static void random_test(uint32_t n) {
  term_t *a, *b;
  int i;

  a = (term_t *) malloc(n * sizeof(term_t));
  b = (term_t *) malloc(n * sizeof(term_t));

  random_terms(n, a);
  for (i=0; i<n; i++) b[i] = a[i];

  printf("\n--- Test: n = %"PRIu32" ---\n", n);
  print_terms(n, a);
  printf("\n");
  fflush(stdout);
  isort_terms(n, a);
  print_terms(n, a);
  printf("\n");

  print_terms(n, b);
  printf("\n");
  fflush(stdout);
  sort_terms(n, b);
  print_terms(n, b);
  printf("\n");

  for (i=0; i<n; i++) {
    assert(a[i] == b[i]);
  }

  free(b);
  free(a);
}

static void constant_test(uint32_t n) {
  term_t *a;
  int i, x;

  a = (term_t *) malloc(n * sizeof(term_t));

  x = random() % 100;
  for (i=0; i<n; i++) a[i] = x;

  printf("\n--- Test: n = %"PRIu32" ---\n", n);
  print_terms(n, a);
  printf("\n");
  fflush(stdout);
  isort_terms(n, a);
  print_terms(n, a);
  printf("\n");

  fflush(stdout);
  sort_terms(n, a);
  print_terms(n, a);
  printf("\n");

  for (i=0; i<n; i++) {
    assert(a[i] == x);
  }

  free(a);
}

static void increasing_test(uint32_t n) {
  term_t *a, *b;
  int i;

  a = (term_t *) malloc(n * sizeof(term_t));
  b = (term_t *) malloc(n * sizeof(term_t));

  for (i=0; i<n; i++) {
    a[i] = i;
    b[i] = a[i];
  }

  printf("\n--- Test: n = %"PRIu32" ---\n", n);
  print_terms(n, a);
  printf("\n");
  fflush(stdout);
  isort_terms(n, a);
  print_terms(n, a);
  printf("\n");

  print_terms(n, b);
  printf("\n");
  fflush(stdout);
  sort_terms(n, b);
  print_terms(n, b);
  printf("\n");

  for (i=0; i<n; i++) {
    assert(a[i] == b[i]);
  }

  free(b);
  free(a);
}


static void decreasing_test(uint32_t n) {
  term_t *a, *b;
  int i;

  a = (term_t *) malloc(n * sizeof(term_t));
  b = (term_t *) malloc(n * sizeof(term_t));

  for (i=0; i<n; i++) {
    a[i] = n- i - 1;
    b[i] = a[i];
  }

  printf("\n--- Test: n = %"PRIu32" ---\n", n);
  print_terms(n, a);
  printf("\n");
  fflush(stdout);
  isort_terms(n, a);
  print_terms(n, a);
  printf("\n");

  print_terms(n, b);
  printf("\n");
  fflush(stdout);
  sort_terms(n, b);
  print_terms(n, b);
  printf("\n");

  for (i=0; i<n; i++) {
    assert(a[i] == b[i]);
  }

  free(b);
  free(a);
}



int main(void) {
  int n;

  random_test(0);
  random_test(1);
  random_test(2);
  random_test(3);
  random_test(3);
  random_test(3);
  random_test(4);
  random_test(5);

  constant_test(100);
  constant_test(100);
  increasing_test(100);
  decreasing_test(100);

  for (n=0; n<30; n++) {
    random_test(100);
    random_test(200);
    random_test(1000);
  }

  return 0;
}
