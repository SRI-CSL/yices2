/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>

#include "utils/cputime.h"
#include "utils/stable_sort.h"

#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif

/*
 * Data to be sorted
 * each element is a pair key, idx
 * - the ordering is defined by p <= q iff p->key <= q->key
 * - idx is use to check that the ordering is table:
 *   if p is stored at index k in the array to be sorted
 *   then p->idx = k
 */
typedef struct pair_s {
  uint32_t key;
  uint32_t idx;
} pair_t;


/*
 * Comparison function:
 * cmp(aux, p, q) must return true if p <= q
 */
static bool cmp(const void *aux, const void *p, const void *q) {
  return ((pair_t *) p)->key <= ((pair_t *) q)->key;
}


/*
 * Check that all elements of a are in increasing order
 */
static void check_stable_sort(pair_t **a, uint32_t n) {
  pair_t *p, *q;
  uint32_t i;

  for (i=1; i<n; i++) {
    p = a[i-1];
    q = a[i];
    if (p->key > q->key) {
      fprintf(stderr, "*** BUG: array is not sorted ***\n");
      exit(1);
    }
    if (p->key == q->key && p->idx > q->idx) {
      fprintf(stderr, "*** BUG: not a stable sort ***\n");
      exit(1);
    }
  }
}


/*
 * Check that all indices from 0 to n-1 are present
 */
static uint8_t tag[10000];

static void check_indices(pair_t **a, uint32_t n) {
  uint32_t i, j;

  if (n <= 10000) {
    for (i=0; i<n; i++) {
      tag[i] = 0;
    }

    for (i=0; i<n; i++) {
      j = a[i]->idx;
      if (tag[j] != 0) {
	fprintf(stderr, "*** BUG: found duplicate element in array (index %"PRIu32")\n", j);
	exit(1);
      }
      tag[j] = 1;
    }
  }
}

static void show_array(pair_t **a, uint32_t n) {
  uint32_t i, k;

  k = 19;
  printf("[");
  for (i=0; i<n; i++) {
    k ++;
    if (k == 20) {
      printf("\n    ");
      k = 0;
    }
    printf(" %4"PRIu32, a[i]->key);
  }
  printf("]\n");
}

/*
 * Test of sort:
 * - a = array of n pair_t pointers (all distinct)
 * - sorter must be initialized
 */
static void test_sort(stable_sorter_t *sorter, pair_t **a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    a[i]->idx = i;
  }
  if (n <= 200) {
    printf("array:");
    show_array(a, n);
  }
  apply_sorter(sorter, (void**) a, n);
  if (n <= 200) {
    printf("sorted:");
    show_array(a, n);
    printf("\n");
  }
  check_stable_sort(a, n);
  check_indices(a, n);
}


/*
 * Initialize array a
 */
static void constant_array(pair_t **a, uint32_t n) {
  uint32_t i, v;

  v = (uint32_t) (random() % 100);
  for (i=0; i<n; i++) {
    a[i]->key = v;
  }
}

static void increasing_array(pair_t **a, uint32_t n) {
  uint32_t i, v;

  v = (uint32_t) (random() % 100);
  for (i=0; i<n; i++) {
    a[i]->key = v;
    v += (uint32_t) (random() % 4);
  }
}

static void strictly_increasing_array(pair_t **a, uint32_t n) {
  uint32_t i, v;

  v = (uint32_t) (random() % 100);
  for (i=0; i<n; i++) {
    a[i]->key = v;
    v += (uint32_t) (random() % 4) + 1;
  }
}


static void reverse_array(pair_t **a, uint32_t n) {
  pair_t *p;
  uint32_t i;

  if (n < 2) return;

  n --;
  i = 0;
  while (i < n) {
    p = a[i];
    a[i] = a[n];
    a[n] = p;
    i ++;
    n --;
  }
}

static void swap_elements(pair_t **a, uint32_t n, uint32_t nswaps) {
  pair_t *p;
  uint32_t i, j;

  if (n < 2) return;

  while (nswaps > 0) {
    nswaps --;
    i = (uint32_t) (random() % n);
    j = (uint32_t) (random() % n);
    p = a[i];
    a[i] = a[j];
    a[j] = p;
  }
}

static void decreasing_array(pair_t **a, uint32_t n) {
  increasing_array(a, n);
  reverse_array(a, n);
}

static void strictly_decreasing_array(pair_t **a, uint32_t n) {
  strictly_increasing_array(a, n);
  reverse_array(a, n);
}

static void random_array(pair_t **a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    a[i]->key = (uint32_t) (random() % 200);
  }
}

// variant: use larger numbers
static void random_array2(pair_t **a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    a[i]->key = (uint32_t) (random() % 20000000);
  }
}


static void almost_increasing_array(pair_t **a, uint32_t n) {
  increasing_array(a, n);
  swap_elements(a, n, n/20);
}

static void almost_decreasing_array(pair_t **a, uint32_t n) {
  decreasing_array(a, n);
  swap_elements(a, n, n/20);
}

static void down_up_down_array(pair_t **a, uint32_t n) {
  if (n >= 150) {
    strictly_decreasing_array(a, 80);
    strictly_increasing_array(a + 80, 70);
    strictly_decreasing_array(a + 150, n-150);
  } else {
    random_array(a, n);
  }
}

/*
 * For checking the balance_runs code: (based on paper by de Gouw et al).
 * - make run stores 0 .....0 1 starting at index i. n = size of the run
 */
static void make_run(pair_t **a, uint32_t i, uint32_t n) {
  uint32_t j;

  assert(n > 0);

  j = i+n-1;
  while (i < j) {
    a[i]->key = 0;
    i ++;
  }
  a[j]->key = 1;
}

static void balance_test_array(pair_t **a, uint32_t n) {
  if (n > 1100) {
    make_run(a, 0, 480);
    make_run(a, 480, 320);
    make_run(a, 800, 100);
    make_run(a, 900, 80);
    make_run(a, 980, 120);
    make_run(a, 1100, n - 1100);
  } else {
    down_up_down_array(a, n);
  }
}


/*
 * Minimal run size for an array of size n:
 * - returns n if n < 64
 * - returns 32 if n is a power of two
 * - returns a number between 33 and 64 otherwise =
 *   1 + the 6 high order bits of n
 *
 * This function is copied from stable_sort.c
 */
static uint32_t min_run(uint32_t n) {
  uint32_t r;

  r = 0;
  while (n >= 64) {
    r |= n & 1u;
    n >>= 1;
  }
  return n + r;
}

/*
 * Tests: array of size n
 * - base = array of n pairs
 */
static void test_sorting(stable_sorter_t *sorter, pair_t **a, pair_t *base, uint32_t n) {
  uint32_t i;

  printf("**** TEST SORT: ARRAY SIZE %"PRIu32" (min_run = %"PRIu32") ****\n", n, min_run(n));
  fflush(stdout);

  for (i=0; i<n; i++) {
    a[i] = base + i;
  }

  constant_array(a, n);
  test_sort(sorter, a, n);
  constant_array(a, n);
  test_sort(sorter, a, n);

  increasing_array(a, n);
  test_sort(sorter, a, n);
  increasing_array(a, n);
  test_sort(sorter, a, n);
  decreasing_array(a, n);
  test_sort(sorter, a, n);
  decreasing_array(a, n);
  test_sort(sorter, a, n);

  almost_increasing_array(a, n);
  test_sort(sorter, a, n);
  almost_increasing_array(a, n);
  test_sort(sorter, a, n);
  almost_decreasing_array(a, n);
  test_sort(sorter, a, n);
  almost_decreasing_array(a, n);
  test_sort(sorter, a, n);

  down_up_down_array(a, n);
  test_sort(sorter, a, n);
  down_up_down_array(a, n);
  test_sort(sorter, a, n);
  down_up_down_array(a, n);
  test_sort(sorter, a, n);
  down_up_down_array(a, n);
  test_sort(sorter, a, n);
  down_up_down_array(a, n);
  test_sort(sorter, a, n);
  down_up_down_array(a, n);
  test_sort(sorter, a, n);
  down_up_down_array(a, n);
  test_sort(sorter, a, n);

  balance_test_array(a, n);
  test_sort(sorter, a, n);
  balance_test_array(a, n);
  test_sort(sorter, a, n);
  balance_test_array(a, n);
  test_sort(sorter, a, n);
  balance_test_array(a, n);
  test_sort(sorter, a, n);

  random_array(a, n);
  test_sort(sorter, a, n);
  random_array(a, n);
  test_sort(sorter, a, n);
  random_array(a, n);
  test_sort(sorter, a, n);
  random_array(a, n);
  test_sort(sorter, a, n);
  random_array(a, n);
  test_sort(sorter, a, n);
  random_array(a, n);
  test_sort(sorter, a, n);
  random_array(a, n);
  test_sort(sorter, a, n);
}


/*
 * Measure sort time:
 * - s message
 */
static void test_sort2(const char *s, stable_sorter_t *sorter, pair_t **a, uint32_t n) {
  double runtime;
  uint32_t i;

  for (i=0; i<n; i++) {
    a[i]->idx = i;
  }

  runtime = get_cpu_time();
  apply_sorter(sorter, (void **) a, n);
  runtime = get_cpu_time() - runtime;
  if (runtime < 0) runtime = 0.0;
  printf("---> %s : sort time = %.3f s\n", s, runtime);
  fflush(stdout);

  check_stable_sort(a, n);
}

/*
 * Large array: initialize and allocte n pair objects
 * - n = number of elements
 */
static void test_large_sort(stable_sorter_t *sorter, uint32_t n) {
  pair_t **tmp;
  pair_t *aux;
  uint32_t i;

  printf("**** TEST SORT: ARRAY SIZE %"PRIu32" (min_run = %"PRIu32") ****\n", n, min_run(n));
  fflush(stdout);

  tmp = (pair_t **) malloc(n * sizeof(pair_t *));
  if (tmp == NULL) {
    fprintf(stderr, "Failed to allocate array\n");
    return;
  }

  for (i=0; i<n; i++) {
    aux = (pair_t *) malloc(sizeof(pair_t));
    if (aux == NULL) {
      fprintf(stderr, "Failed to allocate element (after %"PRIu32" allocations)\n", i);
      n = i;
      goto cleanup;
    }
    tmp[i] = aux;
  }

  constant_array(tmp, n);
  test_sort2("constant array", sorter, tmp, n);

  increasing_array(tmp, n);
  test_sort2("increasing array", sorter, tmp, n);

  strictly_decreasing_array(tmp, n);
  test_sort2("strictly decreasing array", sorter, tmp, n);

  decreasing_array(tmp, n);
  test_sort2("decreasing array", sorter, tmp, n);

  almost_increasing_array(tmp, n);
  test_sort2("mostly increasing array", sorter, tmp, n);

  almost_increasing_array(tmp, n);
  test_sort2("mostly increasing array", sorter, tmp, n);

  almost_increasing_array(tmp, n);
  test_sort2("mostly increasing array", sorter, tmp, n);

  almost_increasing_array(tmp, n);
  test_sort2("mostly increasing array", sorter, tmp, n);

  almost_increasing_array(tmp, n);
  test_sort2("mostly increasing array", sorter, tmp, n);

  almost_increasing_array(tmp, n);
  test_sort2("mostly increasing array", sorter, tmp, n);

  almost_decreasing_array(tmp, n);
  test_sort2("mostly decreasing array", sorter, tmp, n);

  almost_decreasing_array(tmp, n);
  test_sort2("mostly decreasing array", sorter, tmp, n);

  almost_decreasing_array(tmp, n);
  test_sort2("mostly decreasing array", sorter, tmp, n);

  almost_decreasing_array(tmp, n);
  test_sort2("mostly decreasing array", sorter, tmp, n);

  almost_decreasing_array(tmp, n);
  test_sort2("mostly decreasing array", sorter, tmp, n);

  almost_decreasing_array(tmp, n);
  test_sort2("mostly decreasing array", sorter, tmp, n);

  almost_decreasing_array(tmp, n);
  test_sort2("mostly decreasing array", sorter, tmp, n);

  random_array(tmp, n);
  test_sort2("random array", sorter, tmp, n);

  random_array(tmp, n);
  test_sort2("random array", sorter, tmp, n);

  random_array(tmp, n);
  test_sort2("random array", sorter, tmp, n);

  random_array2(tmp, n);
  test_sort2("random array", sorter, tmp, n);

  random_array2(tmp, n);
  test_sort2("random array", sorter, tmp, n);

  random_array2(tmp, n);
  test_sort2("random array", sorter, tmp, n);

  printf("\n");

 cleanup:
  for (i=0; i<n; i++) {
    free(tmp[i]);
  }
  free(tmp);
}

static pair_t buffer[10000];
static pair_t *test[10000];

int main(void) {
  stable_sorter_t sorter;
  uint32_t i;
  double runtime;

  init_stable_sorter(&sorter, NULL, cmp);

  runtime = get_cpu_time();
  for (i=0; i<= 100; i++) {
    test_sorting(&sorter, test, buffer, i);
  }
  for (i=100; i<=10000; i += 100) {
    test_sorting(&sorter, test, buffer, i);
  }
  runtime = get_cpu_time() - runtime;
  printf("Total run time: %.3f s\n\n", runtime);

  test_large_sort(&sorter, 500000);
  test_large_sort(&sorter, 1000000);
  test_large_sort(&sorter, 2000000);
  test_large_sort(&sorter, 3000000);
  test_large_sort(&sorter, 4000000);

  runtime = get_cpu_time() - runtime;
  printf("Total run time: %.3f s\n\n", runtime);

  delete_stable_sorter(&sorter);

  return 0;
}
