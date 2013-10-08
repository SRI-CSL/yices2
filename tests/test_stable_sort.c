#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "memalloc.h"
#include "cputime.h"
#include "stable_sort.h"

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
static bool cmp(void *aux, void *p, void *q) {
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
 * Initialize constant, increasing, decreasing arrays
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

static void decreasing_array(pair_t **a, uint32_t n) {
  increasing_array(a, n);
  reverse_array(a, n);
}

static void random_array(pair_t **a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    a[i]->key = (uint32_t) (random() % 200);
  }
}


/*
 * Tests: array of size n
 * - base = array of n pairs
 */
static void test_sorting(stable_sorter_t *sorter, pair_t **a, pair_t *base, uint32_t n) {
  uint32_t i;

  printf("**** TEST SORT: ARRAY SIZE %"PRIu32" ****\n", n);
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
  random_array(a, n);
  test_sort(sorter, a, n);
  random_array(a, n);
  test_sort(sorter, a, n);
  random_array(a, n);
  test_sort(sorter, a, n);
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
  printf("Total run time: %.3f s\n", runtime);

  delete_stable_sorter(&sorter);

  return 0;
}
