/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>
#include <assert.h>

#include "utils/sparse_arrays.h"

#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif



/*
 * Test data: array of pairs (idx, cnt) where idx = a random number and cnt = reference counter for x
 * - the array is sorted: a[i].idx < a[i+1].idx
 */
typedef struct ref_pairs_s {
  uint32_t idx;
  uint32_t cnt;
} ref_pair_t;



/*
 * Binary search in a[0 ... n-1]
 * - a[0 ... n-1] must be sorted
 * - return i such that
 *   all elements in a[0 ... i-1] are less than x (strictly)
 *   all elements in a[i ... n-1] are more than or equal to x
 * - in particular:
 *   return 0 if all elements are >= x
 *   return n if all elements are < x
 */
static uint32_t locate_sample(ref_pair_t *a, uint32_t n, uint32_t x) {
  uint32_t l, h, k;

  l = 0;
  h = n;
  while (l < h) {
    k = (l + h)/2;
    assert(l <= k && k < h);
    if (a[k].idx < x) {
      l = k + 1;
    } else {
      h = k;
    }
  }

  return l;
}


/*
 * Insert x into array a[0 .. n]
 * - a[0 ... n-1] is sorted
 * - return true if x can be inserted (i.e., x is not duplicate)
 */
static bool insert_sample(ref_pair_t *a, uint32_t n, uint32_t x) {
  uint32_t i, k;

  k = locate_sample(a, n, x);
  assert(0 <= k && k <= n);
  if (k < n && a[k].idx == x) {
    return false;
  }

  i = n;
  while (k < i) {
    a[i] = a[i-1];
    i --;
  }
  a[k].idx = x;
  a[k].cnt = 0;

  return true;
}


/*
 * Initialize array a:
 * - n = number of elements in a
 * - max_idx = bound on the indices
 * - we force a[i].idx < a[i+1].idx
 */
static void init_samples(ref_pair_t *a, uint32_t n, uint32_t max_idx) {
  uint32_t i, x;

  assert(max_idx > n);

  i = 0;
  while (i < n) {
    x = ((uint32_t) random()) % max_idx;
    i += insert_sample(a, i, x);
  }
}

/*
 * Check that all samples are in increasing order and below max_idx
 */
static void check_samples(ref_pair_t *a, uint32_t n, uint32_t max_idx) {
  uint32_t i, x;

  assert(n > 0);
  x = a[0].idx;
  if (x >= max_idx) {
    fprintf(stderr, "Bad sample array: limit = %"PRIu32", a[0]=%"PRIu32"\n", max_idx, x);
    exit(1);
  }

  for (i=1; i<n; i++) {
    if (a[i].idx <= x) {
      fprintf(stderr, "Bad sample array: not increasing: a[%"PRIu32"]=%"PRIu32", a[%"PRIu32"]=%"PRIu32"\n",
	      i-1, x, i, a[i].idx);
      exit(1);
    }
    x = a[i].idx;
    if (x >= max_idx) {
      fprintf(stderr, "Bad sample array: limit = %"PRIu32", a[%"PRIu32"]=%"PRIu32"\n", max_idx, i, x);
      exit(1);
    }
  }
}



/*
 * Check what all elements in [lo, hi-1] have ref count 0 in test
 */
static void check_all_zero(sparse_array_t *test, uint32_t lo, uint32_t hi) {
  uint32_t i, c;

  assert(lo <= hi);

  for (i=lo; i<hi; i++) {
    c = sparse_array_read(test, i);
    if (c != 0) {
      fprintf(stderr, "*** BUG: incorrect ref count for %"PRIu32": should be zero\n", i);
      exit(1);
    }
  }
}


/*
 * Check that a and test agree
 * - n = number of elements in a
 * - max_idx = range of indices ([0 ... max_idx-1])
 */
static void check_sparse_array(sparse_array_t *test, ref_pair_t *a, uint32_t n, uint32_t max_idx) {
  uint32_t x, i, c, base;
  uint32_t nelems;

  nelems = 0;
  base = 0;
  for (i=0; i<n; i++) {
    x = a[i].idx;
    c = sparse_array_read(test, x);
    if (c != a[i].cnt) {
      fprintf(stderr, "*** BUG: incorrect ref count for %"PRIu32": returned %"PRIu32" (%"PRIu32" was expected)\n",
	      x, c, a[i].cnt);
      exit(1);
    }
    check_all_zero(test, base, x);
    base = x+1;
    if (a[i].cnt > 0) {
      nelems ++;
    }
  }
  check_all_zero(test, base, max_idx);

  if (nelems != test->nelems) {
    fprintf(stderr, "*** BUG: incorrect nelems %"PRIu32" (should be %"PRIu32")\n", test->nelems, nelems);
    exit(1);
  }
}



/*
 * Do nops random incr/decr operations on elements of a
 */
static void random_ops(sparse_array_t *test, ref_pair_t *a, uint32_t n, uint32_t nops) {
  uint32_t i, x;

  assert(n > 0);

  while (nops > 0) {
    nops --;

    i = random() % n;
    x = a[i].idx;
    assert(a[i].cnt < UINT32_MAX);
    if (a[i].cnt == 0 || (random() & 0x800) == 0) {
      printf("increment a[%"PRIu32"]\n", x);
      sparse_array_incr(test, x);
      a[i].cnt ++;
    } else {
      printf("decrement a[%"PRIu32"]\n", x);
      sparse_array_decr(test, x);
      a[i].cnt --;
    }
  }
}


/*
 * Iterate: print all elements with a positive count
 */
static void print_elem(void *aux, uint32_t i) {
  printf(" %"PRIu32, i);
}

static void print_sparse_array(sparse_array_t *test) {
  sparse_array_iterate(test, NULL, print_elem);
  printf("\n");
}




int main(void) {
  sparse_array_t array;
  ref_pair_t test[200];
  uint32_t ntests;

  init_sparse_array(&array, 10000);

  for (ntests = 1; ntests <= 1000; ntests ++) {
    init_samples(test, 200, 10000);
    check_samples(test, 200, 10000);

    printf("---- Test %"PRIu32" ---\n", ntests);
    printf("initial array: ");
    print_sparse_array(&array);
    check_sparse_array(&array, test, 200, 10000);

    random_ops(&array, test, 200, 400);
    printf("new array: ");
    print_sparse_array(&array);
    check_sparse_array(&array, test, 200, 10000);

    random_ops(&array, test, 200, 400);
    printf("new array: ");
    print_sparse_array(&array);
    check_sparse_array(&array, test, 200, 10000);

    random_ops(&array, test, 200, 400);
    printf("new array: ");
    print_sparse_array(&array);
    check_sparse_array(&array, test, 200, 10000);

    reset_sparse_array(&array);
  }

  delete_sparse_array(&array);

  return 0;
}
