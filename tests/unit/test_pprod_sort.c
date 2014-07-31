/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "terms/power_products.h"
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


/*
 * Sort in increasing order of variables:
 * - a = array of pairs <variable, exponent>
 * - n = size of the array.
 */
static void isort_varexp_array(varexp_t *a, uint32_t n);
static void qsort_varexp_array(varexp_t *a, uint32_t n);

static inline void sort_varexp_array(varexp_t *a, uint32_t n) {
  if (n <= 10) {
    isort_varexp_array(a, n);
  } else {
    qsort_varexp_array(a, n);
  }
}

static void isort_varexp_array(varexp_t *a, uint32_t n) {
  uint32_t i, j, d, e;
  int32_t v, w;

  for (i=1; i<n; i++) {
    v = a[i].var;
    d = a[i].exp;
    j = 0;
    while (a[j].var < v) j ++;
    while (j < i) {
      w = a[j].var; a[j].var = v; v = w;
      e = a[j].exp; a[j].exp = d; d = e;
      j ++;
    }
    a[j].var = v;
    a[j].exp = d;
  }
}

static void qsort_varexp_array(varexp_t *a, uint32_t n) {
  uint32_t i, j;
  int32_t pivot;
  varexp_t aux;

  // random pivot
  i = random_uint(n);
  aux = a[i];
  pivot = a[i].var;

  // swap with a[0];
  a[i] = a[0];
  a[0] = aux;

  i = 0;
  j = n;

  // test i <= j in second loop is required for termination
  // if all elements are smaller than the pivot.
  do { j--; } while (a[j].var > pivot);
  do { i++; } while (i <= j && a[i].var < pivot);

  while (i < j) {
    aux = a[i]; a[i] = a[j]; a[j] = aux;

    do { j--; } while (a[j].var > pivot);
    do { i++; } while (a[i].var < pivot);
  }

  // swap pivot = a[0] and a[j]
  aux = a[0]; a[0] = a[j]; a[j] = aux;

  // sort a[0 ... j-1] and a[j+1 ... n-1]
  sort_varexp_array(a, j);
  j ++;
  sort_varexp_array(a + j, n - j);
}



/*
 * Merge pairs <var, d> with the same var.
 * Remove pairs <var, d> with d = 0.
 * return the number of elements remaining after normalization
 */
static int32_t normalize_varexp_array(varexp_t *a, uint32_t n) {
  uint32_t i, j, d;
  int32_t v;

  if (n == 0) return n;

  sort_varexp_array(a, n);

  j = 0;
  d = a[0].exp;
  v = a[0].var;
  for (i=1; i<n; i++) {
    if (a[i].var == v) {
      d += a[i].exp;
    } else {
      if (d != 0) {
	a[j].var = v;
	a[j].exp = d;
	j ++;
      }
      v = a[i].var;
      d = a[i].exp;
    }
  }

  if (d != 0) {
    a[j].var = v;
    a[j].exp = d;
    j ++;
  }

  return j;
}

static varexp_t a[200];

static void show_array(uint32_t n) {
  uint32_t i, l;

  if (n == 0) {
    printf(" empty\n");
    return;
  }
  l = 10;
  for (i=0; i<n; i++) {
    if (l == 0) { l = 10; printf("\n"); };
    l --;
    printf(" (%3"PRId32",%3"PRIu32")", a[i].var, a[i].exp);
  }
  printf("\n");
}

static void normalize_array(uint32_t n) {
  printf("--- original ---\n");
  show_array(n);
  printf("--- normalized ---\n");
  n = normalize_varexp_array(a, n);
  show_array(n);
  printf("---\n\n");
}


int main() {
  int i;

  for (i=0; i<20; i++) {
    a[i].var = i;
    a[i].exp = 1;
  }
  normalize_array(20);

  for (i=0; i<20; i++) {
    a[i].var = 20 - i;
    a[i].exp = 2;
  }
  normalize_array(20);

  for (i=0; i<10; i++) {
    a[i].var = 20 - i;
    a[i].exp = -i;
  }
  for (i=10; i<20; i++) {
    a[i].var = i + 1;
    a[i].exp = 19 - i;
  }
  normalize_array(20);

  normalize_array(0);
  normalize_array(1);

  a[0].var = 0;
  a[1].var = 10;
  normalize_array(2);

  a[0].var = 10;
  a[1].var = 0;
  normalize_array(2);

  for (i=0; i<40; i++) {
    a[i].var = random() % 100;
    a[i].exp = i;
  }
  normalize_array(40);

  for (i=0; i<100; i++) {
    a[i].var = random() % 100;
    a[i].exp = i;
  }
  normalize_array(100);

  for (i=0; i<100; i++) {
    a[i].var = random() % 100;
    a[i].exp = i;
  }
  normalize_array(100);

  for (i=0; i<100; i++) {
    a[i].var = random() % 100;
    a[i].exp = i;
  }
  normalize_array(100);

  for (i=0; i<100; i++) {
    a[i].var = random() % 100;
    a[i].exp = i;
  }
  normalize_array(100);

  for (i=0; i<100; i++) {
    a[i].var = random() % 100;
    a[i].exp = i;
  }
  normalize_array(100);

  for (i=0; i<100; i++) {
    a[i].var = random() % 100;
    a[i].exp = i;
  }
  normalize_array(100);

  return 0;
}
