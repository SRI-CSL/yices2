/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Quick sort of an array of integers
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <assert.h>
#include <inttypes.h>

#include "utils/memalloc.h"
#include "utils/cputime.h"

#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline long int random(void) {
  return rand();
}

#endif

static void insertion_sort(int32_t *a, int32_t n) {
  int32_t i, j, p;

  for (i=1; i<n; i++) {
    p = a[i];
    if (p < a[i-1]) {
      j = i-1;
      do {
	a[j+1] = a[j];
	j --;
      } while (j >= 0 && a[j] > p);
      a[j+1] = p;
    }
  }
}

#if 0

// unused function
static void finish_sort2(int32_t *a, int32_t n) {
  int32_t i, p;

  for (i=1; i<n; i++) {
    p = a[i];
    if (p < a[i-1]) {
      a[i] = a[i-1];
      a[i-1] = p;
    }
  }
}

#endif

// first implementation
static void quick_sort(int32_t *a, int32_t low, int32_t high) {
  int32_t p, i, j, aux;

  if (high <= low + 1) return;

  p = a[(low + high)/2];
  i = low - 1;
  j = high;

  for (;;) {
    do { i ++; } while (a[i] < p);
    if (j <= i) break;
    do { j --; } while (a[j] > p);
    if (j <= i) break;

    aux = a[i]; a[i] = a[j]; a[j] = aux;
  }

  quick_sort(a, low, i);
  quick_sort(a, i, high);
}

static void sort(int32_t *a, int32_t n) {
  quick_sort(a, 0, n);
}


// variant
static void quick_sort2(int32_t *a, int32_t low, int32_t high) {
  int32_t i, j, p, aux;

  if (high <= low + 1) return;

  p = a[low];
  i = low;
  j = high;

  do { j--; } while (a[j] > p);
  do { i++; } while (i <= j && a[i] < p);

  while (i < j) {
    aux = a[i]; a[i] = a[j]; a[j] = aux;

    do { j--; } while (a[j] > p);
    do { i++; } while (a[i] < p);
  }

  a[low] = a[j];
  a[j] = p;

  quick_sort2(a, low, j);
  quick_sort2(a, j+1, high);
}

static void sort2(int32_t *a, int32_t n) {
  quick_sort2(a, 0, n);
}


// another variant
static void quick_sort3(int32_t *a, int32_t low, int32_t high) {
  int32_t i, j, p, aux;

  if (high <= low + 1) return;

  i = low;
  j = high - 1;
  p = a[i];
  i ++;

  while (i <= j) {
    if (a[i] < p) {
      i ++;
    } else {
      aux = a[i]; a[i] = a[j]; a[j] = aux;
      j --;
    }
  }

  a[low] = a[j];
  a[j] = p;

  quick_sort3(a, low, j);
  quick_sort3(a, j+1, high);
}

static void sort3(int32_t *a, int32_t n) {
  quick_sort3(a, 0, n);
}


// variant 4 assumes a[high] is larger than all elements in a[low ..high-1]
static void quick_sort4(int32_t *a, int32_t low, int32_t high) {
  int32_t i, j, p, aux;

  //  if (high <= low + 1) return;

  p = a[low];
  i = low;
  j = high;

  for (;;) {
    do { j--; } while (a[j] > p);
    do { i++; } while (a[i] < p);
    if (i >= j) break;
    aux = a[i]; a[i] = a[j]; a[j] = aux;
  }

  a[low] = a[j];
  a[j] = p;

  if (j > low + 1) quick_sort4(a, low, j);
  j ++;
  if (high > j + 1) quick_sort4(a, j, high);
}

static void sort4(int32_t *a, int32_t n) {
  a[n] = INT32_MAX;
  if (n >= 2) quick_sort4(a, 0, n);
}


// variant 4 assumes a[high] is larger than all elements in a[low ..high-1]
static void quick_sort4var(int32_t *a, int32_t low, int32_t high);

static void quick_sort4var_aux(int32_t *a, int32_t low, int32_t high) {
  if (high <= low + 12) {
    insertion_sort(a + low, high - low);
  } else {
    quick_sort4var(a, low, high);
  }
}

static void quick_sort4var(int32_t *a, int32_t low, int32_t high) {
  int32_t i, j, p, aux;

  p = a[low];
  i = low;
  j = high;

  for (;;) {
    do { j--; } while (a[j] > p);
    do { i++; } while (a[i] < p);
    if (i >= j) break;
    aux = a[i]; a[i] = a[j]; a[j] = aux;
  }

  a[low] = a[j];
  a[j] = p;

  quick_sort4var_aux(a, low, j);
  quick_sort4var_aux(a, j+1, high);
}

static void sort4var(int32_t *a, int32_t n) {
  quick_sort4var_aux(a, 0, n);
}


// variant 4 assumes a[high] is larger than all elements in a[low ..high-1]
static void quick_sort4var2(int32_t *a, int32_t low, int32_t high) {
  int32_t i, j, p, aux;

  p = a[low];
  i = low;
  j = high;

  for (;;) {
    do { j--; } while (a[j] > p);
    do { i++; } while (a[i] < p);
    if (i >= j) break;
    aux = a[i]; a[i] = a[j]; a[j] = aux;
  }

  a[low] = a[j];
  a[j] = p;

  if (j > low + 9) quick_sort4var2(a, low, j);
  j ++;
  if (high > j + 9) quick_sort4var2(a, j, high);
}

static void sort4var2(int32_t *a, int32_t n) {
  if (n > 9) quick_sort4var2(a, 0, n);
  insertion_sort(a, n);
}



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

static void copy_array(int32_t *a, int32_t *b, int32_t n) {
  int32_t i;
  for (i=0; i<n; i++) a[i] = b[i];
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

static void check_sorted(int32_t *a, int32_t n) {
  int32_t i;

  n --;
  for (i=0; i<n; i++) {
    assert(a[i] <= a[i+1]);
  }
}

static double time1, time2, time3, time4, time4var, time4var2, itime;
static double total1, total2, total3, total4, total4var, total4var2, itotal;

static void compare(int32_t *a, int32_t n) {
  int32_t *b;
  int32_t i;
  double runtime;

  b = (int32_t *) safe_malloc((n + 1) * sizeof(int32_t));

  runtime = get_cpu_time();
  for (i=0; i<5000; i++) {
    copy_array(b, a, n);
    insertion_sort(b, n);
  }
  runtime = get_cpu_time() - runtime;
  //    printf("isort: %.3f s\n", runtime);
  itime += runtime;

  runtime = get_cpu_time();
  for (i=0; i<5000; i++) {
    copy_array(b, a, n);
    sort(b, n);
  }
  runtime = get_cpu_time() - runtime;
  //  printf("sort1: %.3f s\n", runtime);
  time1 += runtime;

  runtime = get_cpu_time();
  for (i=0; i<5000; i++) {
    copy_array(b, a, n);
    sort2(b, n);
  }
  runtime = get_cpu_time() - runtime;
  //  printf("sort2: %.3f s\n", runtime);
  time2 += runtime;

  runtime = get_cpu_time();
  for (i=0; i<5000; i++) {
    copy_array(b, a, n);
    sort3(b, n);
  }
  runtime = get_cpu_time() - runtime;
  //  printf("sort3: %.3f s\n", runtime);
  time3 += runtime;

  runtime = get_cpu_time();
  for (i=0; i<5000; i++) {
    copy_array(b, a, n);
    sort4(b, n);
  }
  runtime = get_cpu_time() - runtime;
  //  printf("sort4: %.3f s\n\n", runtime);
  time4 += runtime;

  runtime = get_cpu_time();
  for (i=0; i<5000; i++) {
    copy_array(b, a, n);
    sort4var(b, n);
  }
  runtime = get_cpu_time() - runtime;
  //  printf("sort4var: %.3f s\n\n", runtime);
  time4var += runtime;

  runtime = get_cpu_time();
  for (i=0; i<5000; i++) {
    copy_array(b, a, n);
    sort4var2(b, n);
  }
  runtime = get_cpu_time() - runtime;
  //  printf("sort4var2: %.3f s\n\n", runtime);
  time4var2 += runtime;

  safe_free(b);
}


int main() {
  int32_t *a;
  int32_t n, j;

  a = (int32_t *) safe_malloc(1000 * sizeof(int32_t));

  constant_array(a, 20);
  printf("input:  ");
  print_array(a, 20);
  insertion_sort(a, 20);
  printf("isort:  ");
  print_array(a, 20);
  printf("\n");

  increasing_array(a, 20);
  printf("input:  ");
  print_array(a, 20);
  insertion_sort(a, 20);
  printf("isort:  ");
  print_array(a, 20);
  printf("\n");

  decreasing_array(a, 20);
  printf("input:  ");
  print_array(a, 20);
  insertion_sort(a, 20);
  printf("isort:  ");
  print_array(a, 20);
  printf("\n");

  for (n=0; n<20; n++) {
    for (j=0; j<10; j++) {
      random_array(a, n);
      printf("input:  ");
      print_array(a, n);
      insertion_sort(a, n);
      printf("isort:  ");
      print_array(a, n);
      printf("\n");
      check_sorted(a, n);
    }
  }

  total1 = 0.0;
  total2 = 0.0;
  total3 = 0.0;
  total4 = 0.0;
  total4var = 0.0;
  total4var2 = 0.0;
  itotal = 0.0;

  for (n=0; n<100; n ++) {
    time1 = 0.0;
    time2 = 0.0;
    time3 = 0.0;
    time4 = 0.0;
    time4var = 0.0;
    time4var2 = 0.0;
    itime = 0.0;

    printf("size %"PRId32"\n", n);
    fflush(stdout);
    for (j=0; j<100; j++) {
      random_array(a, n);
      compare(a, n);
      if (j % 10 == 9) {
	printf(".");
	fflush(stdout);
      }
    }

    printf("\nisort: %.3f s\n", itime);
    printf("sort1: %.3f s\n", time1);
    printf("sort2: %.3f s\n", time2);
    printf("sort3: %.3f s\n", time3);
    printf("sort4: %.3f s\n", time4);
    printf("sort4var: %.3f s\n", time4var);
    printf("sort4var2: %.3f s\n", time4var2);
    printf("\n");

    total1 += time1;
    total2 += time2;
    total3 += time3;
    total4 += time4;
    total4var += time4var;
    total4var2 += time4var2;
    itotal += itime;
  }

  printf("Total time\n");
  printf("isort: %.3f s\n", itotal);
  printf("sort1: %.3f s\n", total1);
  printf("sort2: %.3f s\n", total2);
  printf("sort3: %.3f s\n", total3);
  printf("sort4: %.3f s\n", total4);
  printf("sort4var: %.3f s\n", total4var);
  printf("sort4var2: %.3f s\n", total4var2);

  safe_free(a);
  return 0;
}
