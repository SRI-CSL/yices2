/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <inttypes.h>


#include "utils/ptr_array_sort2.h"

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
 * Create a random pointer
 */
static void *random_pointer(void) {
  return (void *) ((uintptr_t) random());
}


/*
 * Initialize array a with constant pointer
 */
static void set_array_constant(void **a, uint32_t n) {
  void *p;
  uint32_t i;

  p = random_pointer();
  for (i=0; i<n; i++) {
    a[i] = p;
  }
}


/*
 * Initialize array a with an increasing set of pointers
 */
static void set_array_increasing(void **a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    a[i] = a + i;
  }
}


/*
 * Initialize a with a decreasing set of pointers
 */
static void set_array_decreasing(void **a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    a[i] = a + (n - 1 - i);
  }
}


/*
 * Random array
 */
static void set_array_random(void **a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    a[i] = random_pointer();
  }
}



/*
 * Print array a
 */
static void print_array(void **a, uint32_t n) {
  uint32_t i, l;

  l = 10;
  for (i=0; i<n; i++) {
    if (l == 0) {
      printf("\n\t");
      l = 10;
    }
    l --;
    printf(" %p", a[i]);
  }
  printf("\n");
}


/*
 * Check that a is sorted
 */
static void check_sorted(void **a, uint32_t n) {
  uint32_t i;

  if (n > 0) {
    n --;
    for (i=0; i<n; i++) {
      assert(a[i] <= a[i+1]);
    }
  }
}


/*
 * Comparison function
 */
static bool cmp_ptr(void *data, void *x, void *y) {
  return ((uintptr_t) x) < ((uintptr_t) y);
}


/*
 * Test: sort array a then check whether it's sorted
 */
static void test_sort(void **a, uint32_t n) {
  printf("input:  ");
  print_array(a, n);
  ptr_array_sort2(a, n, NULL, cmp_ptr);
  printf("output: ");
  print_array(a, n);
  check_sorted(a, n);
  printf("\n");
}


/*
 * Test array
 */
static void *a[100];



int main(void) {
  uint32_t n;

  for (n=0; n <= 100; n += 20) {
    printf("\n==== size %"PRIu32" ====\n", n);
    set_array_constant(a, n);
    test_sort(a, n);
    set_array_increasing(a, n);
    test_sort(a, n);
    set_array_decreasing(a, n);
    test_sort(a, n);
    set_array_random(a, n);
    test_sort(a, n);
    set_array_random(a, n);
    test_sort(a, n);
  }

  return 0;
}
