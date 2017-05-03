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
#include <stdlib.h>
#include <assert.h>
#include <inttypes.h>


#include "utils/ptr_array_sort.h"

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
 * Test: sort array a then check whether it's sorted
 */
static void test_sort(void **a, uint32_t n) {
  printf("input:  ");
  print_array(a, n);
  ptr_array_sort(a, n);
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
