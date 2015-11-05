/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>

#include "utils/int_bv_sets.h"

#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline int random(void) {
  return rand();
}

#endif

static int_bvset_t s;

static void print_set(int_bvset_t *s) {
  uint32_t i, k, n;

  printf("set %p\n", s);
  printf("  size = %" PRIu32" (%"PRIu32" bytes)\n", s->size, s->size/8);
  printf("  nelems = %"PRIu32"\n", s->nbits);
  n = s->nbits;
  if (n == 0) {
    printf("  empty\n");
  } else {
    printf("  content:");
    k = 10;
    for (i=0; i<n; i++) {
      if (int_bvset_member(s, i)) {
	k ++;
	if (k > 10) {
	  printf("\n    %3"PRIu32, i);
	  k = 0;
	} else {
	  printf(" %3"PRIu32, i);
	}
      }
    }
    printf("\n");
  }
}


int main(void) {
  uint32_t x, i, n;

  printf("\n"
	 "*****************\n"
	 "*    TEST 1     *\n"
	 "*****************\n\n");

  printf("Initial set\n");
  init_int_bvset(&s, 2);
  print_set(&s);

  x = 7;
  printf("\nAdding %"PRIu32": ", x);
  if (int_bvset_add_check(&s, x)) {
    printf("new element\n");
  } else {
    printf("no change\n");
  }
  print_set(&s);


  x = 8;
  printf("\nAdding %"PRIu32": ", x);
  if (int_bvset_add_check(&s, x)) {
    printf("new element\n");
  } else {
    printf("no change\n");
  }
  print_set(&s);

  n = 400;
  for (i=0; i<n; i++) {
    x = random() % 200;
    printf("\nAdding %"PRIu32": ", x);
    if (int_bvset_add_check(&s, x)) {
      printf("new element\n");
    } else {
      printf("no change\n");
    }
    print_set(&s);
  }

  printf("\nCheck members\n");
  for (i=0; i<=200; i++) {
    printf(" %"PRIu32": ", i);
    if (int_bvset_member(&s, i)) {
      printf("present\n");
    } else {
      printf("absent\n");
    }
  }

  printf("\n\n"
	 "*****************\n"
	 "*    TEST 2     *\n"
	 "*****************\n\n");

  reset_int_bvset(&s);
  printf("After reset\n");
  print_set(&s);

  n = 500;
  for (i=0; i<n; i++) {
    x = random() % 1000;
    printf("\nAdding %"PRIu32": ", x);
    if (int_bvset_add_check(&s, x)) {
      printf("new element\n");
    } else {
      printf("no change\n");
    }
    print_set(&s);
  }

  printf("\nCheck members\n");
  for (i=0; i<=1000; i++) {
    printf(" %"PRIu32": ", i);
    if (int_bvset_member(&s, i)) {
      printf("present\n");
    } else {
      printf("absent\n");
    }
  }


  delete_int_bvset(&s);

  return 0;
}
