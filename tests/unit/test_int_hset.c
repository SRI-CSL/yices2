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

#include "utils/int_hash_sets.h"

#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline int random(void) {
  return rand();
}

#endif

static int_hset_t s;

static void print_set(int_hset_t *s) {
  uint32_t i, n;

  printf("set %p\n", s);
  printf("  size = %" PRIu32"\n", s->size);
  printf("  threshold = %"PRIu32"\n", s->resize_threshold);
  printf("  nelems = %"PRIu32"\n", s->nelems);
  printf("  content:\n");
  if (s->z_flag) {
    printf("    z_flag = true\n");
  } else {
    printf("    z_flag = false\n");
  }
  n = s->size;
  for (i=0; i<n; i++) {
    if (s->data[i] != 0) {
      printf("    data[%"PRIu32"] = %"PRIu32"\n", i, s->data[i]);
    }
  }
}

static void print_closed_set(int_hset_t *s) {
  uint32_t i, n;

  printf("set %p\n", s);
  printf("  size = %" PRIu32"\n", s->size);
  printf("  threshold = %"PRIu32"\n", s->resize_threshold);
  printf("  nelems = %"PRIu32"\n", s->nelems);
  printf("  content:\n");
  if (s->z_flag) {
    printf("    z_flag = true\n");
  } else {
    printf("    z_flag = false\n");
  }
  n = s->nelems;
  for (i=0; i<n; i++) {
    printf("    data[%"PRIu32"] = %"PRIu32"\n", i, s->data[i]);
  }
}

int main(void) {
  uint32_t x, i, n;

  printf("Initial set\n");
  init_int_hset(&s, 2);
  print_set(&s);

  n = 40;
  for (i=0; i<n; i++) {
    x = random() % 20;
    printf("\nAdding %"PRIu32": ", x);
    if (int_hset_add(&s, x)) {
      printf("new element\n");
    } else {
      printf("no change\n");
    }
    print_set(&s);
  }

  printf("\nCheck members\n");
  for (i=0; i<=20; i++) {
    printf(" %"PRIu32": ", i);
    if (int_hset_member(&s, i)) {
      printf("present\n");
    } else {
      printf("absent\n");
    }
  }

  int_hset_close(&s);
  printf("\nFINAL SET\n");
  print_closed_set(&s);

  delete_int_hset(&s);

  return 0;
}
