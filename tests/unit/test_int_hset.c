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
