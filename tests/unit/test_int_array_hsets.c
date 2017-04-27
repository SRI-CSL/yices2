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
#include <inttypes.h>

#include "utils/int_array_hsets.h"


static void print_array(uint32_t n, int32_t *a) {
  uint32_t i;

  if (n == 0) {
    printf("[]");
  } else {
    printf("[%"PRId32, a[0]);
    for (i=1; i<n; i++) {
      printf(" %"PRId32, a[i]);
    }
    printf("]");
  }
}

static void print_harray(harray_t *set) {
  uint32_t i, n;

  n = set->nelems;
  if (n == 0) {
    printf("[]");
  } else {
    printf("[%"PRId32, set->data[0]);
    for (i=1; i<n; i++) {
      printf(" %"PRId32, set->data[i]);
    }
    printf("]");
  }
}


static void print_harray_set(int_array_hset_t *table) {
  uint32_t i;
  harray_t *d;

  printf("table %p\n", table);
  printf("  size = %"PRIu32"\n", table->size);
  printf("  nelems = %"PRIu32"\n", table->nelems);
  printf("  ndeleted = %"PRIu32"\n", table->ndeleted);
  printf("  content:\n");

  for (i=0; i<table->size; i++) {
    d = table->data[i];
    if (d != NULL && d != DELETED_HARRAY) {
      printf("    ");
      print_harray(d);
      printf("\n");
    }
  }
  printf("\n");
}


/*
 * Add a record
 */
static void test_get(int_array_hset_t *table, uint32_t n, int32_t *a) {
  harray_t *d;

  printf("Test get ");
  print_array(n, a);
  printf("\n");

  d = int_array_hset_get(table, n, a);
  printf("result: %p = ", d);
  print_harray(d);
  printf("\n");
}


/*
 * Search for a record
 */
static void test_find(int_array_hset_t *table, uint32_t n, int32_t *a) {
  harray_t *d;

  printf("Test find ");
  print_array(n, a);
  printf("\n");

  d = int_array_hset_find(table, n, a);
  if (d != NULL) {
    printf("result: %p = ", d);
    print_harray(d);
  } else {
    printf("result: NULL");
  }
  printf("\n");
}


/*
 * Remove a record
 */
static void test_remove(int_array_hset_t *table, uint32_t n, int32_t *a) {
  printf("Test remove ");
  print_array(n, a);
  printf("\n");
  int_array_hset_remove(table, n, a);
}


#define N 20
static int_array_hset_t table;
static int32_t aux[20];

int main(void) {
  uint32_t i, j;

  init_int_array_hset(&table, 4);
  printf("\n*** Initial table ***\n");
  print_harray_set(&table);

  for (j=0; j<20; j++) {
    aux[j] = j;
  }

  for (i=0; i<9; i++) {
    test_get(&table, i, aux);
    test_find(&table, i, aux);
  }

  printf("\n*** After additions ***\n");
  print_harray_set(&table);

  test_find(&table, 10, aux);
  test_find(&table, 15, aux);

  reset_int_array_hset(&table);
  printf("\n*** After reset ***\n");
  print_harray_set(&table);

  for (i=0; i<14; i += 2) {
    test_get(&table, i, aux);
  }

  printf("\n*** After additions ***\n");
  print_harray_set(&table);

  for (i=0; i<20; i++) {
    test_find(&table, i, aux);
  }

  for (i=0; i<10; i++) {
    test_remove(&table, i, aux);
  }

  printf("\n*** After removals ***\n");
  print_harray_set(&table);

  for (i=0; i<20; i++) {
    test_find(&table, i, aux);
  }


  delete_int_array_hset(&table);

  return 0;
}
