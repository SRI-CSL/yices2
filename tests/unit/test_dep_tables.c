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
#include <assert.h>

#include "utils/dep_tables.h"
#include "utils/index_vectors.h"

#ifdef MINGW

static inline long int random(void) {
  return rand();
}

#endif

static void print_vector(int32_t *v) {
  uint32_t i, n;

  assert(v != NULL);
  n = iv_size(v);
  for (i=0; i<n; i++) {
    printf(" %"PRId32, v[i]);
  }
}

static void print_dep_table(dep_table_t *table) {
  int32_t *v;
  uint32_t i, n;

  printf("dep table %p\n", table);
  printf("  size = %"PRIu32"\n", table->size);
  printf("  nelems = %"PRIu32"\n", table->nelems);
  printf("  content:\n");

  n = table->nelems;
  for (i=0; i<n; i++) {
    v = get_dependents(table, i);
    if (v != NULL) {
      printf("   dep[%"PRId32"] = {", i);
      print_vector(v);
      printf(" }\n");
    }
  }

  printf("\n");
}


/*
 * n random additions to table
 */
static void test_additions(dep_table_t *table, uint32_t n) {
  int32_t i, j;
  int32_t *v;

  while (n > 0) {
    i = (int32_t) (random() & 255);
    j = (int32_t) (random() & 255);
    printf("test add %"PRId32" to dep[%"PRId32"]: ", j, i);
    add_dependent(table, i, j);
    // check that j is the last element of dep[i];
    v = get_dependents(table, i);
    if (v == NULL) {
      printf("BUG: empty vector\n");
      exit(1);
    }
    if (index_vector_last(v) != j) {
      printf("BUG: addition failed\n");
      exit(1);
    }
    printf("ok\n");
    n --;
  }
}


/*
 * Global table for testing
 */
static dep_table_t table;

int main(void) {
  init_dep_table(&table, 0);

  printf("--- Initial table: size 0 ---\n");
  print_dep_table(&table);

  test_additions(&table, 50);
  printf("\n--- After 50 additions ---\n");
  print_dep_table(&table);

  reset_dep_table(&table);
  printf("\n--- After reset ---\n");
  print_dep_table(&table);

  test_additions(&table, 3000);
  printf("\n--- After 3000 additions ---\n");
  print_dep_table(&table);

  delete_dep_table(&table);

  return 0;
}
