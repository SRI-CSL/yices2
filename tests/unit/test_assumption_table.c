/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

#include "frontend/common/assumption_table.h"
#include "utils/int_vectors.h"

static void print_assumption(FILE *f, assumption_t *a) {
  if (a->polarity) {
    fprintf(f, "%s: t!%"PRId32, a->name, a->term);
  } else {
    fprintf(f, "(not %s): t!%"PRId32, a->name, a->term);
  }
}

static void print_table(FILE *f, assumption_table_t *table) {
  uint32_t i, n;

  fprintf(f, "Table: %p\n", table);
  fprintf(f, "  size:   %"PRIu32"\n", table->size);
  fprintf(f, "  nelems: %"PRIu32"\n", table->nelems);
  fprintf(f, "  content:\n");
  
  n = table->nelems;
  for (i=0; i<n; i++) {
    fprintf(f, "    ");  
    print_assumption(f, table->data + i);
    fprintf(f, "\n");
  }
  fprintf(f, "\n");
}

static void print_table_index(FILE *f, assumption_table_t *table) {
  uint32_t i, n;

  fprintf(f, "Table: %p\n", table);
  fprintf(f, "  index: %p\n", table->index);
  fprintf(f, "  index_size: %"PRIu32"\n", table->index_size);
  fprintf(f, "  indices:\n");
  n = table->index_size;
  for (i=0; i<n; i++) {
    fprintf(f, "    %"PRId32"\n", table->index[i]);
  }
  fprintf(f, "\n");
}


static void check_present(assumption_table_t *table, term_t x) {
  assumption_t *a;

  a = assumption_table_get(table, x);
  if (a == NULL) {
    fprintf(stderr, "*** BUG: failed to find assumption t!%"PRId32" ***\n", x);
    exit(1);
  }
  if (a->term != x) {
    fprintf(stderr, "*** BUG: wrong record for assumption  t!%"PRId32" ***\n", x);
    exit(1);
  }

  printf("Success: found term t!%"PRId32": ", x);
  print_assumption(stdout, a);
  printf("\n");
}

static void check_absent(assumption_table_t *table, term_t x) {
  assumption_t *a;

  a = assumption_table_get(table, x);
  if (a != NULL) {
    fprintf(stderr, "*** BUG: found assumption t%"PRId32" ***\n", x);
    print_assumption(stderr, a);
    exit(1);
  }
  printf("Success: term t!%"PRId32" not found as expected\n", x);
}


static assumption_table_t table;

int main(void) {
  ivector_t v;
  int32_t i;
  char  buffer[20];

  init_assumption_table(&table);
  printf("--- initial table ---\n");
  print_table(stdout, &table);
  print_table_index(stdout, &table);

  assumption_table_add(&table, 12, "C", false);
  assumption_table_add(&table, 4, "A", true);
  assumption_table_add(&table, 5, "A", false);
  assumption_table_add(&table, 10, "B", true);
  assumption_table_add(&table, 10, "X", false);
  assumption_table_add(&table, 10, "Y", true);

  printf("--- after adding assumptions ---\n");
  print_table(stdout, &table);
  print_table_index(stdout, &table);

  assumption_table_build_index(&table);
  printf("--- after building index ---\n");
  print_table(stdout, &table);
  print_table_index(stdout, &table);

  init_ivector(&v, 10);
  collect_assumptions(&table, &v);
  printf("--- assumed terms ---\n");
  for (i=0; i<v.size; i++) {
    printf(" t!%"PRId32, v.data[i]);
  }
  printf("\n\n");

  check_present(&table, 4);
  check_present(&table, 5);
  check_present(&table, 10);
  check_present(&table, 12);
  printf("\n");
  check_absent(&table, 11);
  check_absent(&table, 0);
  printf("\n");

  reset_assumption_table(&table);
  printf("--- after reset ---\n");
  print_table(stdout, &table);
  print_table_index(stdout, &table);

  for (i=0; i<200; i++) {
    snprintf(buffer, 20, "A%"PRId32, i);
    assumption_table_add(&table, i, buffer, true);
  }

  printf("--- after 200 additions ---\n");
  print_table(stdout, &table);
  print_table_index(stdout, &table);

  
  
  delete_assumption_table(&table);
  delete_ivector(&v);

  return 0;
}
