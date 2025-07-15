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

/*
 * Test hash-consing of power products
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "terms/pprod_table.h"
#include "terms/terms.h"


/*
 * Display power products
 */
static void print_varexp_array(FILE *f, varexp_t *a, uint32_t n) {
  uint32_t i, d;

  if (n == 0) {
    fprintf(f, "[]");
    return;
  }
  d = a[0].exp;
  fprintf(f, "[x_%"PRId32, a[0].var);
  if (d != 1) {
    fprintf(f, "^%"PRIu32, d);
  }
  for (i=1; i<n; i++) {
    d = a[i].exp;
    fprintf(f, " x_%"PRId32, a[i].var);
    if (d != 1) {
      fprintf(f, "^%"PRIu32, d);
    }
  }
  fprintf(f, "]");
}


static void print_pp_buffer0(FILE *f, pp_buffer_t *b) {
  print_varexp_array(f, b->prod, b->len);
}

static void print_pprod0(FILE *f, pprod_t *p) {
  if (pp_is_var(p)) {
    fprintf(f, "[x_%"PRId32"]", var_of_pp(p));
  } else if (pp_is_empty(p)) {
    fprintf(f, "[]");
  } else {
    print_varexp_array(f, p->prod, p->len);
  }
}


/*
 * Print table
 */
static void print_pprod_table(FILE *f, pprod_table_t *table) {
  pprod_t *p;
  uint32_t i, n;
  int32_t l;

  fprintf(f, "pprod_table %p\n", table);
  fprintf(f, "  size = %"PRIu32"\n", table->pprods.size);
  fprintf(f, "  nelems = %"PRIu32"\n", indexed_table_nelems(&table->pprods));
  fprintf(f, "  free_idx = %"PRId32"\n", table->pprods.free_idx);
  fprintf(f, "  content:\n");
  n = indexed_table_nelems(&table->pprods);
  for (i=0; i<n; i++) {
    p = indexed_table_elem(pprod_table_elem_t, &table->pprods, i)->pprod;
    if (!has_int_tag(p)) {
      fprintf(f, "  data[%"PRIu32"] = ", i);
      print_varexp_array(f, p->prod, p->len);
      fprintf(f, "\n");
    }
  }
  if (table->pprods.free_idx >= 0) {
    fprintf(f, "  free list:");
    l = table->pprods.free_idx;
    do {
      fprintf(f, " %"PRId32, l);
      l = untag_i32(indexed_table_elem(pprod_table_elem_t, &table->pprods, l)->pprod);
    } while (l >= 0);
    fprintf(f, "\n");
  }
}


/*
 * Table + buffer for tests
 */
static pprod_table_t ptbl;
static pp_buffer_t buffer;

/*
 * Array of all power products
 */
#define NUM_PRODS 300

static pprod_t *p[NUM_PRODS];
static uint32_t num_prods;

/*
 * Check whether q is equal to a product p[k]
 * - if so, check whether p[k] = q
 * - otherwise, add a at the end of the array
 */
static void check_product(pprod_t *q) {
  uint32_t k;

  for (k=0; k<num_prods; k++) {
    if (pprod_equal(q, p[k])) {
      break;
    }
  }

  if (k < num_prods) {
    printf("--> equal to p[%"PRIu32"]\n", k);
    if (p[k] != q) {
      printf("BUG: HASH CONSING FAILED\n");
      fflush(stdout);
      abort();
    }
  } else if (num_prods < NUM_PRODS) {
    printf("--> stored as p[%"PRIu32"]\n", k);
    p[k] = q;
    num_prods ++;
  }
}


int main(void) {
  uint32_t i, j, n;
  pprod_t *q;

  init_pprod_table(&ptbl, 10);
  init_pp_buffer(&buffer, 10);

  p[0] = empty_pp;
  p[1] = var_pp(0);
  p[2] = var_pp(1);
  p[3] = var_pp(2);
  p[4] = var_pp(3);
  num_prods = 5;

  for (i=0; i<5; i++) {
    for (j=0; j<5; j++) {
      q = pprod_mul(&ptbl, p[i], p[j]);
      print_pprod0(stdout, p[i]);
      printf(" * ");
      print_pprod0(stdout, p[j]);
      printf(" = ");
      print_pprod0(stdout, q);
      printf("\n");
      check_product(q);
      printf("\n");
    }
  }

  n = num_prods;
  for (i=0; i<n; i++) {
    for (j=0; j<n; j++) {
      q = pprod_mul(&ptbl, p[i], p[j]);
      print_pprod0(stdout, p[i]);
      printf(" * ");
      print_pprod0(stdout, p[j]);
      printf(" = ");
      print_pprod0(stdout, q);
      printf("\n");
      check_product(q);
      printf("\n");
    }
  }

  for (i=0; i<num_prods; i++) {
    pp_buffer_set_pprod(&buffer, p[i]);
    printf("p[%"PRIu32"] = %p = ", i, p[i]);
    print_pprod0(stdout, p[i]);
    printf("\n");
    printf("buffer: ");
    print_pp_buffer0(stdout, &buffer);
    printf("\n");
    q = pprod_from_buffer(&ptbl, &buffer);
    printf("prod from buffer = %p = ", q);
    print_pprod0(stdout, q);
    if (q != p[i]) {
      printf("BUG: HASH CONSING FAILED\n");
      fflush(stdout);
      abort();
    }
    printf("\n\n");
  }

  // delete the non-trivial products
  for (i=5; i<num_prods; i++) {
    q = p[i];
    assert(q != empty_pp && q != end_pp && !pp_is_var(q));
    printf("deleting p[%"PRIu32"] = %p = ", i, q);
    print_pprod0(stdout, q);
    printf("\n");
    delete_pprod(&ptbl, q);
  }
  printf("\n\n");

  p[5] = var_pp(4);
  num_prods = 6;

  // reconstruct more products
  q = pprod_mul(&ptbl, p[1], p[2]);
  printf("checking q = %p = ", q);
  print_pprod0(stdout, q);
  printf("\n");
  check_product(q);
  printf("\n");

  q = pprod_mul(&ptbl, p[2], p[3]);
  printf("checking q = %p = ", q);
  print_pprod0(stdout, q);
  printf("\n");
  check_product(q);
  printf("\n");

  q = pprod_mul(&ptbl, p[3], p[2]);
  printf("rechecking q = %p = ", q);
  print_pprod0(stdout, q);
  printf("\n");
  check_product(q);
  printf("\n");

  q = pprod_mul(&ptbl, p[3], p[4]);
  printf("checking q = %p = ", q);
  print_pprod0(stdout, q);
  printf("\n");
  check_product(q);
  printf("\n");

  q = pprod_mul(&ptbl, p[4], p[3]);
  printf("rechecking q = %p = ", q);
  print_pprod0(stdout, q);
  printf("\n");
  check_product(q);
  printf("\n");

  q = pprod_mul(&ptbl, p[4], p[5]);
  printf("checking q = %p = ", q);
  print_pprod0(stdout, q);
  printf("\n");
  check_product(q);
  printf("\n");

  q = pprod_mul(&ptbl, p[0], p[5]);
  printf("checking q = %p = ", q);
  print_pprod0(stdout, q);
  printf("\n");
  check_product(q);
  printf("\n");

  printf("*** Table content before GC ***\n");
  print_pprod_table(stdout, &ptbl);
  pprod_table_set_gc_mark(&ptbl, p[num_prods - 1]);
  pprod_table_gc(&ptbl);
  printf("\n*** Table content after GC ***\n");
  print_pprod_table(stdout, &ptbl);
  printf("\n");

  delete_pp_buffer(&buffer);
  delete_pprod_table(&ptbl);


  return 0;
}
