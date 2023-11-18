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
#include <inttypes.h>

#include "scratch/booleq_table.h"


static void show_literal(literal_t l) {
  if (is_neg(l)) printf("~");
  printf("p%"PRId32, var_of(l));
}

/*
 * Equality: l := (eq a b)
 */
static void show_booleq(literal_t l, literal_t a, literal_t b) {
  show_literal(l);
  printf(" := (eq ");
  show_literal(a);
  printf(" ");
  show_literal(b);
  printf(")");
}

/*
 * Show equality i := eq
 */
static void show_eq(bvar_t i, booleq_t *b) {
  show_booleq(pos_lit(i), b->lit[0], b->lit[1]);
}

/*
 * Show all equalities stored in table
 */
static void show_table(booleq_table_t *table) {
  uint32_t i;
  int32_t k;

  printf("table %p\n", table);
  printf("  nvars: %"PRIu32"\n", table->nvars);
  printf("  dsize: %"PRIu32"\n", table->dsize);
  printf("  neqs:  %"PRIu32"\n", table->neqs);
  printf("  esize; %"PRIu32"\n", table->esize);

  for (i=0; i<table->nvars; i++) {
    k = table->def[i];
    if (k >= 0) {
      printf("  eq[%"PRId32"]: ", k);
      show_eq(i, table->eq + k);
      printf("\n");
    }
  }

  printf("\n");
}


static void test_addeq(booleq_table_t *table, literal_t l, literal_t a, literal_t b) {
  literal_t ta, tb;

  printf("adding: ");
  show_booleq(l, a, b);
  printf("\n");

  if (literal_is_eq(table, l)) {
    printf("*** ERROR: ");
    show_literal(l);
    printf(" already in the table ****\n");
    fflush(stdout);
  } else {
    booleq_table_record_eq(table, l, a, b);
    if (!literal_is_eq(table, l)) {
      printf("*** BUG: addeq failed ***\n");
      fflush(stdout);
      exit(1);
    }

    if (get_booleq(table, l, &ta, &tb)) {
      if (! (ta == a && tb == b) || (ta == not(a) && tb == not(b))) {
	printf("*** BUG: invalid literals returned by get_booleq ***\n");
	fflush(stdout);
	exit(1);
      }
    } else {
      printf("*** BUG: get_booleq failed for ");
      show_literal(l);
      printf(" ***\n");
      fflush(stdout);
      exit(1);
    }

    if (get_booleq(table, not(l), &ta, &tb)) {
      if (! (ta == not(a) && tb == b) || (ta == a && tb == not(b))) {
	printf("*** BUG: invalid literals returned by get_booleq ***\n");
	fflush(stdout);
	exit(1);
      }
    } else {
      printf("*** BUG: get_booleq failed for ");
      show_literal(not(l));
      printf(" ***\n");
      fflush(stdout);
      exit(1);
    }

  }
}



static booleq_table_t table;




int main(void) {
  init_booleq_table(&table);

  printf("**** INITIAL TABLE ****\n");
  show_table(&table);

  test_addeq(&table, 20, 8, 10);
  test_addeq(&table, 1000, 10, 12);
  test_addeq(&table, 23, 12, 14);
  test_addeq(&table, 901, 14, 16);
  test_addeq(&table, 800, 16, 18);

  printf("**** AFTER ADDITIONS ****\n");
  show_table(&table);

  reset_booleq_table(&table);
  printf("**** AFTER RESET ****\n");
  show_table(&table);

  test_addeq(&table, 20, 8, 10);
  test_addeq(&table, 1000, 10, 12);
  test_addeq(&table, 23, 12, 14);
  test_addeq(&table, 901, 14, 16);
  test_addeq(&table, 800, 16, 18);

  printf("**** AFTER ADDITIONS ****\n");
  show_table(&table);

  delete_booleq_table(&table);

  return 0;
}
