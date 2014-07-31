/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>

#include "terms/types.h"
#include "io/type_printer.h"
#include "utils/refcount_strings.h"


#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif


/*
 * Display a type substitution
 * - v[0 ... n-1] = type variables
 * - u[0 ... n-1] = types
 */
static void show_type_subst(FILE *f, type_table_t *table, type_t v[], type_t u[], uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    print_type(f, table, v[i]);
    fputs(" := ", f);
    print_type(f, table, u[i]);
    fputc('\n', f);
  }
  fflush(f);
}


/*
 * Test substitution
 */
static void test_type_subst(type_table_t *table, type_t tau, type_t v[], type_t u[], uint32_t n) {
  type_t sigma;

  printf("--- Test substitution ---\n");
  show_type_subst(stdout, table, v, u, n);
  printf("input type: ");
  print_type(stdout, table, tau);
  fputc('\n', stdout);
  sigma = type_substitution(table, tau, n, v, u);
  printf("result: ");
  print_type(stdout, table, sigma);
  fputc('\n', stdout);
}


/*
 * Global variables:
 * var[NVARS] = all variables
 * tests[NTESTS]
 */
static type_table_t types;

#define NVARS 12
#define NTESTS 20

static type_t var[NVARS];
static type_t tests[NTESTS];


/*
 * Initialize the variables
 */
static void init_variables(void) {
  char name[2];
  uint32_t i;

  name[0] = 'A';
  name[1] = '\0';

  for (i=0; i<NVARS; i++) {
    var[i] = type_variable(&types, i);
    set_type_name(&types, var[i], clone_string(name));
    name[0] ++;
  }
}


/*
 * Initialize the test types
 */
static void init_tests(void) {
  type_t aux[12];

  tests[0] = bool_type(&types);
  tests[1] = int_type(&types);
  tests[2] = real_type(&types);
  tests[3] = bv_type(&types, 10);
  tests[4] = bv_type(&types, 32);
  tests[5] = new_scalar_type(&types, 6);
  set_type_name(&types, tests[5], clone_string("s"));
  tests[6] = new_scalar_type(&types, 1);
  set_type_name(&types, tests[6], clone_string("u"));
  tests[7] = new_uninterpreted_type(&types);
  set_type_name(&types, tests[7], clone_string("aa"));
  tests[8] = new_uninterpreted_type(&types);
  set_type_name(&types, tests[8], clone_string("bb"));
  tests[9] = var[3];
  tests[10] = var[4];
  tests[11] = var[5];

  aux[0] = tests[0];
  aux[1] = var[0];
  aux[2] = var[3];
  tests[12] = tuple_type(&types, 3, aux);

  aux[0] = tests[4];
  aux[1] = tests[4];
  aux[2] = var[10];
  aux[3] = var[10];
  aux[4] = tests[12];
  aux[5] = tests[1];
  aux[6] = tests[2];
  tests[13] = tuple_type(&types, 6, aux);

  tests[14] = function_type(&types, var[6], 4, aux);

  aux[0] = tests[3];
  aux[1] = tests[4];
  aux[2] = tests[5];
  aux[3] = tests[6];
  aux[4] = tests[7];
  aux[5] = tests[8];
  aux[6] = tests[9];
  aux[7] = tests[10];
  aux[8] = tests[11];
  aux[9] = tests[12];
  aux[10] = tests[13];
  tests[15] = tuple_type(&types, 10, aux);

  tests[16] = function_type(&types, tests[10], 10, aux);

  aux[0] = tests[4];
  aux[1] = tests[0];
  aux[2] = tests[2];
  tests[17] = tuple_type(&types, 3, aux);

  aux[0] = tests[17];
  aux[1] = tests[17];
  tests[18] = tuple_type(&types, 2, aux);

  aux[0] = tests[18];
  aux[1] = tests[18];
  aux[2] = tests[18];
  tests[19] = function_type(&types, tests[18], 3, aux);
}


/*
 * Check whether x occurs in v[0 ... n-1]
 */
static bool repeated_var(type_t x, uint32_t n, type_t *v) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (v[i] == x) return true;
  }

  return false;
}

/*
 * Store n random variables in array v
 */
static void random_vars(uint32_t n, type_t *v) {
  uint32_t i, j;
  type_t x;

  for (i=0; i<n; i++) {
    do {
      j = random() % NVARS;
      x = var[j];
    } while (repeated_var(x, i, v));
    v[i] = x;
  }
}


/*
 * Store n random types in array u
 */
static void random_types(uint32_t n, type_t *u) {
  uint32_t i, j;

  for (i=0; i<n; i++) {
    j = random() % NTESTS;
    u[i] = tests[j];
  }
}


/*
 * Apply n random substitutions to type tau
 */
static void test_random_subst(type_t tau, uint32_t n) {
  type_t v[6];
  type_t u[6];

  while (n > 0) {
    n --;
    random_vars(4, v);
    random_types(4, u);
    test_type_subst(&types, tau, v, u, 4);
  }
  printf("\n\n");
}


int main(void) {
  uint32_t i;

  init_type_table(&types, 0);
  init_variables();
  init_tests();

  for (i=0; i<NTESTS; i++) {
    test_random_subst(tests[i], 5);
  }

  delete_type_table(&types);

  return 0;
}
