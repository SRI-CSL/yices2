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
 * Test normalization of functions with finite domains
 */

#include <inttypes.h>
#include <stdio.h>
#include <assert.h>

#include "io/concrete_value_printer.h"
#include "io/type_printer.h"
#include "model/concrete_values.h"
#include "terms/types.h"

static type_table_t types;
static value_table_t vtbl;


/*
 * Short cuts: type constructors
 */
static type_t pair_type(type_t a, type_t b) {
  type_t aux[2];

  aux[0] = a;
  aux[1] = b;
  return tuple_type(&types, 2, aux);
}

// [a -> b]
static type_t fun_type1(type_t a, type_t b) {
  return function_type(&types, b, 1, &a);
}

/*
 * Base types: all finite and small
 */
#define NUM_BASE_TYPES 10

static type_t base[NUM_BASE_TYPES];

static void init_base_types(void) {
  base[0] = bool_type(&types);             // bool
  base[1] = bv_type(&types, 5);            // bv5
  base[2] = new_scalar_type(&types, 3);    // scalar3
  base[3] = new_scalar_type(&types, 1);    // scalar1
  base[4] = pair_type(base[0], base[2]);   // bool x scalar3
  base[5] = pair_type(base[3], base[0]);   // scalar1 x bool
  base[6] = fun_type1(base[0], base[2]);   // [bool -> scalar3]
  base[7] = fun_type1(base[0], base[3]);   // [bool -> scalar1]
  base[8] = fun_type1(base[2], base[0]);   // [scalar3 -> bool]
  base[9] = fun_type1(base[3], base[0]);   // [scalar1 -> bool]
}


/*
 * Integer objects (range of the functions)
 */
#define NVALS 4

static value_t val[NVALS];

static void init_val(void) {
  int32_t i;

  for (i=0; i<NVALS; i++) {
    val[i] = vtbl_mk_int32(&vtbl, i);
  }
}


/*
 * Buffers for building functions
 */
#define BUFFER_SIZE 1024

static value_t buffer1[BUFFER_SIZE];
static value_t buffer2[BUFFER_SIZE];


/*
 * Mapping element: for function of type [tau[0] x ... x tau[n-1] --> int]
 * - i = index of an element in the domain
 * - v = what's mapped to that element
 */
static value_t make_mapping(type_t *tau, uint32_t n, uint32_t i, value_t v) {
  value_t aux[4];

  assert(n <= 4 && good_object(&vtbl, v));

  vtbl_gen_object_tuple(&vtbl, n, tau, i, aux);
  return vtbl_mk_map(&vtbl, n, aux, v);
}

/*
 * Build the function defined by tau, n, range, rsize, default
 * - n = arity
 * - tau[0 ... n-1] = domain type
 * - rsize = size of range
 * - def = default value to use
 * - all elements in range[0 ... rsize - 1] must be integers
 *
 * The function maps element of index i in domain to range[i].
 */
static value_t make_function(type_t *tau, uint32_t n,
			     value_t *range, uint32_t rsize, value_t def) {
  value_t *map;
  value_t v;
  uint32_t i, j;
  type_t ftype;

  assert(n <= 4 && rsize <= BUFFER_SIZE);
  map = buffer2;

  j = 0;
  for (i=0; i<rsize; i++) {
    if (range[i] != def) {
      map[j] = make_mapping(tau, n, i, range[i]);
      j ++;
    }
  }

  ftype = function_type(&types, int_type(&types), n, tau);
  v = vtbl_mk_function(&vtbl, ftype, j, map, def);

  return v;
}


/*
 * Test different constructions for the same function
 * - tau[0...n-1] = domain type
 * - n = arity
 * - range = array of size equal to card(domain of tau)
 * - the function maps x_i to range[i]
 *   where x_i is the i-th tuple in domain of tau
 */
static void test_function(type_t *tau, uint32_t n, value_t *range) {
  value_t f[NVALS];
  uint32_t dsize, i;
  type_t ftype;

  ftype = function_type(&types, int_type(&types), n, tau);
  dsize = card_of_domain_type(&types, ftype);
  if (dsize > BUFFER_SIZE) return;

  printf("=== testing function of type ");
  print_type(stdout, &types, ftype);
  printf(" ===\n");

  for (i=0; i<NVALS; i++) {
    f[i] = make_function(tau, n, range, dsize, val[i]);
    printf("using default: ");
    vtbl_print_object(stdout, &vtbl, val[i]);
    printf("\nresult:\n");
    vtbl_print_object(stdout, &vtbl, f[i]);
    printf("\n");
    vtbl_print_queued_functions(stdout, &vtbl, true);
    printf("\n");
  }

  for (i=1; i<NVALS; i++) {
    if (f[0] != f[i]) {
      fprintf(stderr, "*** BUG: NORMALIZATION FAILED ***\n");
      fflush(stderr);
      exit(1);
    }
  }
}


/*
 * Test1: all functions from a base type to the range defined by buffer1
 */
static void test_base_types(void) {
  uint32_t i;
  type_t tau;

  for (i=0; i<NUM_BASE_TYPES; i++) {
    tau = base[i];
    test_function(&tau, 1, buffer1);
  }
}

/*
 * Test2: take all pairs of base types
 */
static void test_pair_types(void) {
  uint32_t i, j;
  type_t tau[2];

  for (i=0; i<NUM_BASE_TYPES; i++) {
    tau[0] = base[i];
    for (j=0; j<NUM_BASE_TYPES; j++) {
      tau[1] = base[j];
      test_function(tau, 2, buffer1);
    }
  }
}


/*
 * Initialize buffer1: cycle through val[0 ... nvals-1]
 */
static void init_buffer1(void) {
  uint32_t i, j;

  j = 0;
  for (i=0; i<BUFFER_SIZE; i++) {
    buffer1[i] = val[j];
    j ++;
    if (j >= NVALS) j = 0;
  }
}

/*
 * remove val[0] from buffer1, replace it by val[2]
 */
static void change_buffer1(void) {
  uint32_t i;

  for (i=0; i<BUFFER_SIZE; i++) {
    if (buffer1[i] == val[0]) {
      buffer1[i] = val[2];
    }
  }
}

/*
 * Store constant value val[1] in buffer1
 */
static void constant_buffer1(void) {
  uint32_t i;

  for (i=0; i<BUFFER_SIZE; i++) {
    buffer1[i] = val[1];
  }
}

int main(void) {
  init_type_table(&types, 10);
  init_value_table(&vtbl, 0, &types);

  init_base_types();
  init_val();

  printf("**************************\n"
	 "*   TEST1: CYCLIC MAP    *\n"
	 "**************************\n\n");

  init_buffer1();
  test_base_types();
  test_pair_types();

  printf("**************************\n"
	 "*  TEST2: REMOVED ZEROS  *\n"
	 "**************************\n\n");

  change_buffer1();
  test_base_types();
  test_pair_types();

  printf("**************************\n"
	 "*  TEST3: CONSTANT MAP   *\n"
	 "**************************\n\n");

  constant_buffer1();
  test_base_types();
  test_pair_types();

  delete_value_table(&vtbl);
  delete_type_table(&types);

  return 0;
}
