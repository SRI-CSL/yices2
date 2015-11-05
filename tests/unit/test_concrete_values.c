/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of object construction
 */

#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>

#include "io/concrete_value_printer.h"
#include "model/concrete_values.h"
#include "terms/rationals.h"
#include "terms/types.h"
#include "utils/assert_utils.h"

static type_table_t types;
static value_table_t vtbl;


/*
 * Base types
 */
static type_t bools;
static type_t reals;
static type_t bv5;
static type_t bv100;
static type_t enum3;
static type_t real_pairs;
static type_t bool_funs; // [bool bool -> bool]


/*
 * Initialize both tables and create the base types
 */
static void init_tables(void) {
  type_t aux[2];

  init_type_table(&types, 10);
  init_value_table(&vtbl, 0, &types);

  bools = bool_type(&types);
  reals = real_type(&types);
  bv5 = bv_type(&types, 5);
  bv100 = bv_type(&types, 100);
  enum3 = new_scalar_type(&types, 3);

  aux[0] = reals;
  aux[1] = reals;
  real_pairs = tuple_type(&types, 2, aux);

  aux[0] = bools;
  aux[1] = bools;
  bool_funs = function_type(&types, bools, 2, aux);

}


/*
 * Delete both tables
 */
static void delete_tables(void) {
  delete_value_table(&vtbl);
  delete_type_table(&types);
}


/*
 * Show the full value table
 */
static void dump_vtbl(void) {
  uint32_t i, n;

  printf("\n=== Value table ===\n");
  n = vtbl.nobjects;
  for (i=0; i<n; i++) {
    printf("obj[%"PRIu32"] = ", i);
    vtbl_print_object(stdout, &vtbl, i);
    printf("\n");
  }
  printf("==============\n");
}


/*
 * Store constant u as an array of bits
 *  b[i] = 0 is bit i of u is 0
 *  b[i] = 1 otherwise
 */
static void bits_of_uint32(uint32_t u, uint32_t n, int32_t *b) {
  uint32_t i, mask;

  mask = 1;
  for (i=0; i<n; i++) {
    b[i] = ((u & mask) != 0);
    mask <<= 1;
  }
}


/*
 * Test creation and hash-consing of atomic constants
 *
 * NOTE: used assert_true here instead of assert to fix compiler warnings:
 * variable 'v1' set but not used.
 */
static void test_constants(void) {
  value_t v, v1;
  rational_t q;
  uint32_t i;
  int32_t b[5];

  printf("\n=== Constants ===\n");
  v = vtbl_mk_unknown(&vtbl);
  printf("unknown: v = %"PRId32"\n", v);
  v1 = vtbl_mk_unknown(&vtbl);
  assert_true(v == v1);

  v = vtbl_mk_true(&vtbl);
  printf("true: v = %"PRId32"\n", v);
  v1 = vtbl_mk_true(&vtbl);
  assert_true(v == v1);


  v = vtbl_mk_false(&vtbl);
  printf("false: v = %"PRId32"\n", v);
  v1 = vtbl_mk_false(&vtbl);
  assert_true(v == v1);

  q_init(&q);
  q_set_int32(&q, -1, 2);
  v = vtbl_mk_rational(&vtbl, &q);
  printf("-1/2: v  = %"PRId32"\n", v);
  v1 = vtbl_mk_rational(&vtbl, &q);
  assert_true(v == v1);

  q_set32(&q, 24);
  v = vtbl_mk_rational(&vtbl, &q);
  printf("24: v = %"PRId32"\n", v);
  v1 = vtbl_mk_rational(&vtbl, &q);
  assert_true(v == v1);
  v1 = vtbl_mk_int32(&vtbl, 24);
  assert_true(v == v1);

  // all bitvector constants of size 5
  for (i=0; i<32; i++) {
    v = vtbl_mk_bv_from_bv(&vtbl, 5, &i);
    printf("(mk-bv %"PRIu32" 5): v = %"PRId32"\n", i, v);
    v1 = vtbl_mk_bv_from_bv(&vtbl, 5, &i);
    assert_true(v == v1);
    bits_of_uint32(i, 5, b);
    v1 = vtbl_mk_bv(&vtbl, 5, b);
    assert_true(v == v1);
    v1 = vtbl_mk_bv_from_bv64(&vtbl, 5, (uint64_t) i);
    assert_true(v == v1);
  }

  // bitvector contants: 0 to 31, size 35
  for (i=0; i<32; i++) {
    v = vtbl_mk_bv_from_bv64(&vtbl, 35, (uint64_t) i);
    printf("(mk-bv %"PRIu32" 35): v = %"PRId32"\n", i, v);
    v1 = vtbl_mk_bv_from_bv64(&vtbl, 35, (uint64_t) i);
    assert_true(v == v1);
  }

  // bitvector contants: -0 to -31, size 35
  for (i=0; i<32; i++) {
    v = vtbl_mk_bv_from_bv64(&vtbl, 35, - ((uint64_t) i));
    printf("(mk-bv %"PRId32" 35): v = %"PRId32"\n", -((int32_t) i), v);
    v1 = vtbl_mk_bv_from_bv64(&vtbl, 35, - ((uint64_t) i));
    assert_true(v == v1);
  }

  // bitvector constructors for zero and one: size 64
  v = vtbl_mk_bv_zero(&vtbl, 64);
  printf("(mk-bv-zero 64): v = %"PRId32"\n", v);
  v1 = vtbl_mk_bv_from_bv64(&vtbl, 64, 0);
  assert_true(v == v1);

  v = vtbl_mk_bv_one(&vtbl, 64);
  printf("(mk-bv-zero 64): v = %"PRId32"\n", v);
  v1 = vtbl_mk_bv_from_bv64(&vtbl, 64, 1);
  assert_true(v == v1);

  dump_vtbl();
}


int main(void) {
  init_tables();
  test_constants();
  delete_tables();
  return 0;
}
