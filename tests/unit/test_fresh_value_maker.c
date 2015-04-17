/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test construction of fresh objects
 */

#include <inttypes.h>
#include <stdio.h>
#include <assert.h>

#include "io/concrete_value_printer.h"
#include "io/type_printer.h"
#include "model/fresh_value_maker.h"

static type_table_t types;
static value_table_t vtbl;
static fresh_val_maker_t maker;


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

// [a, b -> c]
static type_t fun_type2(type_t a, type_t b, type_t c) {
  type_t aux[2];

  aux[0] = a;
  aux[1] = b;
  return function_type(&types, c, 2, aux);
}


/*
 * Base types
 */
#define NUM_BASE_TYPES 20

static type_t base[NUM_BASE_TYPES];

static void init_base_types(void) {
  base[0] = bool_type(&types);               // bool
  base[1] = bv_type(&types, 5);              // bv5
  base[2] = new_scalar_type(&types, 3);      // scalar3
  base[3] = new_scalar_type(&types, 1);      // scalar1
  base[4] = pair_type(base[0], base[2]);     // bool x scalar3
  base[5] = pair_type(base[3], base[0]);     // scalar1 x bool
  base[6] = fun_type1(base[0], base[2]);     // [bool -> scalar3]
  base[7] = fun_type1(base[0], base[3]);     // [bool -> scalar1]
  base[8] = fun_type1(base[2], base[0]);     // [scalar3 -> bool]
  base[9] = fun_type1(base[3], base[0]);     // [scalar1 -> bool]
  base[10] = fun_type1(base[0], base[0]);    // [bool -> bool]
  base[11] = fun_type1(base[10], base[0]);   // [[bool -> bool] -> bool]

  // some infinite types
  base[12] = new_uninterpreted_type(&types);
  base[13] = real_type(&types);
  base[14] = int_type(&types);
  base[15] = fun_type1(base[14], base[0]);          // [int -> bool]
  base[16] = fun_type2(base[0], base[0], base[14]); // [bool, bool -> int]

  // larger finite types
  base[17] = pair_type(base[1], base[1]);   // bv5 x bv5
  base[18] = bv_type(&types, 40);           // bv40

  // infinite domain, unit range
  base[19] = fun_type1(base[13], base[3]);  // [real -> scalar1]
}


/*
 * Test
 * - create values of type tau
 * - n: max number of fresh values to try (assumed positive)
 */
static void test_type(type_t tau, uint32_t n) {
  value_t v;
  uint32_t i;

  printf("==== Test fresh values of type ");
  print_type(stdout, &types, tau);
  printf(" ====\n");
  printf("cardinality: %"PRIu32"\n\n", type_card(&types, tau));

  i = 0;
  do {
    v = make_fresh_value(&maker, tau);
    if (v == null_value) break;
    i ++;
    printf("val[%"PRIu32"] = ", i);
    vtbl_print_object(stdout, &vtbl, v);
    printf("\n");
    if (vtbl_queue_is_nonempty(&vtbl)) {
      vtbl_print_queued_functions(stdout, &vtbl, true);
      printf("\n");
    }
  } while (i <n);

  printf("\n---> got %"PRIu32" fresh values\n\n", i);
}


/*
 * TEST1 : all base types
 */
static void test_base_types(void) {
  uint32_t i;

  printf("*****************\n"
	 "*   BASE TYPES  *\n"
	 "*****************\n"
	 "\n");

  for (i=0; i<NUM_BASE_TYPES; i++) {
    test_type(base[i], 100);
  }
}


int main(void) {
  init_type_table(&types, 10);
  init_value_table(&vtbl, 0, &types);
  init_fresh_val_maker(&maker, &vtbl);

  init_base_types();

  test_base_types();

  delete_fresh_val_maker(&maker);
  delete_value_table(&vtbl);
  delete_type_table(&types);

  return 0;
}
