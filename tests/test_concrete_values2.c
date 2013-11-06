/*
 * Test finite type enumerators in concrete_values.c
 */

#include <inttypes.h>
#include <stdio.h>
#include <assert.h>

#include "types.h"
#include "type_printer.h"
#include "concrete_values.h"
#include "concrete_value_printer.h"

static type_table_t types;
static value_table_t vtbl;


/*
 * Base types: all finite and small
 */
#define NUM_BASE_TYPES 10

static type_t base[NUM_BASE_TYPES];

static type_t pair_type(type_t a, type_t b) {
  type_t aux[2];

  aux[0] = a;
  aux[1] = b;
  return tuple_type(&types, 2, aux);
}

static type_t triple_type(type_t a, type_t b, type_t c) {
  type_t aux[3];

  aux[0] = a;
  aux[1] = b;
  aux[2] = c;
  return tuple_type(&types, 3, aux);
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

static void init_base_types(void) {
  base[0] = bool_type(&types);             // bool
  base[1] = bv_type(&types, 5);            // bv5
  base[2] = new_scalar_type(&types, 3);    // scalar3 
  base[3] = new_scalar_type(&types, 1);    // scalar1
  base[4] = pair_type(base[0], base[2]);   // bool x scalar3
  base[5] = pair_type(base[3], base[0]);  // scalar1 x bool
  base[6] = fun_type1(base[0], base[2]);   // [bool -> scalar3]
  base[7] = fun_type1(base[0], base[3]);   // [bool -> scalar1]
  base[8] = fun_type1(base[2], base[0]);   // [scalar3 -> bool]
  base[9] = fun_type1(base[3], base[0]);   // [scalar1 -> bool]
}

static void test_enum_type(type_t tau) {
  uint32_t i, n;
  value_t x;

  assert(is_finite_type(&types, tau) && type_card_is_exact(&types, tau));

  n = type_card(&types, tau);
  printf("==== Enumerating elements of type ");
  print_type(stdout, &types, tau);
  printf(" ====\n");
  printf("cardinality: %"PRIu32"\n", n);
  for (i=0; i<n; i++) {
    x = vtbl_gen_object(&vtbl, tau, i);
    printf("elem[%"PRIu32"] = ", i);
    vtbl_print_object(stdout, &vtbl, x);
    printf("\n");
    if (! int_queue_is_empty(&vtbl.queue.queue)) {
      vtbl_print_queued_functions(stdout, &vtbl, true);
      printf("\n");
    }
  }
  printf("\n");
}

int main(void) {
  uint32_t i;

  init_type_table(&types, 10);
  init_value_table(&vtbl, 0, &types);

  init_base_types();

  for (i=0; i<NUM_BASE_TYPES; i++) {
    test_enum_type(base[i]);
  }
  
  delete_value_table(&vtbl);
  delete_type_table(&types);

  return 0;
}
