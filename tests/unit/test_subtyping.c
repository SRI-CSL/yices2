/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of sup/inf/subtype/compatibility between types
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "io/type_printer.h"
#include "terms/types.h"
#include "utils/refcount_strings.h"

#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline int random(void) {
  return rand();
}

#endif





/*
 * Global type table
 */
static type_table_t types;


/*
 * Constructors for tuples and function types
 */
static type_t unary_function_type(type_t dom1, type_t range) {
  return function_type(&types, range, 1, &dom1);
}

static type_t binary_function_type(type_t dom1, type_t dom2, type_t range) {
  type_t a[2];

  a[0] = dom1;
  a[1] = dom2;
  return function_type(&types, range, 2, a);
}

static type_t tuple_type_pair(type_t t1, type_t t2) {
  type_t a[2];

  a[0] = t1;
  a[1] = t2;
  return tuple_type(&types, 2, a);
}

static type_t tuple_type_triple(type_t t1, type_t t2, type_t t3) {
  type_t a[3];

  a[0] = t1;
  a[1] = t2;
  a[2] = t3;
  return tuple_type(&types, 3, a);
}



/*
 * Array of types
 */
#define NUM_TYPES 600

static type_t all_types[NUM_TYPES];
static uint32_t num_types;


/*
 * Print the full table
 * s = header message
 */
static void show_types(const char *s) {
  printf("*** %s ***\n", s);
  print_type_table(stdout, &types);
  printf("\n");
}

/*
 * Initialize the type table and generate atomic types
 * + some tuple types that mix int and  real
 */
static void init_types(void) {
  init_type_table(&types, 0);

  all_types[0] = bool_type(&types);
  all_types[1] = int_type(&types);
  all_types[2] = real_type(&types);
  all_types[3] = new_uninterpreted_type(&types);
  set_type_name(&types, all_types[3], clone_string("T1"));
  all_types[4] = new_uninterpreted_type(&types);
  set_type_name(&types, all_types[4], clone_string("T2"));
  all_types[5] = new_scalar_type(&types, 1);
  set_type_name(&types, all_types[5], clone_string("U"));
  all_types[6] = new_scalar_type(&types, 5);
  set_type_name(&types, all_types[6], clone_string("E1"));
  all_types[7] = new_scalar_type(&types, 20);
  set_type_name(&types, all_types[7], clone_string("E2"));
  all_types[8] = bv_type(&types, 5);
  set_type_name(&types, all_types[8], clone_string("bv5"));
  all_types[9] = bv_type(&types, 20);
  set_type_name(&types, all_types[9], clone_string("bv20"));
  all_types[10] = bv_type(&types, 300);
  set_type_name(&types, all_types[10], clone_string("bv300"));

  all_types[11] = tuple_type_pair(int_type(&types), real_type(&types));
  all_types[12] = tuple_type_pair(real_type(&types), int_type(&types));
  all_types[13] = tuple_type_triple(int_type(&types), int_type(&types), real_type(&types));
  all_types[14] = tuple_type_triple(real_type(&types), int_type(&types), int_type(&types));
  all_types[15] = tuple_type_triple(int_type(&types), int_type(&types), int_type(&types));
  all_types[16] = tuple_type_triple(real_type(&types), real_type(&types), real_type(&types));

  all_types[17] = unary_function_type(all_types[8], all_types[14]);
  all_types[18] = unary_function_type(all_types[8], all_types[15]);
  all_types[19] = unary_function_type(all_types[8], all_types[16]);

  all_types[20] = binary_function_type(all_types[4], all_types[4], all_types[11]);
  all_types[21] = binary_function_type(all_types[4], all_types[4], all_types[12]);

  all_types[22] = tuple_type_pair(all_types[15], all_types[20]);
  all_types[23] = tuple_type_pair(all_types[14], all_types[21]);

  all_types[24] = tuple_type_triple(all_types[22], all_types[22], all_types[22]);
  all_types[25] = tuple_type_triple(all_types[23], all_types[23], all_types[23]);

  num_types = 26;
}


/*
 * Cleanup: delete the whole type table
 */
static void cleanup(void) {
  delete_type_table(&types);
}


/*
 * Garbage collection: keep type [0 ... n-1]
 */
static void garbage_collect(uint32_t n) {
  uint32_t i;

  // mark all types in [0.. n-1];
  assert(n <= num_types);
  for (i=0; i<n; i++) {
    type_table_set_gc_mark(&types, all_types[i]);
  }
  type_table_gc(&types, true);

  // reset num_types
  num_types = n;
}


/*
 * Randomly construct n tuples or function types:
 */
static type_t random_fun1(void) {
  uint32_t i, j;

  assert(num_types > 0);
  i = random() % num_types;
  j = random() % num_types;
  return unary_function_type(all_types[i], all_types[j]);
}

static type_t random_fun2(void) {
  uint32_t i, j, k;

  assert(num_types > 0);
  i = random() % num_types;
  j = random() % num_types;
  k = random() % num_types;
  return binary_function_type(all_types[i], all_types[j], all_types[k]);
}

static type_t random_tup2(void) {
  uint32_t i, j;

  assert(num_types > 0);
  i = random() % num_types;
  j = random() % num_types;
  return tuple_type_pair(all_types[i], all_types[j]);
}

static type_t random_tup3(void) {
  uint32_t i, j, k;

  assert(num_types > 0);
  i = random() % num_types;
  j = random() % num_types;
  k = random() % num_types;
  return tuple_type_triple(all_types[i], all_types[j], all_types[k]);
}

static void random_types(uint32_t n) {
  uint32_t i;
  type_t tau;
  int x;

  assert(0 < num_types && num_types + n <=  NUM_TYPES);

  for (i=0; i<n; i++) {
    x = (random() >> 8) & 0x3;
    switch (x) {
    case 0:
      tau = random_fun1();
      break;
    case 1:
      tau = random_fun2();
      break;
    case 2:
      tau = random_tup2();
      break;
    default:
      assert(x == 3);
      tau = random_tup3();
      break;
    }
    all_types[num_types] = tau;
    num_types ++;
  }
}


/*
 * Test sup and inf for all pairs in the array
 */
static void test_sup_inf(void) {
  uint32_t i, j;
  type_t a, b, sup, inf;

  for (i=0; i<num_types; i++) {
    for (j=0; j<num_types; j++) {
      a = all_types[i];
      b = all_types[j];
      printf("----\n");
      printf("type[%"PRIu32"]: ", i);
      print_type(stdout, &types, a);
      printf("\n");
      printf("type[%"PRIu32"]: ", j);
      print_type(stdout, &types, b);
      printf("\n");
      if (compatible_types(&types, a, b)) {
	printf("  compatible\n");
      }
      if (is_subtype(&types, a, b)) {
	printf("  type[%"PRIu32"] is a subtype of type[%"PRIu32"]\n", i, j);
      }
      if (is_subtype(&types, b, a)) {
	printf("  type[%"PRIu32"] is a subtype of type[%"PRIu32"]\n", j, i);
      }

      sup = super_type(&types, all_types[i], all_types[j]);
      inf = inf_type(&types, all_types[i], all_types[j]);
      if (sup == NULL_TYPE) {
	printf("  super type: none\n");
      } else {
	printf("  super type: ");
	print_type(stdout, &types, sup);
	printf("\n");
      }
      if (inf == NULL_TYPE) {
	printf("  inf type: none\n");
      } else {
	printf("  inf type: ");
	print_type(stdout, &types, inf);
	printf("\n");
      }

    }
  }
}


/*
 * Pretty printing test
 */
static void pp_types(void) {
  yices_pp_t printer;
  pp_area_t area;
  uint32_t i;
  type_t tau;

  init_yices_pp_tables();

  area.width = 80;
  area.height = UINT32_MAX;
  area.offset = 11;
  area.truncate = false;
  area.stretch = false;

  init_yices_pp(&printer, stdout, &area, PP_VMODE, 0);

  for (i=0; i<num_types; i++) {
    tau = all_types[i];
    printf("type[%"PRIu32"]: ", i);
    if (i < 10) printf(" ");
    if (i < 100) printf(" ");
    pp_type(&printer, &types, tau);
    flush_yices_pp(&printer);
  }

  delete_yices_pp(&printer, false);
}


int main(void) {
  init_types();
  show_types("Initial types");
  random_types(50);
  show_types("Added 50 random types");
  test_sup_inf();
  show_types("After test");

  printf("\nPretty printer test\n");
  pp_types();
  printf("\n");

  garbage_collect(40);
  show_types("After GC: keeping types 0 ... 39");
  test_sup_inf();
  show_types("After test");

  random_types(100);
  show_types("Added 100 random types");
  test_sup_inf();
  show_types("After test");

  garbage_collect(0);
  show_types("After GC: keeping named types");
  cleanup();

  return 0;
}
