/*
 * TEST BASIC API FUNCTIONS
 */

/*
 * Force assert to work even if compiled with debug disabled
 */
#ifdef NDEBUG
# undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <inttypes.h>

#include "yices.h"
#include "yices_globals.h"
#include "type_printer.h"
#include "term_printer.h"



/*
 * Print the type table
 */
static void show_types(void) {
  printf("\n---- Type table ----\n");
  print_type_table(stdout, __yices_globals.types);
}


/*
 * Print the term table
 */
static void show_terms(void) {
  printf("\n---- Term table -----\n");
  print_term_table(stdout, __yices_globals.terms);
}


/*
 * Check that descriptor of a type tau matches what's expected
 */
static bool check_bool_type(type_t tau) {
  return tau >= 0 && type_kind(__yices_globals.types, tau) == BOOL_TYPE;
}

static bool check_int_type(type_t tau) {
  return tau >= 0 && type_kind(__yices_globals.types, tau) == INT_TYPE;
}

static bool check_real_type(type_t tau) {
  return tau >= 0 && type_kind(__yices_globals.types, tau) == REAL_TYPE;
}

static bool check_uninterpreted_type(type_t tau) {
  return tau >= 0 && type_kind(__yices_globals.types, tau) == UNINTERPRETED_TYPE;
}

static bool check_bv_type(type_t tau, uint32_t n) {
  return tau >= 0 && type_kind(__yices_globals.types, tau) == BITVECTOR_TYPE
    && bv_type_size(__yices_globals.types, tau) == n;
}

static bool check_scalar_type(type_t tau, uint32_t n) {
  return tau >= 0 && type_kind(__yices_globals.types, tau) == SCALAR_TYPE
    && scalar_type_cardinal(__yices_globals.types, tau) == n;
}

static bool check_tuple_type(type_t tau, uint32_t n, type_t comp[]) {
  tuple_type_t *d;
  uint32_t i;

  if (tau < 0 || type_kind(__yices_globals.types, tau) != TUPLE_TYPE) {
    return false;
  }

  d = tuple_type_desc(__yices_globals.types, tau);
  if (d->nelem != n) {
    return false;
  }

  for (i=0; i<n; i++) {
    if (d->elem[i] != comp[i]) return false;
  }

  return true;
}

static bool check_function_type(type_t tau, uint32_t n, type_t dom[], type_t range) {
  function_type_t *d;
  uint32_t i;

  if (tau < 0 || type_kind(__yices_globals.types, tau) != FUNCTION_TYPE) {
    return false;
  }

  d = function_type_desc(__yices_globals.types, tau);
  if (d->ndom != n || d->range != range) {
    return false;
  }

  for (i=0; i<n; i++) {
    if (d->domain[i] != dom[i]) return false;
  }

  return true;
}


/*
 * Check whether the name of type tau matches 'name'
 */
static bool check_type_name(type_t tau, const char *name) {
  char *s;

  s = type_name(__yices_globals.types, tau);
  if (name == NULL) {
    return s == NULL;
  } else {
    return s != NULL && strcmp(s, name) == 0;
  }
}



/*
 * Check whether tau is NULL_TYPE and whether the 
 * error report is what's expected.
 */
static bool check_pos_int_required(type_t tau) {
  error_report_t *rep;

  rep = yices_error_report();
  return tau == NULL_TYPE && yices_error_code() == POS_INT_REQUIRED && rep->badval <= 0;
}

static bool check_max_bvsize_exceeded(type_t tau, int64_t size) {
  error_report_t *rep;

  rep = yices_error_report();
  return tau == NULL_TYPE && yices_error_code() == MAX_BVSIZE_EXCEEDED && 
    rep->badval == size && size > (int64_t) YICES_MAX_BVSIZE;
}

static bool check_too_many_arguments(type_t tau, int64_t n) {
  error_report_t *rep;

  rep = yices_error_report();
  return tau == NULL_TYPE && yices_error_code() == TOO_MANY_ARGUMENTS && 
    rep->badval == n && n > (int64_t) YICES_MAX_ARITY;
}

static bool check_invalid_type(type_t tau, type_t bad, int32_t bad_index) {
  error_report_t *rep;

  rep = yices_error_report();
  return tau == NULL_TYPE && bad_type(__yices_globals.types, rep->type1) && 
    rep->type1 == bad && rep->index == bad_index;
}



/*
 * Global types
 */
static type_t boolean, integer, real;
static type_t bv1, bv2, bv32, bv54, bv65;
static type_t T1, T2;
static type_t S3, S10;
static type_t U1, U2;

// tuple and function types
static type_t pair_T1_T2, mono_U1, triple_U1_U1_U2, pair_bool, pair_pair_bool;
static type_t fun_bool_bool, fun_int_bv54, fun_S3_S10_bool, fun_real_U1, fun_real_U2;  
static type_t pair_unit_fun, fun_T1_T2_fun_real_U1;


static void test_base_types(void) { 
  int32_t code;
  
  boolean = yices_bool_type();
  assert(check_bool_type(boolean));

  integer = yices_int_type();
  assert(check_int_type(integer));

  real = yices_real_type();
  assert(check_real_type(real));

  bv1 = yices_bv_type(1);
  assert(check_bv_type(bv1, 1));

  bv2 = yices_bv_type(2);
  assert(check_bv_type(bv2, 2));

  bv32 = yices_bv_type(32);
  assert(check_bv_type(bv32, 32));

  bv54 = yices_bv_type(54);
  assert(check_bv_type(bv54, 54));

  bv65 = yices_bv_type(65);
  assert(check_bv_type(bv65, 65));

  T1 = yices_new_uninterpreted_type();
  assert(check_uninterpreted_type(T1));

  T2 = yices_new_uninterpreted_type();
  assert(check_uninterpreted_type(T1));
  
  S3 = yices_new_scalar_type(3);
  assert(check_scalar_type(S3, 3));

  S10 = yices_new_scalar_type(10);
  assert(check_scalar_type(S10, 10));
	 
  U1 = yices_new_scalar_type(1);
  assert(check_scalar_type(U1, 1));

  U2 = yices_new_scalar_type(1);
  assert(check_scalar_type(U2, 1));

  // assign and verify type names
  code = yices_set_type_name(T1, "T1");
  assert(code >= 0 && check_type_name(T1, "T1"));

  code = yices_set_type_name(T2, "T2");
  assert(code >= 0 && check_type_name(T2, "T2"));

  code = yices_set_type_name(S3, "S3");
  assert(code >= 0 && check_type_name(S3, "S3"));

  code = yices_set_type_name(S10, "S10");
  assert(code >= 0 && check_type_name(S10, "S10"));

  code = yices_set_type_name(U1, "U1");
  assert(code >= 0 && check_type_name(U1, "U1"));

  code = yices_set_type_name(U2, "U2");
  assert(code >= 0 && check_type_name(U2, "U2"));

  check_type_name(bv1, NULL);
  check_type_name(bv2, NULL);
  check_type_name(bv32, NULL);
  check_type_name(bv54, NULL);
  check_type_name(bv65, NULL);

  printf("PASS: %s\n", __func__);
  fflush(stdout);
}



/*
 * Test tuple and function type construction
 */
static void test_composite_types(void) {
  type_t aux[10];

  aux[0] = T1;
  aux[1] = T2;
  pair_T1_T2 = yices_tuple_type(2, aux);
  assert(check_tuple_type(pair_T1_T2, 2, aux));

  aux[0] = U1;
  mono_U1 = yices_tuple_type(1, aux);
  assert(check_tuple_type(mono_U1, 1, aux));

  aux[0] = U1;
  aux[1] = U1;
  aux[2] = U2;
  triple_U1_U1_U2 = yices_tuple_type(3, aux);
  assert(check_tuple_type(triple_U1_U1_U2, 3, aux));

  aux[0] = boolean;
  aux[1] = boolean;
  pair_bool = yices_tuple_type(2, aux);
  assert(check_tuple_type(pair_bool, 2, aux));

  aux[0] = pair_bool;
  aux[1] = pair_bool;
  pair_pair_bool = yices_tuple_type(2, aux);
  assert(check_tuple_type(pair_pair_bool, 2, aux));

  aux[0] = boolean;
  fun_bool_bool = yices_function_type(1, aux, boolean);
  assert(check_function_type(fun_bool_bool, 1, aux, boolean));

  aux[0] = integer;
  fun_int_bv54 = yices_function_type(1, aux, bv54);
  assert(check_function_type(fun_int_bv54, 1, aux, bv54));

  aux[0] = S3;
  aux[1] = S10;
  fun_S3_S10_bool = yices_function_type(2, aux, boolean);
  assert(check_function_type(fun_S3_S10_bool, 2, aux, boolean));

  aux[0] = real;
  fun_real_U1 = yices_function_type(1, aux, U1);
  assert(check_function_type(fun_real_U1, 1, aux, U1));

  aux[0] = real;
  fun_real_U2 = yices_function_type(1, aux, U2);
  assert(check_function_type(fun_real_U2, 1, aux, U2));

  aux[0] = fun_real_U1;
  aux[1] = fun_real_U2;
  pair_unit_fun = yices_tuple_type(2, aux);
  assert(check_tuple_type(pair_unit_fun, 2, aux));
  
  aux[0] = T1;
  aux[1] = T2;
  fun_T1_T2_fun_real_U1 = yices_function_type(2, aux, fun_real_U1);
  assert(check_function_type(fun_T1_T2_fun_real_U1, 2, aux, fun_real_U1));

  printf("PASS: %s\n", __func__);
  fflush(stdout);
}



/*
 * Test error reporting for type constructors
 */
static void test_type_errors(void) {
  type_t aux[3];
  type_t test;

  test = yices_bv_type(0);
  assert(check_pos_int_required(test));

  test = yices_bv_type(YICES_MAX_BVSIZE);
  assert(check_bv_type(test, YICES_MAX_BVSIZE)); // not an error

  test = yices_bv_type(UINT32_MAX);
  assert(check_max_bvsize_exceeded(test, UINT32_MAX));

  test = yices_new_scalar_type(0);
  assert(check_pos_int_required(test));

  test = yices_tuple_type(0, NULL);
  assert(check_pos_int_required(test));

  test = yices_tuple_type(UINT32_MAX, NULL);
  assert(check_too_many_arguments(test, UINT32_MAX));

  aux[0] = real;
  aux[1] = bv2;
  aux[2] = -3;
  test = yices_tuple_type(3, aux);
  assert(check_invalid_type(test, aux[2], 2));

  test = yices_function_type(0, NULL, real);
  assert(check_pos_int_required(test));

  test = yices_function_type(UINT32_MAX, NULL, real);
  assert(check_too_many_arguments(test, UINT32_MAX));

  test = yices_function_type(3, aux, real);
  assert(check_invalid_type(test, aux[2], 2));

  aux[2] = T2;
  test = yices_function_type(3, aux, -4);
  assert(check_invalid_type(test, -4, -1));

  printf("PASS: %s\n", __func__);
  fflush(stdout);
}









int main(void) {
  yices_init();

  test_base_types();
  test_composite_types();
  test_type_errors();
  show_types();
  show_terms();

  yices_cleanup();

  return 0;
}
