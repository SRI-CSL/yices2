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

#include <gmp.h>

#include "api/yices_globals.h"
#include "io/type_printer.h"
#include "io/term_printer.h"
#include "terms/rationals.h"
#include "terms/bv64_constants.h"
#include "terms/bv_constants.h"

#include "yices.h"

#include "mt/threads.h"
#include "mt/threadsafe.h"


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
  assert(check_bool_type_mt(boolean));

  integer = yices_int_type();
  assert(check_int_type_mt(integer));

  real = yices_real_type();
  assert(check_real_type_mt(real));

  bv1 = yices_bv_type(1);
  assert(check_bv_type_mt(bv1, 1));

  bv2 = yices_bv_type(2);
  assert(check_bv_type_mt(bv2, 2));

  bv32 = yices_bv_type(32);
  assert(check_bv_type_mt(bv32, 32));

  bv54 = yices_bv_type(54);
  assert(check_bv_type_mt(bv54, 54));

  bv65 = yices_bv_type(65);
  assert(check_bv_type_mt(bv65, 65));

  T1 = yices_new_uninterpreted_type();
  assert(check_uninterpreted_type_mt(T1));

  T2 = yices_new_uninterpreted_type();
  assert(check_uninterpreted_type_mt(T1));

  S3 = yices_new_scalar_type(3);
  assert(check_scalar_type_mt(S3, 3));

  S10 = yices_new_scalar_type(10);
  assert(check_scalar_type_mt(S10, 10));

  U1 = yices_new_scalar_type(1);
  assert(check_scalar_type_mt(U1, 1));

  U2 = yices_new_scalar_type(1);
  assert(check_scalar_type_mt(U2, 1));

  // assign and verify type names
  code = yices_set_type_name(T1, "T1");
  assert(code >= 0 && check_type_name_mt(T1, "T1"));

  code = yices_set_type_name(T2, "T2");
  assert(code >= 0 && check_type_name_mt(T2, "T2"));

  code = yices_set_type_name(S3, "S3");
  assert(code >= 0 && check_type_name_mt(S3, "S3"));

  code = yices_set_type_name(S10, "S10");
  assert(code >= 0 && check_type_name_mt(S10, "S10"));

  code = yices_set_type_name(U1, "U1");
  assert(code >= 0 && check_type_name_mt(U1, "U1"));

  code = yices_set_type_name(U2, "U2");
  assert(code >= 0 && check_type_name_mt(U2, "U2"));

  check_type_name_mt(bv1, NULL);
  check_type_name_mt(bv2, NULL);
  check_type_name_mt(bv32, NULL);
  check_type_name_mt(bv54, NULL);
  check_type_name_mt(bv65, NULL);

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
  assert(check_tuple_type_mt(pair_T1_T2, 2, aux));

  aux[0] = U1;
  mono_U1 = yices_tuple_type(1, aux);
  assert(check_tuple_type_mt(mono_U1, 1, aux));

  aux[0] = U1;
  aux[1] = U1;
  aux[2] = U2;
  triple_U1_U1_U2 = yices_tuple_type(3, aux);
  assert(check_tuple_type_mt(triple_U1_U1_U2, 3, aux));

  aux[0] = boolean;
  aux[1] = boolean;
  pair_bool = yices_tuple_type(2, aux);
  assert(check_tuple_type_mt(pair_bool, 2, aux));

  aux[0] = pair_bool;
  aux[1] = pair_bool;
  pair_pair_bool = yices_tuple_type(2, aux);
  assert(check_tuple_type_mt(pair_pair_bool, 2, aux));

  aux[0] = boolean;
  fun_bool_bool = yices_function_type(1, aux, boolean);
  assert(check_function_type_mt(fun_bool_bool, 1, aux, boolean));

  aux[0] = integer;
  fun_int_bv54 = yices_function_type(1, aux, bv54);
  assert(check_function_type_mt(fun_int_bv54, 1, aux, bv54));

  aux[0] = S3;
  aux[1] = S10;
  fun_S3_S10_bool = yices_function_type(2, aux, boolean);
  assert(check_function_type_mt(fun_S3_S10_bool, 2, aux, boolean));

  aux[0] = real;
  fun_real_U1 = yices_function_type(1, aux, U1);
  assert(check_function_type_mt(fun_real_U1, 1, aux, U1));

  aux[0] = real;
  fun_real_U2 = yices_function_type(1, aux, U2);
  assert(check_function_type_mt(fun_real_U2, 1, aux, U2));

  aux[0] = fun_real_U1;
  aux[1] = fun_real_U2;
  pair_unit_fun = yices_tuple_type(2, aux);
  assert(check_tuple_type_mt(pair_unit_fun, 2, aux));

  aux[0] = T1;
  aux[1] = T2;
  fun_T1_T2_fun_real_U1 = yices_function_type(2, aux, fun_real_U1);
  assert(check_function_type_mt(fun_T1_T2_fun_real_U1, 2, aux, fun_real_U1));

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
  assert(check_pos_int_required_mt(test));

  test = yices_bv_type(YICES_MAX_BVSIZE);
  assert(check_bv_type_mt(test, YICES_MAX_BVSIZE)); // not an error

  test = yices_bv_type(UINT32_MAX);
  assert(check_max_bvsize_exceeded_mt(test, UINT32_MAX));

  test = yices_new_scalar_type(0);
  assert(check_pos_int_required_mt(test));

  test = yices_tuple_type(0, NULL);
  assert(check_pos_int_required_mt(test));

  test = yices_tuple_type(UINT32_MAX, NULL);
  assert(check_too_many_arguments_mt(test, UINT32_MAX));

  aux[0] = real;
  aux[1] = bv2;
  aux[2] = -3;
  test = yices_tuple_type(3, aux);
  assert(check_invalid_type_mt(test, aux[2]));

  test = yices_function_type(0, NULL, real);
  assert(check_pos_int_required_mt(test));

  test = yices_function_type(UINT32_MAX, NULL, real);
  assert(check_too_many_arguments_mt(test, UINT32_MAX));

  test = yices_function_type(3, aux, real);
  assert(check_invalid_type_mt(test, aux[2]));

  aux[2] = T2;
  test = yices_function_type(3, aux, -4);
  assert(check_invalid_type_mt(test, -4));

  printf("PASS: %s\n", __func__);
  fflush(stdout);
}






/*
 * Test construction of uninterpreted terms of type tau.
 */
static void test_uninterpreted(type_t tau) {
  term_t x, y, z;

  if (is_unit_type(__yices_globals.types, tau)) {
    /*
     * all term constructors of type tau should
     * return the unique representative of that type.
     * - for a function type, rep = an uninterpreted constant
     * - for a scalar type, rep = constant of index 0
     * - for a tuple type, rep = tuple of reps
     */
    x = yices_new_uninterpreted_term(tau);
    assert(check_unit_rep_mt(x, tau));

    y = yices_new_uninterpreted_term(tau);
    assert(x == y);

  } else {
    x = yices_new_uninterpreted_term(tau);
    assert(check_uninterpreted_term_mt(x, tau));

    y = yices_new_uninterpreted_term(tau);
    assert(check_uninterpreted_term_mt(y, tau));

    z = yices_new_uninterpreted_term(tau);
    assert(check_uninterpreted_term_mt(z, tau));

    assert(x != y && y != z && z != x);
  }

  printf("PASS: %s for type ", __func__);
  print_type(stdout, __yices_globals.types, tau);
  printf("\n");
  fflush(stdout);
}



static void test_uninterpreted_all(void) {
  test_uninterpreted(boolean);
  test_uninterpreted(integer);
  test_uninterpreted(real);
  test_uninterpreted(bv1);
  test_uninterpreted(bv2);
  test_uninterpreted(bv32);
  test_uninterpreted(bv54);
  test_uninterpreted(bv65);
  test_uninterpreted(T1);
  test_uninterpreted(T2);
  test_uninterpreted(S3);
  test_uninterpreted(S10);
  test_uninterpreted(U1);
  test_uninterpreted(U2);
  test_uninterpreted(pair_T1_T2);
  test_uninterpreted(mono_U1);
  test_uninterpreted(triple_U1_U1_U2);
  test_uninterpreted(pair_bool);
  test_uninterpreted(pair_pair_bool);
  test_uninterpreted(fun_bool_bool);
  test_uninterpreted(fun_int_bv54);
  test_uninterpreted(fun_S3_S10_bool);
  test_uninterpreted(fun_real_U1);
  test_uninterpreted(fun_real_U2);
  test_uninterpreted(pair_unit_fun);
  test_uninterpreted(fun_T1_T2_fun_real_U1);
}


/*
 * Test the construction of constants of type tau.
 * tau must be uninterpreted or scalar.
 */
static void test_constants(type_t tau) {
  uint32_t i, n;
  term_t x, y;

  if (is_uninterpreted_type(__yices_globals.types, tau)) {
    x = yices_constant(tau, 0);
    assert(check_constant_term_mt(x, tau, 0));

    y = yices_constant(tau, 0);
    assert(y == x);

    x = yices_constant(tau, 24);
    assert(check_constant_term_mt(x, tau, 24));

    y = yices_constant(tau, 24);
    assert(y == x);

    x = yices_constant(tau, -20);
    assert(x == NULL_TERM && yices_error_code() == INVALID_CONSTANT_INDEX);

  } else {
    assert(is_scalar_type(__yices_globals.types, tau));

    n = scalar_type_cardinal(__yices_globals.types, tau);
    for (i=0; i<n; i++) {
      x = yices_constant(tau, i);
      assert(check_constant_term_mt(x, tau, i));

      y = yices_constant(tau, i);
      assert(y == x);
    }

    x = yices_constant(tau, -20);
    assert(x == NULL_TERM && yices_error_code() == INVALID_CONSTANT_INDEX);

    y = yices_constant(tau, n);
    assert(y == NULL_TERM && yices_error_code() == INVALID_CONSTANT_INDEX);

  }

  printf("PASS: %s for type ", __func__);
  print_type(stdout, __yices_globals.types, tau);
  printf("\n");
  fflush(stdout);
}



static void test_constants_all(void) {
  test_constants(T1);
  test_constants(T2);
  test_constants(S3);
  test_constants(S10);
  test_constants(U1);
  test_constants(U2);
}



static void test_constant_errors(void) {
  term_t x;

  x = yices_new_uninterpreted_term(-23);
  assert(check_invalid_type2_mt(x, -23));

  x = yices_constant(10000, 0);
  assert(check_invalid_type2_mt(x, 10000));

  x = yices_constant(real, 0);
  assert(check_scalar_or_utype_required_mt(x, real));

  printf("PASS: %s\n", __func__);
  fflush(stdout);
}




static void test_arith_constants(void) {
  mpq_t mpq;
  mpz_t mpz;
  rational_t q;
  term_t x, y;

  q_init(&q);   // q is zero

  // Many ways of constructing 0
  x = yices_zero();
  assert(check_arith_constant_mt(x, &q));

  y = yices_int32(0);
  assert(x == y);
  y = yices_int64(0);
  assert(x == y);

  y = yices_rational32(0, 1);
  assert(y == x);
  y = yices_rational64(0, 1);
  assert(y == x);

  y = yices_parse_rational("+000");
  assert(y == x);

  y = yices_parse_rational("-0/2");
  assert(y == x);

  y = yices_parse_float("0.0E-1");
  assert(y == x);
  y = yices_parse_float("-0.00000000000000000000000");
  assert(y == x);

  // Contructing -1/300
  q_set_int32(&q, -1, 300);

  x = yices_rational32(-1, 300);
  assert(check_arith_constant_mt(x, &q));

  y = yices_rational64(-5, 1500);
  assert(y == x);

  mpq_init(mpq);
  mpq_set_si(mpq, -3, 900);
  mpq_canonicalize(mpq);
  y = yices_mpq(mpq);
  assert(y == x);

  y = yices_parse_rational("-4/1200");
  assert(y == x);


  // Large integer
  mpz_init(mpz);
  mpz_set_str(mpz, "123456789123456789223456789", 10);
  q_set_mpz(&q, mpz);

  x = yices_mpz(mpz);
  assert(check_arith_constant_mt(x, &q));

  y = yices_parse_float("123456789123456789223456.789e3");
  assert(y == x);

  mpq_set_z(mpq, mpz);
  y = yices_mpq(mpq);
  assert(y == x);


  // Error codes
  x = yices_rational32(1, 0);
  assert(x == NULL_TERM && yices_error_code() == DIVISION_BY_ZERO);

  x = yices_rational64(-1, 0);
  assert(x == NULL_TERM && yices_error_code() == DIVISION_BY_ZERO);

  x = yices_parse_rational("");
  assert(x == NULL_TERM && yices_error_code() == INVALID_RATIONAL_FORMAT);

  x = yices_parse_rational("not a rational");
  assert(x == NULL_TERM && yices_error_code() == INVALID_RATIONAL_FORMAT);

  x = yices_parse_rational("1/0");
  assert(x == NULL_TERM && yices_error_code() == DIVISION_BY_ZERO);

  x = yices_parse_float("");
  assert(x == NULL_TERM && yices_error_code() == INVALID_FLOAT_FORMAT);

  x = yices_parse_float("not a float");
  assert(x == NULL_TERM && yices_error_code() == INVALID_FLOAT_FORMAT);


  // cleanup
  q_clear(&q);
  mpq_clear(mpq);
  mpz_clear(mpz);

  printf("PASS: %s\n", __func__);
  fflush(stdout);
}


static void test_bv_constants(void) {
  uint32_t aux[10];
  int32_t test[66];
  mpz_t mpz;
  term_t x, y;
  uint32_t i;

  mpz_init(mpz);

  // zero constant 10bits
  x = yices_bvconst_zero(10);
  assert(check_bv64_constant_mt(x, 0, 10));

  y = yices_bvconst_uint32(10, 0);
  assert(y == x);

  y = yices_bvconst_uint64(10, 0);
  assert(y == x);

  y = yices_bvconst_mpz(10, mpz);
  assert(y == x);

  y = yices_parse_bvbin("0000000000");
  assert(y == x);

  // zero constant 65 bits
  aux[0] = 0;
  aux[1] = 0;
  aux[2] = 0;
  aux[3] = 0;
  x = yices_bvconst_zero(65);
  assert(check_bv_constant_mt(x, aux, 65));

  y = yices_bvconst_uint32(65, 0);
  assert(y == x);

  y = yices_bvconst_uint64(65, 0);
  assert(y == x);

  y = yices_bvconst_mpz(65, mpz);
  assert(y == x);

  for (i=0; i<65; i++) {
    test[i] = 0;
  }
  y = yices_bvconst_from_array(65, test);
  assert(y == x);

  // constant 0b1bit
  x = yices_bvconst_one(1);
  assert(check_bv64_constant_mt(x, 1, 1));

  y = yices_bvconst_minus_one(1);
  assert(y == x);
  y = yices_bvconst_uint32(1, 1);
  assert(y == x);
  y = yices_bvconst_uint64(1, 1);
  assert(y == x);
  y = yices_parse_bvbin("1");
  assert(y == x);

  // constant: 0xFFF... (68 bits)
  aux[0] = 0xFFFFFFFF;
  aux[1] = 0xFFFFFFFF;
  aux[2] = 0x0000000F;
  x = yices_parse_bvhex("FFFFFFFFFFFFFFFFF");
  assert(check_bv_constant_mt(x, aux, 68));

  y = yices_parse_bvhex("FFfffffffffffffff");
  assert(check_bv_constant_mt(y, aux, 68) && y == x);

  y = yices_bvconst_minus_one(68);
  assert(y == x);

  mpz_set_ui(mpz, 1);
  mpz_mul_2exp(mpz, mpz, 68);
  mpz_sub_ui(mpz, mpz, 1);
  y = yices_bvconst_mpz(68, mpz);
  assert(y == x);

  // error codes
  x = yices_bvconst_uint32(0, 0);
  assert(x == NULL_TERM && yices_error_code() == POS_INT_REQUIRED);

  x = yices_bvconst_uint64(UINT32_MAX, 1);
  assert(x == NULL_TERM && yices_error_code() == MAX_BVSIZE_EXCEEDED);

  x = yices_parse_bvbin("");
  assert(x == NULL_TERM && yices_error_code() == INVALID_BVBIN_FORMAT);

  x = yices_parse_bvbin("01xxxxx");
  assert(x == NULL_TERM && yices_error_code() == INVALID_BVBIN_FORMAT);

  x = yices_parse_bvhex("");
  assert(x == NULL_TERM && yices_error_code() == INVALID_BVHEX_FORMAT);

  x = yices_parse_bvhex("%%%%%%%%");
  assert(x == NULL_TERM && yices_error_code() == INVALID_BVHEX_FORMAT);

  mpz_clear(mpz);

  printf("PASS: %s\n", __func__);
  fflush(stdout);
}





int _old_main(void) {
  yices_init();

  // type constructors
  test_base_types();
  test_composite_types();
  test_type_errors();

  // term constructors
  test_uninterpreted_all();
  test_constants_all();
  test_constant_errors();

  test_arith_constants();
  test_bv_constants();

  show_types_mt(stdout);
  show_terms_mt(stdout);


  yices_exit();

  printf("All tests succeeded\n");
  
  return 0;
}


static yices_lock_t __all_lock;


yices_thread_result_t YICES_THREAD_ATTR test_thread(void* arg){

  thread_data_t* tdata = (thread_data_t *)arg;
  //FILE* output = tdata->output;
  int32_t id = tdata->id;

  fprintf(stderr, "Starting: %d\n", id);
  
  fprintf(stderr, "Done: %d\n", id);

  return yices_thread_exit();

}
  

int main(int argc, char* argv[]) {
  
  if(argc != 2){
    mt_test_usage(argc, argv);
    return 0;
  } else {
    int32_t nthreads = atoi(argv[1]);
    
    yices_init();
    create_yices_lock(&__all_lock);


    /*
    init_store();
    */
    
    if(nthreads < 0){
      fprintf(stderr, "thread number must be positive!\n");
      exit(EXIT_FAILURE);
    } else if(nthreads == 0){
      thread_data_t tdata = {0, stdout};
      test_thread(&tdata);
    } else {
      launch_threads(nthreads, NULL, 0, "test_api4_mt", test_thread, true);
    }
    
    destroy_yices_lock(&__all_lock);
    
    yices_exit();
    
  } 
  return 0;
}
