/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST CONVERSIONS TO STRING
 */

#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>

#include "yices.h"


/*
 * Test conversion of type tau
 * - error = expected error code (0 means no error)
 */
static void test_type_to_string(type_t tau, int32_t error) {
  char *s;
  error_code_t ecode;

  printf("Testing type_to_string: tau = %"PRId32" (print area = 40 x 10)\n", tau);
  fflush(stdout);

  s = yices_type_to_string(tau, 40, 10, 0);
  if (s != NULL) {
    printf("Result:\n%s", s);
    fflush(stdout);
    if (error != 0) {
      printf("TEST FAILED\n");
      printf("--> Yices function succeeded but NULL output was expected\n");
      fflush(stdout);
      exit(1);
    }
    yices_free_string(s);
  } else {
    printf("Result = NULL\n");
    fflush(stdout);
    printf("error: ");
    yices_print_error(stdout);
    printf("\n");
    ecode = yices_error_code();
    if (ecode != error) {
      printf("TEST FAILED\n");
      printf("--> Yices error code = %"PRId32" bit %"PRId32" was expected\n", ecode, error);
      fflush(stdout);
      exit(1);      
    }
  }

  printf("\n");
  fflush(stdout);
}


/*
 * Test conversion of term t
 * - error = expected error code (0 means no error)
 */
static void test_term_to_string(term_t t, int32_t error) {
  char *s;
  error_code_t ecode;

  printf("Testing term_to_string: t = %"PRId32" (print area = 100 x 60)\n", t);
  fflush(stdout);

  s = yices_term_to_string(t, 100, 60, 0);
  if (s != NULL) {
    printf("Result:\n%s", s);
    fflush(stdout);
    if (error != 0) {
      printf("TEST FAILED\n");
      printf("--> Yices function succeeded but NULL output was expected\n");
      fflush(stdout);
      exit(1);
    }
    yices_free_string(s);
  } else {
    printf("Result = NULL\n");
    fflush(stdout);
    printf("error: ");
    yices_print_error(stdout);
    printf("\n");
    ecode = yices_error_code();
    if (ecode != error) {
      printf("TEST FAILED\n");
      printf("--> Yices error code = %"PRId32" bit %"PRId32" was expected\n", ecode, error);
      fflush(stdout);
      exit(1);      
    }
  }

  printf("\n");
  fflush(stdout);
}



/*
 * Arrays of types and terms for testing
 */
#define NUM_TYPES 6
#define NUM_TERMS 6

static type_t type[NUM_TYPES];
static term_t term[NUM_TERMS];


static void init_types(void) {
  type_t aux[3];
  type_t tau;

  type[0] = yices_int_type();
  type[1] = yices_bv_type(123);
  type[2] = yices_new_uninterpreted_type();
  yices_set_type_name(type[2], "T");

  aux[0] = type[2];
  aux[1] = type[2];
  tau = yices_bool_type();
  type[3] = yices_function_type(2, aux, tau);

  aux[0] = type[1];
  aux[1] = type[3];
  aux[2] = type[1];
  type[4] = yices_tuple_type(3, aux);

  aux[0] = type[4];
  aux[1] = type[4];
  aux[2] = type[4];
  type[5] = yices_tuple_type(3, aux);
}


static void init_terms(void) {
  term_t a, b, c;
  type_t tau;

  tau = yices_bv_type(123);

  term[0] = yices_new_uninterpreted_term(tau);
  yices_set_term_name(term[0], "X");
  term[1] = yices_bvconst_uint32(123, 111111);
  term[2] = yices_new_uninterpreted_term(tau);
  yices_set_term_name(term[2], "Y");

  a = yices_bvand2(term[0], term[1]);
  b = yices_bvadd(a, term[2]);
  c = yices_bvpower(b, 5);
  term[3] = yices_bveq_atom(c, term[1]);

  term[4] = yices_bvxor2(a, c);
  term[5] = yices_bvor2(term[4], term[2]);
}

/*
 * Test of type_to_string
 */
static void test_types(void) {
  uint32_t i;

  for (i=0; i<NUM_TYPES; i++) {
    test_type_to_string(type[i], 0);
  }
  test_type_to_string(-321, INVALID_TYPE);
  test_type_to_string(888888, INVALID_TYPE);
}

/*
 * Test all terms
 */
static void test_terms(void) {
  uint32_t i;

  for (i=0; i<NUM_TERMS; i++) {
    test_term_to_string(term[i], 0);
  }
  test_term_to_string(-321, INVALID_TERM);
  test_term_to_string(888888, INVALID_TERM);
}


int main(void) {
  yices_init();
  init_types();
  init_terms();
  test_types();
  test_terms();
  yices_exit();

  printf("All tests succeeded\n");
  
  return 0;
}
