/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST PRETTY PRINTING FUNCTIONS
 */

#include <assert.h>
#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>
#include <errno.h>

#include "yices.h"


/*
 * Pretty print type tau on f:
 * - k expected return value
 * - error expected error code (if k < 0)
 */
static void test_pp_type(FILE *f, type_t tau, int32_t k, int32_t error) {
  int32_t code;
  error_code_t ecode;
  int saved_errno;

  printf("Testing pp_type: tau = %"PRId32" (print area = 40 x 10)\n", tau);
  fflush(stdout);

  code = yices_pp_type(f, tau, 40, 10, 0);
  if (code >= 0) {
    printf("ok\n");
  } else {
    ecode = yices_error_code();
    if (ecode == OUTPUT_ERROR) {
      saved_errno = errno;
    }
    printf("error\n");
    yices_print_error(stdout);
    if (ecode == OUTPUT_ERROR) {
      errno = saved_errno;
      perror("yices_pp_type");
    }
  }

  if (code != k) {
    printf("TEST FAILED\n");
    printf("--> Yices function returned %"PRId32"; %"PRId32" was expected\n", code, k);
    fflush(stdout);
    exit(1);
  } else if (k < 0) {
    ecode = yices_error_code();
    if (ecode != error) {
      printf("TEST FAILED\n");
      printf("--> Found error code %"PRId32"; %"PRId32" was expected\n", ecode, error);
      fflush(stdout);
      exit(1);
    }
  }

  printf("\n");
  fflush(stdout);
}


/*
 * Pretty print term t on f:
 * - k expected return value
 * - error expected error code (if k < 0)
 */
static void test_pp_term(FILE *f, term_t t, int32_t k, int32_t error) {
  int32_t code;
  error_code_t ecode;
  int saved_errno;

  printf("Testing pp_term: t = %"PRId32" (print area = 100 x 60)\n", t);
  fflush(stdout);

  code = yices_pp_term(f, t, 100, 60, 0);
  if (code >= 0) {
    printf("ok\n");
  } else {
    ecode = yices_error_code();
    if (ecode == OUTPUT_ERROR) {
      saved_errno = errno;
    }
    printf("error\n");
    yices_print_error(stdout);
    if (ecode == OUTPUT_ERROR) {
      errno = saved_errno;
      perror("yices_pp_term");
    }
  }

  if (code != k) {
    printf("TEST FAILED\n");
    printf("--> Yices function returned %"PRId32"; %"PRId32" was expected\n", code, k);
    fflush(stdout);
    exit(1);
  } else if (k < 0) {
    ecode = yices_error_code();
    if (ecode != error) {
      printf("TEST FAILED\n");
      printf("--> Found error code %"PRId32"; %"PRId32" was expected\n", ecode, error);
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

  a = yices_bvand(term[0], term[1]);
  b = yices_bvadd(a, term[2]);
  c = yices_bvpower(b, 5);
  term[3] = yices_bveq_atom(c, term[1]);

  term[4] = yices_bvxor(a, c);
  term[5] = yices_bvor(term[4], term[2]);
}


/*
 * Tests of print type
 */
static void test_pp_types(void) {
  FILE *f;
  uint32_t i;

  printf("File = stdout\n");
  for (i=0; i<NUM_TYPES; i++) {
    test_pp_type(stdout, type[i], 0, 0);
  }
  test_pp_type(stdout, 1389841, -1, INVALID_TYPE);
  printf("\n\n");

  // use /tmp/yices.a, open for writing
  printf("File = /tmp/yices.a\n");
  f = fopen("/tmp/yices.a", "w");
  if (f == NULL) {
    perror("/tmp/yices.a");
  } else {
    for (i=0; i<NUM_TYPES; i++) {
      test_pp_type(f, type[i], 0, 0);
    }
    test_pp_type(f, -123, -1, INVALID_TYPE);
    fclose(f);
    printf("\n\n");
  }

  // create an empty file
  printf("File = /tmp/yices.b (read only)\n");
  f = fopen("/tmp/yices.b", "w");
  if (f == NULL) {
    perror("/tmp/yices.b");
    return;
  } else {
    fclose(f);
  }

  // open /tmp/yices.b read only
  // This should produce error: EBADF (Bad file descriptor)
  f = fopen("/tmp/yices.b", "r");
  if (f == NULL) {
    perror("/tmp/yices.b");
  } else {
    test_pp_type(f, type[0], -1, OUTPUT_ERROR);
    test_pp_type(f, -123, -1, INVALID_TYPE);
    fclose(f);
  }
  printf("\n\n");
}



static void test_pp_terms(void) {
  FILE *f;
  uint32_t i;

  printf("File = stdout\n");
  for (i=0; i<NUM_TERMS; i++) {
    test_pp_term(stdout, term[i], 0, 0);
  }
  test_pp_term(stdout, 1389841, -1, INVALID_TERM);
  printf("\n\n");

  // use /tmp/yices.c, open for writing
  printf("File = /tmp/yices.c\n");
  f = fopen("/tmp/yices.c", "w");
  if (f == NULL) {
    perror("/tmp/yices.c");
  } else {
    for (i=0; i<NUM_TERMS; i++) {
      test_pp_term(f, term[i], 0, 0);
    }
    test_pp_term(f, -123, -1, INVALID_TERM);
    fclose(f);
    printf("\n\n");
  }

  // create another empty file
  printf("File = /tmp/yices.d (read only)\n");
  f = fopen("/tmp/yices.d", "w");
  if (f == NULL) {
    perror("/tmp/yices.d");
    return;
  } else {
    fclose(f);
  }

  // use it read-only
  f = fopen("/tmp/yices.d", "r");
  if (f == NULL) {
    perror("/tmp/yices.d");
  } else {
    test_pp_term(f, term[0], -1, OUTPUT_ERROR);
    test_pp_term(f, -123, -1, INVALID_TERM);
    fclose(f);
  }
  printf("\n\n");

}

int main(void) {
  yices_init();
  init_types();
  init_terms();
  test_pp_types();
  test_pp_terms();
  yices_exit();

  return 0;
}
