/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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



/*
 * Print the type table
 */
static void show_types(void) {
  printf("\n---- Type table ----\n");
  //  print_type_table(stdout, __yices_globals.types);
  pp_type_table(stdout, __yices_globals.types);
}


/*
 * Print the term table
 */
static void show_terms(void) {
  printf("\n---- Term table -----\n");
  //  print_term_table(stdout, __yices_globals.terms);
  pp_term_table(stdout, __yices_globals.terms);
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

static bool check_invalid_type(type_t tau, type_t bad) {
  error_report_t *rep;

  rep = yices_error_report();
  return tau == NULL_TYPE && bad_type(__yices_globals.types, rep->type1) && rep->type1 == bad;
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
  assert(check_invalid_type(test, aux[2]));

  test = yices_function_type(0, NULL, real);
  assert(check_pos_int_required(test));

  test = yices_function_type(UINT32_MAX, NULL, real);
  assert(check_too_many_arguments(test, UINT32_MAX));

  test = yices_function_type(3, aux, real);
  assert(check_invalid_type(test, aux[2]));

  aux[2] = T2;
  test = yices_function_type(3, aux, -4);
  assert(check_invalid_type(test, -4));

  printf("PASS: %s\n", __func__);
  fflush(stdout);
}



/*
 * Check that a term descriptor matches what's expected
 */
static bool check_constant_term(term_t t, type_t tau, int32_t idx) {
  return t >= 0 && is_pos_term(t) &&
    term_kind(__yices_globals.terms, t) == CONSTANT_TERM &&
    term_type(__yices_globals.terms, t) == tau &&
    constant_term_index(__yices_globals.terms, t) == idx;
}

static bool check_uninterpreted_term(term_t t, type_t tau) {
  return t >= 0 && is_pos_term(t) &&
    term_kind(__yices_globals.terms, t) == UNINTERPRETED_TERM &&
    term_type(__yices_globals.terms, t) == tau;
}


/*
 * CHECKS ON UNIT-TYPE REPRESENTATIVES
 */

static bool check_unit_rep(term_t t, type_t tau);

static bool check_unit_tuple(term_t t, type_t tau) {
  tuple_type_t *d;
  composite_term_t *c;
  uint32_t i, n;

  if (t < 0 || is_neg_term(t) ||
      term_kind(__yices_globals.terms, t) != TUPLE_TERM ||
      term_type(__yices_globals.terms, t) != tau) {
    return false;
  }

  d = tuple_type_desc(__yices_globals.types, tau);
  c = tuple_term_desc(__yices_globals.terms, t);
  if (d->nelem != c->arity) {
    return false;
  }

  n = d->nelem;
  for (i=0; i<n; i++) {
    if (! check_unit_rep(c->arg[i], d->elem[i])) {
      return false;
    }
  }

  return true;
}

static bool check_unit_rep(term_t t, type_t tau) {
  if (is_function_type(__yices_globals.types, tau)) {
    return check_uninterpreted_term(t, tau);
  } else if (is_scalar_type(__yices_globals.types, tau)) {
    return check_constant_term(t, tau, 0);
  } else {
    assert(is_tuple_type(__yices_globals.types, tau));
    return check_unit_tuple(t, tau);
  }
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
    assert(check_unit_rep(x, tau));

    y = yices_new_uninterpreted_term(tau);
    assert(x == y);

  } else {
    x = yices_new_uninterpreted_term(tau);
    assert(check_uninterpreted_term(x, tau));

    y = yices_new_uninterpreted_term(tau);
    assert(check_uninterpreted_term(y, tau));

    z = yices_new_uninterpreted_term(tau);
    assert(check_uninterpreted_term(z, tau));

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
    assert(check_constant_term(x, tau, 0));

    y = yices_constant(tau, 0);
    assert(y == x);

    x = yices_constant(tau, 24);
    assert(check_constant_term(x, tau, 24));

    y = yices_constant(tau, 24);
    assert(y == x);

    x = yices_constant(tau, -20);
    assert(x == NULL_TERM && yices_error_code() == INVALID_CONSTANT_INDEX);

  } else {
    assert(is_scalar_type(__yices_globals.types, tau));

    n = scalar_type_cardinal(__yices_globals.types, tau);
    for (i=0; i<n; i++) {
      x = yices_constant(tau, i);
      assert(check_constant_term(x, tau, i));

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



/*
 * Error codes for constant & uninterpreted term constructors
 */
static bool check_invalid_type2(term_t t, type_t tau) {
  error_report_t *rep;

  rep = yices_error_report();
  return t == NULL_TERM && yices_error_code() == INVALID_TYPE && rep->type1 == tau;
}

static bool check_scalar_or_utype_required(term_t t, type_t tau) {
  error_report_t *rep;

  rep = yices_error_report();
  return t == NULL_TERM && yices_error_code() == SCALAR_OR_UTYPE_REQUIRED && rep->type1 == tau;
}


static void test_constant_errors(void) {
  term_t x;

  x = yices_new_uninterpreted_term(-23);
  assert(check_invalid_type2(x, -23));

  x = yices_constant(10000, 0);
  assert(check_invalid_type2(x, 10000));

  x = yices_constant(real, 0);
  assert(check_scalar_or_utype_required(x, real));

  printf("PASS: %s\n", __func__);
  fflush(stdout);
}




/*
 * ARITHMETIC CONSTANTS
 */
static bool check_arith_constant(term_t t, rational_t *q) {
  type_t tau;

  if (t < 0 || is_neg_term(t) ||
      term_kind(__yices_globals.terms, t) != ARITH_CONSTANT ||
      q_neq(rational_term_desc(__yices_globals.terms, t), q)) {
    return false;
  }

  tau = term_type(__yices_globals.terms, t);
  return q_is_integer(q) ? is_integer_type(tau) : is_real_type(tau);
}

static void test_arith_constants(void) {
  mpq_t mpq;
  mpz_t mpz;
  rational_t q;
  term_t x, y;

  q_init(&q);   // q is zero

  // Many ways of constructing 0
  x = yices_zero();
  assert(check_arith_constant(x, &q));

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
  assert(check_arith_constant(x, &q));

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
  assert(check_arith_constant(x, &q));

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


/*
 * BIT-VECTOR CONSTANTS
 */
static bool check_bv64_constant(term_t t, uint64_t v, uint32_t n) {
  bvconst64_term_t *c;
  type_t tau;

  if (t < 0 || is_neg_term(t) || term_kind(__yices_globals.terms, t) != BV64_CONSTANT) {
    return false;
  }

  tau = term_type(__yices_globals.terms, t);
  c = bvconst64_term_desc(__yices_globals.terms, t);
  v = norm64(v, n);

  return c->bitsize == n && c->value == v && check_bv_type(tau, n);
}


static bool check_bv_constant(term_t t, uint32_t *v, uint32_t n) {
  bvconst_term_t *c;
  type_t tau;

  if (t < 0 || is_neg_term(t) || term_kind(__yices_globals.terms, t) != BV_CONSTANT) {
    return false;
  }

  tau = term_type(__yices_globals.terms, t);
  c = bvconst_term_desc(__yices_globals.terms, t);
  bvconst_normalize(v, n);

  return c->bitsize == n && bvconst_eq(c->data, v, (n + 31)>>5) && check_bv_type(tau, n);
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
  assert(check_bv64_constant(x, 0, 10));

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
  assert(check_bv_constant(x, aux, 65));

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
  assert(check_bv64_constant(x, 1, 1));

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
  assert(check_bv_constant(x, aux, 68));

  y = yices_parse_bvhex("FFfffffffffffffff");
  assert(check_bv_constant(y, aux, 68) && y == x);

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





int main(void) {
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

  show_types();
  show_terms();

  yices_exit();

  printf("All tests succeeded\n");
  
  return 0;
}
