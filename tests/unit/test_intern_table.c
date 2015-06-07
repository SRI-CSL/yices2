/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST INTERNALIZATION/SUBSTITUTION TABLE
 */

#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>

#include "utils/int_vectors.h"
#include "utils/string_buffers.h"
#include "api/yices_globals.h"
#include "context/internalization_table.h"
#include "io/term_printer.h"
#include "io/type_printer.h"
#include "io/yices_pp.h"

#include "yices.h"

#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif


/*
 * Print the type table
 */
static void __attribute__((unused)) show_types(void) {
  printf("\n---- Type table ----\n");
  //  print_type_table(stdout, __yices_globals.types);
  pp_type_table(stdout, __yices_globals.types);
}


/*
 * Print the term table
 */
static void  __attribute__((unused)) show_terms(void) {
  printf("\n---- Term table -----\n");
  //  print_term_table(stdout, __yices_globals.terms);
  pp_term_table(stdout, __yices_globals.terms);
}




/*
 * TERM/TYPE STORE
 */

/*
 * Base types:
 * - unit = singleton type (scalar type of card 1)
 * - compass = scalar type with 4 elements
 * - unint1, unint2 = two uninterpreted types
 */
static type_t unit, compass, unint1, unint2;

/*
 * All pair types formed from int and real
 */
static type_t int_int_pairs, int_real_pairs, real_int_pairs, real_real_pairs;


/*
 * String buffer: used to construct variable names
 */
static string_buffer_t string_buffer;

/*
 * Data structure: four vectors
 * - tau = array of randomly generated types
 * - terms = array of randomly generated terms
 * - vars = uninterpreted terms
 * - constants = constant terms
 */
typedef struct test_store_s {
  ivector_t types;
  ivector_t terms;
  ivector_t vars;
  ivector_t constants;
} test_store_t;


static void init_store(test_store_t *s) {
  init_ivector(&s->types, 20);
  init_ivector(&s->terms, 20);
  init_ivector(&s->vars, 20);
  init_ivector(&s->constants, 20);
}

static void delete_store(test_store_t *s) {
  delete_ivector(&s->types);
  delete_ivector(&s->terms);
  delete_ivector(&s->vars);
  delete_ivector(&s->constants);
}



/*
 * Get a random element from vector v (must be non-empty)
 */
static int32_t sample_vector(ivector_t *v) {
  uint32_t i, n;

  n = v->size;
  assert(n > 0);
  i = random() % n;
  return  v->data[i];
}


/*
 * Get k random elements from vector v and store them in a[0.. k-1]
 */
static void multi_sample_vector(ivector_t *v, int32_t *a, uint32_t k) {
  uint32_t i;

  for (i=0; i<k; i++) {
    a[i] = sample_vector(v);
  }
}



/*
 * Build the pair type tau1 x tau2
 */
static type_t pair_type(type_t tau1, type_t tau2) {
  type_t aux[2];

  aux[0] = tau1;
  aux[1] = tau2;
  return yices_tuple_type(2, aux);
}


/*
 * Add basic types to store s and store them
 */
static void add_base_types(test_store_t *s) {
  ivector_push(&s->types, yices_bool_type());
  ivector_push(&s->types, yices_int_type());
  ivector_push(&s->types, yices_real_type());
  ivector_push(&s->types, yices_bv_type(1));
  ivector_push(&s->types, yices_bv_type(32));
  ivector_push(&s->types, yices_bv_type(65));

  unint1 = yices_new_uninterpreted_type();
  yices_set_type_name(unint1, "T");
  ivector_push(&s->types, unint1);

  unint2 = yices_new_uninterpreted_type();
  yices_set_type_name(unint2, "U");
  ivector_push(&s->types, unint2);

  unit = yices_new_scalar_type(1);
  yices_set_type_name(unit, "UNIT");
  ivector_push(&s->types, unit);

  compass = yices_new_scalar_type(4);
  yices_set_type_name(compass, "COMPASS");
  ivector_push(&s->types, compass);

  int_int_pairs = pair_type(yices_int_type(), yices_int_type());
  ivector_push(&s->types, int_int_pairs);

  int_real_pairs = pair_type(yices_int_type(), yices_real_type());
  ivector_push(&s->types, int_real_pairs);

  real_int_pairs = pair_type(yices_real_type(), yices_int_type());
  ivector_push(&s->types, real_int_pairs);

  real_real_pairs = pair_type(yices_real_type(), yices_real_type());
  ivector_push(&s->types, real_real_pairs);
}


/*
 * Create n random function and tuple types and add them to s
 */
static void add_random_types(test_store_t *s, uint32_t n) {
  uint32_t i;
  type_t aux[4];
  type_t tau, sigma;
  ivector_t buffer;

  tau = NULL_TYPE;

  init_ivector(&buffer, n);

  for (i=0; i<n; i++) {
    switch (random() % 4) {
    case 0:
      // pairs
      multi_sample_vector(&s->types, aux, 2);
      tau = yices_tuple_type(2, aux);
      break;

    case 1:
      // triples
      multi_sample_vector(&s->types, aux, 3);
      tau = yices_tuple_type(3, aux);
      break;

    case 2:
      // unary functions
      multi_sample_vector(&s->types, aux, 1);
      sigma = sample_vector(&s->types);
      tau = yices_function_type(1, aux, sigma);
      break;

    case 3:
      // binary functions
      multi_sample_vector(&s->types, aux, 2);
      sigma = sample_vector(&s->types);
      tau = yices_function_type(2, aux, sigma);
      break;
    }

    assert(tau >= 0);
    ivector_push(&buffer, tau);
  }

  assert(buffer.size == n);
  for (i=0; i<n; i++) {
    tau = buffer.data[i];
    ivector_push(&s->types, tau);
  }

  delete_ivector(&buffer);
}



/*
 * Create constants of each basic type
 */
static void add_base_constants(test_store_t *s) {
  term_t t;

  ivector_push(&s->constants, yices_true());
  ivector_push(&s->constants, yices_false());

  ivector_push(&s->constants, yices_zero());
  ivector_push(&s->constants, yices_int32(1));
  ivector_push(&s->constants, yices_int32(-1));
  ivector_push(&s->constants, yices_rational32(1, 3));
  ivector_push(&s->constants, yices_rational32(-2, 5));

  ivector_push(&s->constants, yices_bvconst_zero(1));
  ivector_push(&s->constants, yices_bvconst_one(1));
  ivector_push(&s->constants, yices_bvconst_zero(32));
  ivector_push(&s->constants, yices_bvconst_one(32));
  ivector_push(&s->constants, yices_bvconst_minus_one(32));
  ivector_push(&s->constants, yices_bvconst_uint32(32, 0x55555555u));

  t = yices_constant(unint1, 0);
  yices_set_term_name(t, "K0");
  ivector_push(&s->constants, t);

  t = yices_constant(unint1, 1);
  yices_set_term_name(t, "K1");
  ivector_push(&s->constants, t);

  t = yices_constant(unint2, 0);
  yices_set_term_name(t, "L0");
  ivector_push(&s->constants, t);

  t = yices_constant(unint2, 1);
  yices_set_term_name(t, "L1");
  ivector_push(&s->constants, t);

  t = yices_constant(unit, 0);
  yices_set_term_name(t, "Solo");
  ivector_push(&s->constants, t);

  t = yices_constant(compass, 0);
  yices_set_term_name(t, "North");
  ivector_push(&s->constants, t);

  t = yices_constant(compass, 1);
  yices_set_term_name(t, "South");
  ivector_push(&s->constants, t);

  t = yices_constant(compass, 2);
  yices_set_term_name(t, "East");
  ivector_push(&s->constants, t);

  t = yices_constant(compass, 3);
  yices_set_term_name(t, "West");
  ivector_push(&s->constants, t);
}



/*
 * Add n variables of type tau, named pref<k> to pref<k+n-1>
 */
static void add_variables_of_type(test_store_t *s, uint32_t n, type_t tau, char *pref, uint32_t k) {
  uint32_t i;
  term_t t;

  for (i=0; i<n; i++) {
    string_buffer_reset(&string_buffer);
    string_buffer_append_string(&string_buffer, pref);
    string_buffer_append_uint32(&string_buffer, k+i);
    string_buffer_close(&string_buffer);

    t = yices_new_uninterpreted_term(tau);
    yices_set_term_name(t, string_buffer.data);
    ivector_push(&s->vars, t);
  }

}


/*
 * Create n uninterpreted terms of base types and other types in s->types
 */
static void add_variables(test_store_t *s, uint32_t n) {
  uint32_t tup_base, fun_base;
  uint32_t i, k;
  type_t tau;

  add_variables_of_type(s, n, yices_bool_type(), "p", 0);
  add_variables_of_type(s, n, yices_int_type(),  "i", 0);
  add_variables_of_type(s, n, yices_real_type(), "x", 0);
  add_variables_of_type(s, n, yices_bv_type(1),  "u", 0);
  add_variables_of_type(s, n, yices_bv_type(32), "v", 0);
  add_variables_of_type(s, n, yices_bv_type(65), "w", 0);
  add_variables_of_type(s, n, unint1, "a", 0);
  add_variables_of_type(s, n, unint2, "b", 0);
  add_variables_of_type(s, n, compass, "c", 0);

  tup_base = 0;
  fun_base = 0;
  k = s->types.size;
  for (i=0; i<k; i++) {
    tau = s->types.data[i];
    if (is_tuple_type(__yices_globals.types, tau)) {
      add_variables_of_type(s, n, tau, "r", tup_base);
      tup_base += n;
    } else if (is_function_type(__yices_globals.types, tau)) {
      add_variables_of_type(s, n, tau, "f", fun_base);
      fun_base += n;
    }
  }
}


/*
 * Add all variables and constants to the terms vector
 */
static void collect_vars_and_constants(test_store_t *s) {
  uint32_t i, n;
  term_t t;

  n = s->constants.size;
  for (i=0; i<n; i++) {
    t = s->constants.data[i];
    assert(good_term(__yices_globals.terms, t));
    ivector_push(&s->terms, t);
  }

  n = s->vars.size;
  for (i=0; i<n; i++) {
    t = s->vars.data[i];
    assert(good_term(__yices_globals.terms, t));
    ivector_push(&s->terms, t);
  }
}



/*
 * TERM SAMPLING
 */

/*
 * Return a random term of v that satisfies p
 */
static term_t random_term(ivector_t *v, int32_t (*p)(term_t)) {
  uint32_t i, n, m;
  term_t t, pick;

  pick = NULL_TERM;
  m = 0;

  n = v->size;
  for (i=0; i<n; i++) {
    t = v->data[i];
    if (p(t)) {
      m ++;
      if ( (((uint32_t) random()) % m) == 0) {
	pick = t;
      }
    }
  }

  return pick;
}

static term_t random_bool_term(ivector_t *v) {
  term_t t;

  t = random_term(v, yices_term_is_bool);
  if (random() % 10 >= 6) {
    t = yices_not(t);
  }
  return t;
}

static term_t random_arith_term(ivector_t *v) {
  return random_term(v, yices_term_is_arithmetic);
}

static term_t random_bv_term(ivector_t *v) {
  return random_term(v, yices_term_is_bitvector);
}

static term_t random_tuple_term(ivector_t *v) {
  return random_term(v, yices_term_is_tuple);
}

static term_t random_function_term(ivector_t *v) {
  return random_term(v, yices_term_is_function);
}


/*
 * Select randomly a term of type tau
 */
static term_t random_term_of_type(ivector_t *v, type_t tau) {
  uint32_t i, n, m;
  term_t t, pick;

  pick = NULL_TERM;
  m = 0;

  n = v->size;
  for (i=0; i<n; i++) {
    t = v->data[i];
    if (yices_type_of_term(t) == tau) {
      m ++;
      if ( (((uint32_t) random()) % m) == 0) {
	pick = t;
      }
    }
  }

  return pick;
}


/*
 * Select randomly a term whose type is a subtype of tau
 */
static term_t random_term_of_subtype(ivector_t *v, type_t tau) {
  uint32_t i, n, m;
  term_t t, pick;
  type_t sigma;

  pick = NULL_TERM;
  m = 0;

  n = v->size;
  for (i=0; i<n; i++) {
    t = v->data[i];
    sigma = yices_type_of_term(t);
    if (is_subtype(__yices_globals.types, sigma, tau)) {
      m ++;
      if ( (((uint32_t) random()) % m) == 0) {
	pick = t;
      }
    }
  }

  return pick;
}


/*
 * Select randomly a term of a type compatible with t0 type
 */
static term_t random_compatible_term(ivector_t *v, term_t t0) {
  uint32_t i, n, m;
  term_t t, pick;
  type_t sigma, tau;

  tau = yices_type_of_term(t0);

  pick = NULL_TERM;
  m = 0;

  n = v->size;
  for (i=0; i<n; i++) {
    t = v->data[i];
    sigma = yices_type_of_term(t);
    if (compatible_types(__yices_globals.types, sigma, tau)) {
      m ++;
      if ( (((uint32_t) random()) % m) == 0) {
	pick = t;
      }
    }
  }

  return pick;
}




/*
 * Construct random terms
 */
static term_t random_ite(test_store_t *s) {
  term_t a, b, c;

  c = random_bool_term(&s->terms);
  a = sample_vector(&s->terms);
  b = random_compatible_term(&s->terms, a);

  return yices_ite(c, a, b);
}

static term_t random_apply(test_store_t *s) {
  term_t f;
  type_t tau, sigma;
  term_t aux[4];
  uint32_t i, n;

  f = random_function_term(&s->terms);
  tau = yices_type_of_term(f);
  n = function_type_arity(__yices_globals.types, tau);

  assert(n <= 4);
  for (i=0; i<n; i++) {
    sigma = function_type_domain(__yices_globals.types, tau, i);
    aux[i] = random_term_of_subtype(&s->terms, sigma);
  }

  return yices_application(f, n, aux);
}

static term_t random_eq(test_store_t *s) {
  term_t a, b;

  a = sample_vector(&s->terms);
  b = random_compatible_term(&s->terms, a);

  return yices_eq(a, b);
}

static term_t random_or(test_store_t *s) {
  term_t a, b;

  a = random_bool_term(&s->terms);
  b = random_bool_term(&s->terms);

  return yices_or2(a, b);
}

static term_t random_and(test_store_t *s) {
  term_t a, b;

  a = random_bool_term(&s->terms);
  b = random_bool_term(&s->terms);

  return yices_and2(a, b);
}

static term_t random_xor(test_store_t *s) {
  term_t a, b;

  a = random_bool_term(&s->terms);
  b = random_bool_term(&s->terms);

  return yices_xor2(a, b);
}

static term_t random_pair(test_store_t *s) {
  term_t aux[2];

  aux[0] = sample_vector(&s->terms);
  aux[1] = sample_vector(&s->terms);

  return yices_tuple(2, aux);
}

static term_t random_triple(test_store_t *s) {
  term_t aux[3];

  aux[0] = sample_vector(&s->terms);
  aux[1] = sample_vector(&s->terms);
  aux[2] = sample_vector(&s->terms);

  return yices_tuple(3, aux);
}

static term_t random_select(test_store_t *s) {
  term_t t;
  type_t tau;
  uint32_t i, n;

  t = random_tuple_term(&s->terms);
  tau = yices_type_of_term(t);
  n = tuple_type_arity(__yices_globals.types, tau);
  i = ((uint32_t) random()) % n;

  return yices_select(i+1, t);
}

static term_t random_update(test_store_t *s) {
  term_t f, v;
  type_t tau, sigma;
  term_t aux[4];
  uint32_t i, n;

  f = random_function_term(&s->terms);
  tau = yices_type_of_term(f);
  n = function_type_arity(__yices_globals.types, tau);

  assert(n <= 4);
  for (i=0; i<n; i++) {
    sigma = function_type_domain(__yices_globals.types, tau, i);
    aux[i] = random_term_of_subtype(&s->terms, sigma);
  }

  sigma = function_type_range(__yices_globals.types, tau);
  v = random_term_of_subtype(&s->terms, sigma);

  return yices_update(f, n, aux, v);
}

static term_t random_distinct(test_store_t *s) {
  term_t aux[4];

  aux[0] = sample_vector(&s->terms);
  aux[1] = random_compatible_term(&s->terms, aux[0]);
  aux[2] = random_compatible_term(&s->terms, aux[0]);
  aux[3] = random_compatible_term(&s->terms, aux[0]);

  return yices_distinct(4, aux);
}


static term_t random_add(test_store_t *s) {
  term_t a, b;

  a = random_arith_term(&s->terms);
  b = random_arith_term(&s->terms);

  return yices_add(a, b);
}


static term_t random_sub(test_store_t *s) {
  term_t a, b;

  a = random_arith_term(&s->terms);
  b = random_arith_term(&s->terms);

  return yices_sub(a, b);
}


static term_t random_neg(test_store_t *s) {
  term_t a;

  a = random_arith_term(&s->terms);

  return yices_neg(a);
}


static term_t random_mul(test_store_t *s) {
  term_t a, b;

  a = random_arith_term(&s->terms);
  b = random_arith_term(&s->terms);

  return yices_mul(a, b);
}


static term_t random_square(test_store_t *s) {
  term_t a;

  a = random_arith_term(&s->terms);

  return yices_square(a);
}


static term_t random_geq(test_store_t *s) {
  term_t a, b;

  a = random_arith_term(&s->terms);
  b = random_arith_term(&s->terms);

  return yices_arith_geq_atom(a, b);
}


static term_t random_leq(test_store_t *s) {
  term_t a, b;

  a = random_arith_term(&s->terms);
  b = random_arith_term(&s->terms);

  return yices_arith_leq_atom(a, b);
}


static term_t random_gt(test_store_t *s) {
  term_t a, b;

  a = random_arith_term(&s->terms);
  b = random_arith_term(&s->terms);

  return yices_arith_gt_atom(a, b);
}


static term_t random_lt(test_store_t *s) {
  term_t a, b;

  a = random_arith_term(&s->terms);
  b = random_arith_term(&s->terms);

  return yices_arith_lt_atom(a, b);
}


static term_t random_bvadd(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvadd(a, b);
}


static term_t random_bvsub(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvsub(a, b);
}


static term_t random_bvneg(test_store_t *s) {
  term_t a;

  a = random_bv_term(&s->terms);

  return yices_bvneg(a);
}


static term_t random_bvmul(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvmul(a, b);
}


static term_t random_bvsquare(test_store_t *s) {
  term_t a;

  a = random_bv_term(&s->terms);

  return yices_bvsquare(a);
}


static term_t random_bvdiv(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvdiv(a, b);
}


static term_t random_bvrem(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvrem(a, b);
}


static term_t random_bvsdiv(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvsdiv(a, b);
}


static term_t random_bvsrem(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvsrem(a, b);
}


static term_t random_bvnot(test_store_t *s) {
  term_t a;

  a = random_bv_term(&s->terms);

  return yices_bvnot(a);
}


static term_t random_bvand(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvand2(a, b);
}


static term_t random_bvor(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvor2(a, b);
}


static term_t random_bvxor(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvxor2(a, b);
}


static term_t random_bvshl(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvshl(a, b);
}


static term_t random_bvlshr(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvlshr(a, b);
}


static term_t random_bvashr(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvashr(a, b);
}


static term_t random_bvconcat(test_store_t *s) {
  term_t a, b;

  a = random_bv_term(&s->terms);
  b = random_bv_term(&s->terms);

  return yices_bvconcat2(a, b);
}


static term_t random_bvextract(test_store_t *s) {
  term_t a;
  uint32_t i, j, n;

  a = random_bv_term(&s->terms);
  n = yices_term_bitsize(a);
  j = ((uint32_t) random()) % n;
  i = 0;
  if (j > 0) {
    i = ((uint32_t) random()) % j;
  }

  return yices_bvextract(a, i, j);
}


static term_t random_sign_extend(test_store_t *s) {
  term_t a;
  uint32_t n;

  a = random_bv_term(&s->terms);
  n = ((uint32_t) random()) % 5;

  return yices_sign_extend(a, n);
}


static term_t random_zero_extend(test_store_t *s) {
  term_t a;
  uint32_t n;

  a = random_bv_term(&s->terms);
  n = ((uint32_t) random()) % 5;

  return yices_zero_extend(a, n);
}


static term_t random_bvarray(test_store_t *s) {
  term_t aux[4];

  aux[0] = random_bool_term(&s->terms);
  aux[1] = random_bool_term(&s->terms);
  aux[2] = random_bool_term(&s->terms);
  aux[3] = random_bool_term(&s->terms);

  return yices_bvarray(4, aux);
}


static term_t random_bitextract(test_store_t *s) {
  term_t a;
  uint32_t i, n;

  a = random_bv_term(&s->terms);
  n = yices_term_bitsize(a);
  assert(n > 0);
  i = ((uint32_t) random()) % n;

  return yices_bitextract(a, i);
}


static term_t random_bvge(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvge_atom(a, b);
}


static term_t random_bvle(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvle_atom(a, b);
}


static term_t random_bvgt(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvgt_atom(a, b);
}


static term_t random_bvlt(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvlt_atom(a, b);
}


static term_t random_bvsge(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvsge_atom(a, b);
}


static term_t random_bvsle(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvsle_atom(a, b);
}


static term_t random_bvsgt(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvsgt_atom(a, b);
}


static term_t random_bvslt(test_store_t *s) {
  term_t a, b;
  type_t tau;

  a = random_bv_term(&s->terms);
  tau = yices_type_of_term(a);
  b = random_term_of_type(&s->terms, tau);

  return yices_bvslt_atom(a, b);
}




/*
 * Table to select one of the above constructors
 * Each record in the table contains:
 * - function pointer
 * - name
 * - weight
 * The probability of selecting i is weight[i]/sum of all weights
 * - sum of all weights = 10000 (50 * 200)
 */
typedef term_t (*rand_cnstr_t)(test_store_t *s);

typedef struct rand_desc_s {
  rand_cnstr_t fun;
  char *name;
  uint32_t weight;
} rand_desc_t;

#define NUM_RAND_CONSTRUCTORS 50

static const rand_desc_t random_constr[NUM_RAND_CONSTRUCTORS] = {
  { random_ite, "random_ite", 500 },
  { random_apply, "random_apply", 500 },
  { random_eq, "random_eq", 500 },
  { random_update, "random_update", 300 },
  { random_distinct, "random_distinct", 200 },  // 2000

  { random_or, "random_or", 400 },
  { random_and, "random_and", 400 },
  { random_xor, "random_xor", 200 }, // 1000

  { random_pair, "random_pair", 250 },
  { random_triple, "random_triple", 250 },
  { random_select, "random_select", 500 }, // 1000

  { random_add, "random_add", 500 },
  { random_sub, "random_sub", 500 },
  { random_neg, "random_neg", 500 },
  { random_mul, "random_mul", 300 },
  { random_square, "random_square", 200 }, // 2000

  { random_geq, "random_geq", 250 },
  { random_leq, "random_leq", 250 },
  { random_gt, "random_gt", 250 },
  { random_lt, "random_lt", 250 },        // 1000

  { random_bvadd, "random_bvadd", 150 },
  { random_bvsub, "random_bvsub", 150 },
  { random_bvneg, "random_bvneg", 150 },
  { random_bvmul, "random_bvmul", 150 },
  { random_bvsquare, "random_bvsquare", 50 },
  { random_bvdiv, "random_bvdiv", 50 },
  { random_bvrem, "random_bvrem", 50 },
  { random_bvsdiv, "random_bvsdiv", 50 },
  { random_bvsrem, "random_bvsrem", 50 },
  { random_bvnot, "random_bvnot",  100 },
  { random_bvand, "random_bvand", 100 },
  { random_bvor, "random_bvor", 100 },
  { random_bvxor, "random_bvxor", 100 },
  { random_bvshl, "random_bvshl", 100 },
  { random_bvlshr, "random_bvlshr", 75 },
  { random_bvashr, "random_bvashr", 75 },
  { random_bvconcat, "random_bvconcat", 100 },
  { random_bvextract, "random_bvextract", 100 },
  { random_sign_extend, "random_sign_extend", 100 },
  { random_zero_extend, "random_zero_extend", 100 },
  { random_bvarray, "random_bvarray", 50 },
  { random_bitextract, "random_bitextract", 50 }, // 2000

  { random_bvge, "random_bvge", 125 },
  { random_bvle, "random_bvle", 125 },
  { random_bvgt, "random_bvgt", 125 },
  { random_bvlt, "random_bvlt", 125 },
  { random_bvsge, "random_bvsge", 125 },
  { random_bvsle, "random_bvsle", 125 },
  { random_bvsgt, "random_bvsgt", 125 },
  { random_bvslt, "random_bvslt", 125 },   // 1000
};


static term_t make_random_term(test_store_t *s) {
  uint32_t k, i, sum;

  k = ((uint32_t) random()) % 10000;
  i = 0;
  sum = random_constr[0].weight;
  while (sum < k) {
    i ++;
    assert(i < NUM_RAND_CONSTRUCTORS);
    sum += random_constr[i].weight;
  }

  return random_constr[i].fun(s);
}


/*
 * Build n random terms from what's in s->terms
 */
static void add_random_terms(test_store_t *s, uint32_t n) {
  uint32_t i;
  term_t t;
  ivector_t buffer;

  init_ivector(&buffer, n);

  for (i=0; i<n; i++) {
    t = make_random_term(s);
    assert(t >= 0);
    ivector_push(&buffer, t);
  }

  assert(buffer.size == n);
  for (i=0; i<n; i++) {
    t = buffer.data[i];
    ivector_push(&s->terms, t);
  }

  delete_ivector(&buffer);
}



/*
 * GLOBAL STORE
 */
static test_store_t store;


/*
 * Top-level store initialization:
 * - ntypes = number of random types
 * - nvars = number of variables per type
 * - nterms = number of random terms
 */
static void build_store(uint32_t ntypes, uint32_t nvars, uint32_t nterms) {
  init_string_buffer(&string_buffer, 40);
  init_store(&store);
  add_base_types(&store);
  add_random_types(&store, ntypes);
  add_base_constants(&store);
  add_variables(&store, nvars);
  collect_vars_and_constants(&store);
  add_random_terms(&store, nterms);

  //  show_types();
  //  show_terms();
}


/*
 * Delete the whole thing
 */
static void close_store(void) {
  delete_store(&store);
  delete_string_buffer(&string_buffer);
}






/*
 * INTERNALIZATION TABLE
 */

/*
 * Print the substitutions
 */
static void show_subst(yices_pp_t *printer, intern_tbl_t *tbl) {
  term_table_t *terms;
  uint32_t i, n;
  term_t t, r;

  terms = __yices_globals.terms;
  n = tbl->map.top; // number of terms in tbl->map
  for (i=0; i<n; i++) {
    if (good_term_idx(terms, i) && !intern_tbl_is_root_idx(tbl, i)) {
      t = pos_term(i);
      r = intern_tbl_find_root(tbl, t);
      pp_open_block(printer, PP_OPEN);
      pp_term_name(printer, terms, t);
      pp_string(printer, " -> ");
      pp_term(printer, terms, r);
      pp_close_block(printer, false);
      flush_yices_pp(printer);
    }
  }
}


/*
 * Print the internalization mapping
 */
static void show_mapping(yices_pp_t *printer, intern_tbl_t *tbl) {
  term_table_t *terms;
  type_table_t *types;
  uint32_t i, n;
  term_t r;
  int32_t k;
  type_t tau;

  terms = __yices_globals.terms;
  types = __yices_globals.types;

  n = tbl->map.top; // number of terms in tbl->map
  for (i=0; i<n; i++) {
    if (good_term_idx(terms, i) && intern_tbl_is_root_idx(tbl, i)) {
      r = pos_term(i);
      if (intern_tbl_root_is_mapped(tbl, r)) {
	k = intern_tbl_map_of_root(tbl, r);
	tau = intern_tbl_type_of_root(tbl, r);

	pp_open_block(printer, PP_OPEN);
	pp_term_name(printer, terms, r);
	pp_string(printer, "\tmapped to ");
	pp_int32(printer, k);
	pp_string(printer, " type ");
	pp_type(printer, types, tau);
	pp_close_block(printer, false);
	flush_yices_pp(printer);
      }
    }
  }
}



/*
 * Print the full table
 */
static void pp_intern_tbl(FILE *f, intern_tbl_t *tbl) {
  yices_pp_t printer;
  pp_area_t area;

  area.width = 120;
  area.height = UINT32_MAX;
  area.offset = 0;
  area.stretch = false;
  area.truncate = true;

  init_default_yices_pp(&printer, f, &area);
  show_subst(&printer, tbl);
  printf("\n");
  show_mapping(&printer, tbl);
  delete_yices_pp(&printer, false);
}


/*
 * Add substitution x := t to the table if it's valid
 */
static void test_subst(intern_tbl_t *tbl) {
  term_t x, t;

  x = sample_vector(&store.vars); // random variable
  t = random_compatible_term(&store.terms, x); // term of compatible type

  printf("\ntesting subst: ");
  print_term_name(stdout, __yices_globals.terms, x);
  printf(" := ");
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  x = intern_tbl_get_root(tbl, x);
  t = intern_tbl_get_root(tbl, t);
  if (intern_tbl_root_is_free(tbl, x) && intern_tbl_root_is_free(tbl, t)) {
    if (index_of(x) != index_of(t)) {
      printf("variable merging\n");
      intern_tbl_merge_classes(tbl, x, t);
    } else if (x == opposite_term(t)) {
      printf("invalid substitution\n");
    } else {
      assert(x == t);
      printf("no change\n");
    }
  } else if (is_constant_term(__yices_globals.terms, t)) {
    if (is_pos_term(x) && intern_tbl_valid_const_subst(tbl, x, t)) {
      printf("good constant substitution\n");
      intern_tbl_add_subst(tbl, x, t);
    } else {
      printf("invaid constant substitution\n");
    }
#if 0
    // removed intern_tbl_valid_subst from the code
  } else {
    if (is_pos_term(x) && intern_tbl_valid_subst(tbl, x, t)) {
      printf("good substitution\n");
      intern_tbl_add_subst(tbl, x, t);
    } else {
      printf("invalid substitution\n");
    }
#endif

  }
}


/*
 * Test subst n times
 */
static void repeat_test_subst(intern_tbl_t *tbl, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    test_subst(tbl);
  }

  printf("\n---\nNew intern table\n");
  pp_intern_tbl(stdout, tbl);
  printf("---\n\n");
}



/*
 * Select a random term and map it to integer x
 */
static void test_map(intern_tbl_t *tbl, int32_t x) {
  term_t t;

  t = sample_vector(&store.terms);

  printf("\ntesting map: ");
  print_term_name(stdout, __yices_globals.terms, t);
  printf(" --> %"PRId32"\n", x);

  t = intern_tbl_get_root(tbl, t);
  if (is_neg_term(t)) {
    printf("invalid map: root ");
    print_term_name(stdout, __yices_globals.terms, t);
    printf(" has negative polarity\n");
  } else if (intern_tbl_root_is_mapped(tbl, t)) {
    printf("invalid map: root ");
    print_term_name(stdout, __yices_globals.terms, t);
    printf(" is already mapped to %"PRId32"\n", intern_tbl_map_of_root(tbl, t));
  } else {
    printf("good map\n");
    intern_tbl_map_root(tbl, t, x);
  }
}

/*
 * Internalize n terms (map them to integers)
 */
static void repeat_test_map(intern_tbl_t *tbl, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    test_map(tbl, i);
  }

  printf("\n---\nNew intern table\n");
  pp_intern_tbl(stdout, tbl);
  printf("---\n\n");
}


static intern_tbl_t intern;


int main(void) {
  yices_init();
  build_store(10, 100, 10000);

  init_intern_tbl(&intern, 0, __yices_globals.terms);

  printf("\nINITIAL\n");
  pp_intern_tbl(stdout, &intern);
  repeat_test_subst(&intern, 10);
  repeat_test_subst(&intern, 10);

  repeat_test_map(&intern, 100);
  repeat_test_map(&intern, 100);

  printf("\nPUSH\n");
  intern_tbl_push(&intern);
  repeat_test_subst(&intern, 10);
  repeat_test_subst(&intern, 10);

  repeat_test_map(&intern, 100);
  repeat_test_map(&intern, 100);

  printf("\nPUSH\n");
  intern_tbl_push(&intern);
  repeat_test_subst(&intern, 10);
  repeat_test_subst(&intern, 10);

  repeat_test_map(&intern, 100);
  repeat_test_map(&intern, 100);

  printf("\nPOP\n");
  intern_tbl_pop(&intern);
  pp_intern_tbl(stdout, &intern);

  printf("\nPOP\n");
  intern_tbl_pop(&intern);
  pp_intern_tbl(stdout, &intern);

  printf("\nRESET\n");
  reset_intern_tbl(&intern);
  pp_intern_tbl(stdout, &intern);

  printf("\nPUSH\n");
  intern_tbl_push(&intern);
  printf("\nPUSH\n");
  intern_tbl_push(&intern);
  printf("\nPUSH\n");
  intern_tbl_push(&intern);
  repeat_test_subst(&intern, 20000);
  printf("\nPOP\n");
  intern_tbl_pop(&intern);
  pp_intern_tbl(stdout, &intern);
  printf("\nPOP\n");
  intern_tbl_pop(&intern);
  pp_intern_tbl(stdout, &intern);
  printf("\nPOP\n");
  intern_tbl_pop(&intern);
  pp_intern_tbl(stdout, &intern);

  delete_intern_tbl(&intern);

  close_store();
  yices_exit();

  return 0;
}
