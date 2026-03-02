/*
 * API coverage test for finite-field constructors, deconstructors, and model accessors.
 */

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <gmp.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "yices.h"

static void fail(const char *msg) {
  fprintf(stderr, "FAIL: %s\n", msg);
  yices_print_error(stderr);
  exit(2);
}

static void check(bool cond, const char *msg) {
  if (!cond) {
    fail(msg);
  }
}

static void check_mpz_si(const mpz_t z, long x, const char *msg) {
  if (mpz_cmp_si(z, x) != 0) {
    fail(msg);
  }
}

static void test_ff_type_and_constants(void) {
  mpz_t p, bad, v, z;
  type_t tau;
  term_t c;

  mpz_init_set_si(p, 7);
  mpz_init_set_si(bad, 8);
  mpz_init_set_si(v, 15);
  mpz_init(z);

  tau = yices_ff_type(p);
  check(tau != NULL_TYPE, "yices_ff_type(7) failed");

  check(yices_ff_type(bad) == NULL_TYPE, "yices_ff_type(8) should fail");
  check(yices_error_code() == INVALID_FFSIZE, "expected INVALID_FFSIZE for non-prime order");

  c = yices_ff_const(v, p);
  check(c != NULL_TERM, "yices_ff_const(15,7) failed");
  check(yices_term_constructor(c) == YICES_FF_CONSTANT, "expected YICES_FF_CONSTANT");
  check(yices_ff_const_value(c, z) == 0, "yices_ff_const_value failed");
  check_mpz_si(z, 1, "expected 15 mod 7 = 1");
  check(yices_type_of_term(c) == tau, "ff constant has wrong type");

  mpz_set_si(v, -1);
  c = yices_ff_const(v, p);
  check(c != NULL_TERM, "yices_ff_const(-1,7) failed");
  check(yices_ff_const_value(c, z) == 0, "yices_ff_const_value(-1 mod 7) failed");
  check_mpz_si(z, 6, "expected -1 mod 7 = 6");

  mpz_clear(z);
  mpz_clear(v);
  mpz_clear(bad);
  mpz_clear(p);
}

static void test_ff_term_builders_and_deconstruction(void) {
  mpz_t p, z;
  type_t tau;
  term_t x, y, c3;
  term_t t[2], s, pprod;
  term_t eq, neq, eq0, neq0;
  term_t comp;
  mpq_t q;
  uint32_t n;
  int seen_x, seen_y;
  int has_const;

  mpz_init_set_si(p, 7);
  mpz_init(z);
  mpq_init(q);

  tau = yices_ff_type(p);
  check(tau != NULL_TYPE, "ff type creation failed");
  x = yices_new_uninterpreted_term(tau);
  y = yices_new_uninterpreted_term(tau);
  check(x != NULL_TERM && y != NULL_TERM, "failed to create ff variables");

  check(yices_ff_add(x, y) != NULL_TERM, "yices_ff_add failed");
  check(yices_ff_sub(x, y) != NULL_TERM, "yices_ff_sub failed");
  check(yices_ff_neg(x) != NULL_TERM, "yices_ff_neg failed");
  check(yices_ff_mul(x, y) != NULL_TERM, "yices_ff_mul failed");
  check(yices_ff_square(x) != NULL_TERM, "yices_ff_square failed");
  check(yices_ff_power(x, 3) != NULL_TERM, "yices_ff_power failed");

  t[0] = x;
  t[1] = y;
  s = yices_ff_sum(2, t);
  check(s != NULL_TERM, "yices_ff_sum failed");
  check(yices_type_of_term(s) == tau, "yices_ff_sum wrong type");
  check(yices_term_constructor(s) == YICES_FF_SUM, "yices_ff_sum should build YICES_FF_SUM");

  pprod = yices_ff_product(2, t);
  check(pprod != NULL_TERM, "yices_ff_product failed");
  check(yices_type_of_term(pprod) == tau, "yices_ff_product wrong type");

  eq = yices_ff_eq_atom(x, y);
  neq = yices_ff_neq_atom(x, y);
  eq0 = yices_ff_eq0_atom(x);
  neq0 = yices_ff_neq0_atom(x);
  check(eq != NULL_TERM, "yices_ff_eq_atom failed");
  check(neq != NULL_TERM, "yices_ff_neq_atom failed");
  check(eq0 != NULL_TERM, "yices_ff_eq0_atom failed");
  check(neq0 != NULL_TERM, "yices_ff_neq0_atom failed");
  check(yices_term_is_bool(eq) == 1, "ff eq atom must be bool");
  check(yices_term_is_bool(neq) == 1, "ff neq atom must be bool");
  check(yices_term_is_bool(eq0) == 1, "ff eq0 atom must be bool");
  check(yices_term_is_bool(neq0) == 1, "ff neq0 atom must be bool");

  n = yices_term_num_children(s);
  check(n == 2, "expected 2 monomials in ff sum x+y");

  seen_x = 0;
  seen_y = 0;
  for (uint32_t i = 0; i < n; i++) {
    check(yices_ffsum_component(s, (int32_t)i, z, &comp) == 0, "yices_ffsum_component failed");
    check_mpz_si(z, 1, "expected coefficient 1 in x+y");
    if (comp == x) {
      seen_x = 1;
    } else if (comp == y) {
      seen_y = 1;
    } else {
      fail("unexpected monomial term in ff sum");
    }
  }
  check(seen_x && seen_y, "ffsum components should include x and y");

  check(yices_sum_component(s, 0, q, &comp) < 0, "yices_sum_component should reject ff sums");

  mpz_set_si(z, 3);
  c3 = yices_ff_const(z, p);
  check(c3 != NULL_TERM, "ff constant 3 failed");
  t[0] = c3;
  t[1] = x;
  s = yices_ff_sum(2, t);
  check(s != NULL_TERM, "ff sum with constant failed");
  n = yices_term_num_children(s);
  check(n >= 1, "unexpected empty ff sum");

  has_const = 0;
  for (uint32_t i = 0; i < n; i++) {
    check(yices_ffsum_component(s, (int32_t)i, z, &comp) == 0, "ffsum component (const+var) failed");
    if (comp == NULL_TERM) {
      check_mpz_si(z, 3, "expected standalone constant 3 in ff sum");
      has_const = 1;
    }
  }
  check(has_const, "expected NULL_TERM component for constant part");

  check(yices_ffsum_component(s, (int32_t)n, z, &comp) < 0, "ffsum out-of-bounds should fail");

  mpq_clear(q);
  mpz_clear(z);
  mpz_clear(p);
}

static void test_ff_model_accessors(void) {
  mpz_t p, z, val, out_val, out_mod, out_val2, out_mod2, rem;
  type_t tau;
  term_t v, i0;
  model_t *m;
  yval_t yv_nonff;

  mpz_init_set_si(p, 7);
  mpz_init_set_si(val, 6);
  mpz_init_set_si(z, 0);
  mpz_init(out_val);
  mpz_init(out_mod);
  mpz_init(out_val2);
  mpz_init(out_mod2);
  mpz_init(rem);

  tau = yices_ff_type(p);
  check(tau != NULL_TYPE, "ff type creation failed");
  v = yices_new_uninterpreted_term(tau);
  check(v != NULL_TERM, "failed to create ff model variable");

  m = yices_new_model();
  check(m != NULL, "failed to create model");

  check(yices_model_set_ff_mpz(m, v, val) == 0, "yices_model_set_ff_mpz failed");
  check(yices_get_ff_value(m, v, out_val, out_mod) == 0, "yices_get_ff_value failed");
  check_mpz_si(out_mod, 7, "model ff modulus should be 7");
  mpz_mod(rem, out_val, out_mod);
  check_mpz_si(rem, 6, "model ff value should be congruent to 6 mod 7");

  i0 = yices_int32(0);
  check(i0 != NULL_TERM, "yices_int32(0) failed");
  check(yices_get_value(m, i0, &yv_nonff) == 0, "yices_get_value(int const) failed");
  check(yices_val_get_ff(m, &yv_nonff, out_val2, out_mod2) < 0, "yices_val_get_ff should fail on non-FF yval");
  check(yices_error_code() == YVAL_INVALID_OP, "expected YVAL_INVALID_OP");

  check(yices_model_set_ff_mpz(m, v, z) < 0, "reassigning ff variable should fail");

  yices_free_model(m);
  mpz_clear(rem);
  mpz_clear(out_mod2);
  mpz_clear(out_val2);
  mpz_clear(out_mod);
  mpz_clear(out_val);
  mpz_clear(z);
  mpz_clear(val);
  mpz_clear(p);
}

int main(void) {
  yices_init();

  test_ff_type_and_constants();
  test_ff_term_builders_and_deconstruction();
  test_ff_model_accessors();

  yices_exit();
  return 0;
}
