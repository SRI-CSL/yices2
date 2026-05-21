#include <stdio.h>
#include <stdint.h>
#include <assert.h>

#include "yices.h"

#ifdef HAVE_MCSAT
#include "mcsat/cdclt/cdclt_sat_cache.h"
#endif

static context_t *make_mcsat_context(void) {
  ctx_config_t *config = yices_new_config();
  if (!config) return NULL;
  if (yices_set_config(config, "solver-type", "mcsat") < 0) {
    yices_free_config(config);
    return NULL;
  }
  context_t *ctx = yices_new_context(config);
  yices_free_config(config);
  return ctx;
}

static void test_bv_eq_sat(void) {
  context_t *ctx = make_mcsat_context();
  assert(ctx != NULL);
  type_t bv8  = yices_bv_type(8);
  term_t x    = yices_new_uninterpreted_term(bv8);
  term_t five = yices_bvconst_uint32(8, 5);
  assert(yices_assert_formula(ctx, yices_bveq_atom(x, five)) == 0);
  assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);
  yices_free_context(ctx);
  printf("PASS: test_bv_eq_sat\n");
}

static void test_bv_uge_sat(void) {
  context_t *ctx = make_mcsat_context();
  assert(ctx != NULL);
  type_t bv8  = yices_bv_type(8);
  term_t x     = yices_new_uninterpreted_term(bv8);
  term_t three = yices_bvconst_uint32(8, 3);
  term_t five  = yices_bvconst_uint32(8, 5);
  /* x >= 3 AND x = 5 is SAT */
  assert(yices_assert_formula(ctx, yices_bvge_atom(x, three)) == 0);
  assert(yices_assert_formula(ctx, yices_bveq_atom(x, five))  == 0);
  assert(yices_check_context(ctx, NULL) == YICES_STATUS_SAT);
  yices_free_context(ctx);
  printf("PASS: test_bv_uge_sat\n");
}

static void test_bv_unsat(void) {
  context_t *ctx = make_mcsat_context();
  assert(ctx != NULL);
  type_t bv8  = yices_bv_type(8);
  term_t x    = yices_new_uninterpreted_term(bv8);
  term_t zero = yices_bvconst_uint32(8, 0);
  /* x = 0 AND x > 0 is UNSAT */
  assert(yices_assert_formula(ctx, yices_bveq_atom(x, zero)) == 0);
  assert(yices_assert_formula(ctx, yices_bvgt_atom(x, zero)) == 0);
  assert(yices_check_context(ctx, NULL) == YICES_STATUS_UNSAT);
  yices_free_context(ctx);
  printf("PASS: test_bv_unsat\n");
}

static void test_bv_signed_comparison(void) {
  context_t *ctx = make_mcsat_context();
  assert(ctx != NULL);
  type_t bv8  = yices_bv_type(8);
  term_t x    = yices_new_uninterpreted_term(bv8);
  term_t s127 = yices_bvconst_uint32(8, 127); /* 0x7f = +127 signed */
  term_t neg1 = yices_bvconst_uint32(8, 255); /* 0xff = -1 signed   */
  /* bvsge(x, 127) AND x = 255 (= -1 signed) is UNSAT: -1 >=_s 127 is false */
  assert(yices_assert_formula(ctx, yices_bvsge_atom(x, s127)) == 0);
  assert(yices_assert_formula(ctx, yices_bveq_atom(x, neg1))  == 0);
  assert(yices_check_context(ctx, NULL) == YICES_STATUS_UNSAT);
  yices_free_context(ctx);
  printf("PASS: test_bv_signed_comparison\n");
}

#ifdef HAVE_MCSAT
static void test_bv_cache_hit(void) {
  /* Exercises the sat-cache with stand-in term_t integers -- no MCSAT needed.
   * Records SAT for {A,B,C} then verifies subset {A,B} is a cache hit. */
  cdclt_sat_cache_t c;
  cdclt_sat_cache_init(&c);
  term_t A = 10, B = 11, C = 12;
  assert(cdclt_sat_cache_register_atom(&c, A) == 0);
  assert(cdclt_sat_cache_register_atom(&c, B) == 1);
  assert(cdclt_sat_cache_register_atom(&c, C) == 2);
  ivector_t s;
  init_ivector(&s, 0);
  ivector_push(&s, A); ivector_push(&s, B); ivector_push(&s, C);
  cdclt_sat_cache_build(&c, &s);
  cdclt_sat_cache_record_sat(&c, c.scratch);
  ivector_t q;
  init_ivector(&q, 0);
  ivector_push(&q, A); ivector_push(&q, B);
  cdclt_sat_cache_build(&c, &q);
  assert(cdclt_sat_cache_lookup_sat(&c, c.scratch));
  delete_ivector(&s);
  delete_ivector(&q);
  cdclt_sat_cache_destroy(&c);
  printf("PASS: test_bv_cache_hit\n");
}
#endif /* HAVE_MCSAT */

int main(void) {
  yices_init();
#ifdef HAVE_MCSAT
  test_bv_cache_hit();          /* no live solver needed; requires MCSAT compiled in */
#endif
  if (!yices_has_mcsat()) {
    yices_exit();
    return 1;                   /* SKIP */
  }
  test_bv_eq_sat();
  test_bv_uge_sat();
  test_bv_unsat();
  test_bv_signed_comparison();
  yices_exit();
  printf("ALL PASS\n");
  return 0;
}
