/*
 * Tests for model clone/project support and adjacent model-domain behavior.
 */

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>

#include "api/yices_globals.h"
#include "model/models.h"
#include "yices.h"

static void check(bool cond, const char *msg) {
  if (!cond) {
    fprintf(stderr, "%s\n", msg);
    yices_print_error(stderr);
    assert(false);
  }
}

static bool vector_has_term(const term_vector_t *v, term_t t) {
  uint32_t i;

  for (i = 0; i < v->size; i++) {
    if (v->data[i] == t) {
      return true;
    }
  }
  return false;
}

static void test_collect_defined_terms_named_and_unnamed(void) {
  model_t *mdl;
  term_vector_t v;
  term_t x, y;

  x = yices_new_uninterpreted_term(yices_int_type());
  yices_set_term_name(x, "named_collect_x");
  y = yices_new_uninterpreted_term(yices_int_type());

  mdl = yices_new_model();
  check(mdl != NULL, "failed to create model");
  check(yices_model_set_int32(mdl, x, 10) == 0, "failed to set named term");
  check(yices_model_set_int32(mdl, y, 20) == 0, "failed to set unnamed term");

  yices_init_term_vector(&v);
  yices_model_collect_defined_terms(mdl, &v);

  check(v.size == 2, "expected exactly two defined terms");
  check(vector_has_term(&v, x), "missing named defined term");
  check(vector_has_term(&v, y), "missing unnamed defined term");

  yices_delete_term_vector(&v);
  yices_free_model(mdl);
}

static void test_collect_defined_terms_ignores_negative_keys(void) {
  model_t *mdl;
  term_vector_t v;
  term_t b, not_b;

  b = yices_new_uninterpreted_term(yices_bool_type());
  not_b = yices_not(b);

  mdl = yices_new_model();
  check(mdl != NULL, "failed to create model");

  model_map_term(mdl, not_b, vtbl_mk_bool(model_get_vtbl(mdl), true));

  yices_init_term_vector(&v);
  yices_model_collect_defined_terms(mdl, &v);

  check(v.size == 0, "negative model key must not be a defined term");
  check(!vector_has_term(&v, not_b), "negative key was collected");
  check(!vector_has_term(&v, b), "positive term should not be inferred from negative key");

  yices_delete_term_vector(&v);
  yices_free_model(mdl);
}

static void test_collect_defined_terms_alias_domain_only(void) {
  model_t *mdl;
  term_vector_t v;
  term_t x, y, x_plus_one;
  int32_t value;

  x = yices_new_uninterpreted_term(yices_int_type());
  y = yices_new_uninterpreted_term(yices_int_type());
  x_plus_one = yices_add(x, yices_int32(1));
  check(x_plus_one != NULL_TERM, "failed to build x + 1");

  mdl = yices_new_model();
  check(mdl != NULL, "failed to create model");
  model_add_substitution(mdl, y, x_plus_one);

  yices_init_term_vector(&v);
  yices_model_collect_defined_terms(mdl, &v);

  check(v.size == 1, "expected exactly one alias-domain defined term");
  check(vector_has_term(&v, y), "alias-domain term was not collected");
  check(!vector_has_term(&v, x), "default-completed alias RHS dependency was collected");

  check(yices_get_int32_value(mdl, y, &value) == 0, "failed to evaluate alias term");
  check(value == 1, "expected y = default(x) + 1");
  check(yices_get_int32_value(mdl, x, &value) == 0, "failed to evaluate defaulted term");
  check(value == 0, "expected default(x) = 0");

  yices_reset_term_vector(&v);
  yices_model_collect_defined_terms(mdl, &v);
  check(v.size == 1, "evaluation changed the defined-term domain");
  check(vector_has_term(&v, y), "alias-domain term was lost after evaluation");
  check(!vector_has_term(&v, x), "evaluation made default-completed term defined");

  yices_delete_term_vector(&v);
  yices_free_model(mdl);
}

int main(void) {
  yices_init();

  test_collect_defined_terms_named_and_unnamed();
  test_collect_defined_terms_ignores_negative_keys();
  test_collect_defined_terms_alias_domain_only();

  yices_exit();

  return 0;
}
