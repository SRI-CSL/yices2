#include <stdbool.h>

#include "yices.h"

#include "assert.h"

/*
 * Create an MCSAT context 
 */
static context_t *make_mcsat_context(void) {
  ctx_config_t *config;
  context_t *context;
  int32_t code;

  config = yices_new_config();
  code = yices_set_config(config, "solver-type", "mcsat");
  if (code < 0) goto error;
  context = yices_new_context(config);
  if (context == NULL) goto error;
  yices_free_config(config);
  return context;

 error:
  yices_print_error(stderr);
  yices_free_config(config);
  return NULL;
}

int
main(void)
{
  context_t *ctx;

  yices_init();
  ctx = make_mcsat_context();

  type_t p = yices_new_uninterpreted_type();
  type_t r = yices_real_type();

  //type_t a = yices_function_type1(p, r);
  //type_t f = yices_function_type1(p, a);
  type_t f = yices_function_type1(p, r);
  //type_t g = yices_function_type2(p, a, r);

  term_t f1 = yices_new_uninterpreted_term(f);
  //term_t g1 = yices_new_uninterpreted_term(g);

  term_t c1 = yices_constant(p, 1);

  term_t t1 = yices_application1(f1, c1);
  //term_t t2 = yices_application2(g1, c1, t1);
  term_t zero = yices_zero();

  yices_assert_formula(ctx, yices_eq(zero, t1));

  smt_status_t status;
  status = yices_check_context(ctx, NULL);
  if (status != STATUS_SAT) {
    assert(false);
  }
  
  //model_t *model = yices_get_model(ctx, 1);

  return 0;
}
