#include <stdbool.h>

#include "yices.h"

#include "assert.h"

/*
 * Create an Yices context 
 */
static context_t *make_yices_context(void) {
  ctx_config_t *config;
  context_t *context;
  int32_t code;

  config = yices_new_config();
  code = yices_set_config(config, "solver-type", "dpllt");
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

/* (set-logic all)
 * (declare-sort p 0)
 * (declare-fun s () p)
 * (declare-fun p (p) p)
 * (assert (and (= (p s) (_ Const 1 p)) (= (_ Const 2 p) (p (_ Const 0 p)))))
 * (check-sat)
 * (get-model)
 */

int
main(void)
{
  context_t *ctx;

  yices_init();
  ctx = make_yices_context();

  type_t p = yices_new_uninterpreted_type();
  term_t s = yices_new_uninterpreted_term(p);

  type_t fun_p_to_p = yices_function_type1(p, p);
  term_t pp = yices_new_uninterpreted_term(fun_p_to_p);

  term_t c1 = yices_constant(p, 1);
  term_t c2 = yices_constant(p, 2);
  term_t c3 = yices_constant(p, 0);

  term_t t1 = yices_application1(pp, s);
  term_t t2 = yices_eq(t1, c1);

  term_t t3 = yices_application1(pp, c3);
  term_t t4 = yices_eq(c2, t3);

  term_t t5 = yices_and2(t2, t4);

  yices_assert_formula(ctx, t5);

  smt_status_t status;
  status = yices_check_context(ctx, NULL);
  if (status != STATUS_SAT) {
    assert(false);
  }

  model_t *model = yices_get_model(ctx, 1);
  if (!model) {
    assert(false);
  }

  yices_exit();

  return 0;
}
