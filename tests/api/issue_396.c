#include "yices.h"

#include <stdbool.h>
#include "assert.h"

int
main(void)
{
  yices_init();
  type_t s1 = yices_real_type();
  term_t t1 = yices_new_uninterpreted_term(s1);
  term_t t2 = yices_new_uninterpreted_term(s1);
  term_t z = yices_parse_rational("0");
  term_t a1 = yices_arith_gt_atom(t2, z);
  term_t a2 = yices_arith_leq_atom(t2, t1);
  term_t a3 = yices_arith_lt_atom(t1, z);

  ctx_config_t* cfg = yices_new_config();
  context_t* ctx = yices_new_context(cfg);

  yices_assert_formula(ctx, a1);
  yices_assert_formula(ctx, a2);
  yices_assert_formula(ctx, a3);

  yices_check_context_with_assumptions(ctx, NULL, 1, &a2);
  yices_push(ctx);

  return 0;
}
