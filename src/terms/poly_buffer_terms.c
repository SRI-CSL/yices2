/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */


#include "terms/poly_buffer_terms.h"

void poly_buffer_addmul_term(term_table_t *terms, poly_buffer_t *aux, term_t t, rational_t *a) {
  assert(is_arithmetic_term(terms, t) && is_pos_term(t));

  if (term_kind(terms, t) == ARITH_CONSTANT) {
    poly_buffer_addmul_monomial(aux, const_idx, a, rational_term_desc(terms, t));
  } else {
    poly_buffer_add_monomial(aux, t, a);
  }
}

void poly_buffer_submul_term(term_table_t *terms, poly_buffer_t *aux, term_t t, rational_t *a) {
  assert(is_arithmetic_term(terms, t) && is_pos_term(t));

  if (term_kind(terms, t) == ARITH_CONSTANT) {
    poly_buffer_submul_monomial(aux, const_idx, a, rational_term_desc(terms, t));
  } else {
    poly_buffer_sub_monomial(aux, t, a);
  }
}

void poly_buffer_add_term(term_table_t *terms, poly_buffer_t *aux, term_t t) {
  assert(is_arithmetic_term(terms, t) && is_pos_term(t));

  if (term_kind(terms, t) == ARITH_CONSTANT) {
    poly_buffer_add_const(aux, rational_term_desc(terms, t));
  } else {
    poly_buffer_add_var(aux, t);
  }
}

void poly_buffer_sub_term(term_table_t *terms, poly_buffer_t *aux, term_t t) {
  assert(is_arithmetic_term(terms, t) && is_pos_term(t));

  if (term_kind(terms, t) == ARITH_CONSTANT) {
    poly_buffer_sub_const(aux, rational_term_desc(terms, t));
  } else {
    poly_buffer_sub_var(aux, t);
  }
}


