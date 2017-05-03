/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
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


