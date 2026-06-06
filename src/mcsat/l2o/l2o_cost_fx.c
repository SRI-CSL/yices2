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

#include "l2o.h"
#include "l2o_internal.h"

#include <math.h>

//
// Term cost fx
//

/** evaluates an individual term */
static
double l2o_cost_fx_term_eval(l2o_cost_fx_t *fx, const l2o_search_state_t *state) {
  l2o_cost_fx_term_t *fx_t = (l2o_cost_fx_term_t*) fx;
  l2o_evaluator_set_state(&fx->evaluator, state);

  double sum = 0;
  for (uint32_t i = 0; i < fx_t->terms.size; ++i) {
    term_t t = fx_t->terms.data[i];
    sum += l2o_calculate(fx->l2o, t, &fx->evaluator);
  }
  return sum;
}

static
void l2o_cost_fx_term_update_cache(l2o_cost_fx_t *fx) {
  l2o_evaluator_update_cache(&fx->evaluator);
}

static
void l2o_cost_fx_term_get_free_vars(const l2o_cost_fx_t *fx, ivector_t *v) {
  l2o_t *l2o = fx->l2o;
  l2o_cost_fx_term_t *fx_t = (l2o_cost_fx_term_t*) fx;

  ivector_reset(v);
  for (uint32_t i = 0; i < fx_t->terms.size; ++i) {
    int_hmmap_find_all(&l2o->var_member, unsigned_term(fx_t->terms.data[i]), v);
  }
  ivector_remove_duplicates(v);
}

static
void l2o_cost_fx_term_destruct(l2o_cost_fx_t *fx) {
  l2o_cost_fx_term_t *fx_t = (l2o_cost_fx_term_t*) fx;
  l2o_evaluator_destruct(&fx->evaluator);
  delete_ivector(&fx_t->terms);
}

void l2o_cost_fx_term_construct(l2o_t *l2o, l2o_cost_fx_term_t *fx) {
  fx->fx.l2o = l2o;
  fx->fx.trail = NULL;
  fx->fx.eval = l2o_cost_fx_term_eval;
  fx->fx.update_cache = l2o_cost_fx_term_update_cache;
  fx->fx.get_free_vars = l2o_cost_fx_term_get_free_vars;
  fx->fx.destruct = l2o_cost_fx_term_destruct;
  l2o_evaluator_construct(l2o, &fx->fx.evaluator);
  init_ivector(&fx->terms, 0);
}

void l2o_cost_fx_term_add(l2o_cost_fx_term_t *fx, term_t t) {
  ivector_push(&fx->terms, t);
}
