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

#include "lp_data.h"

#include <stdbool.h>

#include <poly/polynomial.h>
#include <poly/integer.h>
#include <poly/polynomial_context.h>
#include <poly/variable_db.h>
#include <poly/feasibility_set.h>
#include <poly/variable_order.h>
#include <poly/variable_list.h>

#include "mcsat/mcsat_types.h"
#include "mcsat/plugin.h"
#include "mcsat/tracing.h"
#include "mcsat/gc.h"
#include "terms/terms.h"

void lp_data_init(lp_data_t *lp_data, mpz_t order, const plugin_context_t *plugin_ctx) {
  init_int_hmap(&lp_data->term_to_lp_var_map, 0);
  init_int_hmap(&lp_data->lp_var_to_term_map, 0);

  lp_int_ring_t *ring = (order == NULL || mpz_sgn(order) <= 0) ? lp_Z : lp_int_ring_create(order, true);

  lp_data->lp_var_db = lp_variable_db_new();
  lp_data->lp_var_order = lp_variable_order_new();
  lp_data->lp_var_order_size = 0;
  lp_data->lp_ctx = lp_polynomial_context_new(ring, lp_data->lp_var_db, lp_data->lp_var_order);
  lp_data->lp_assignment = lp_assignment_new(lp_data->lp_var_db);
  lp_data->lp_interval_assignment = lp_interval_assignment_new(lp_data->lp_var_db);

  scope_holder_construct(&lp_data->scope);

  lp_data->plugin_ctx = plugin_ctx;

  // Tracing in libpoly
  if (false) {
    lp_trace_enable("coefficient");
    lp_trace_enable("coefficient::sgn");
    lp_trace_enable("coefficient::interval");
    lp_trace_enable("polynomial::expensive");
  }
}

void lp_data_destruct(lp_data_t *lp_data) {
  delete_int_hmap(&lp_data->term_to_lp_var_map);
  delete_int_hmap(&lp_data->lp_var_to_term_map);

  lp_polynomial_context_detach(lp_data->lp_ctx);
  lp_variable_order_detach(lp_data->lp_var_order);
  lp_variable_db_detach(lp_data->lp_var_db);
  lp_assignment_delete(lp_data->lp_assignment);
  lp_interval_assignment_delete(lp_data->lp_interval_assignment);

  scope_holder_destruct(&lp_data->scope);
}

lp_data_t* lp_data_new(mpz_t order, const plugin_context_t *plugin_ctx) {
  lp_data_t *lp_data = safe_malloc(sizeof(lp_data_t));
  lp_data_init(lp_data, order, plugin_ctx);
  return lp_data;
}

void lp_data_delete(lp_data_t* lp_data) {
  lp_data_destruct(lp_data);
  safe_free(lp_data);
}

bool lp_data_is_order(lp_data_t *lp_data, mpz_t order) {
  assert(order == NULL || mpz_sgn(order) >= 0);

  if (order == NULL || mpz_sgn(order) == 0) {  // expecting Z
    return lp_data->lp_ctx->K == lp_Z;
  } else if (lp_data->lp_ctx->K == lp_Z) {  // expecting not Z, but is Z
    return false;
  }
  return mpz_cmp(&lp_data->lp_ctx->K->M, order) == 0;
}

static
void lp_data_variable_link(lp_data_t *lp_data, lp_variable_t lp_var, int32_t var) {
  assert(int_hmap_find(&lp_data->lp_var_to_term_map, lp_var) == NULL);
  assert(int_hmap_find(&lp_data->term_to_lp_var_map, var) == NULL);

  int_hmap_add(&lp_data->lp_var_to_term_map, lp_var, var);
  int_hmap_add(&lp_data->term_to_lp_var_map, var, lp_var);
}

lp_variable_t lp_data_add_lp_variable(lp_data_t *lp_data, term_table_t *terms, term_t t) {
  assert(t != NULL_TERM && good_term_idx(terms, index_of(t)));
  assert(is_pos_term(t));
  // Name of the term
  char buffer[100];
  char* var_name = term_name(terms, t);
  if (var_name == NULL) {
    var_name = buffer;
    sprintf(var_name, "#%d", t);
  }

  // Make the variable
  lp_variable_t lp_var = lp_variable_db_new_variable(lp_data->lp_var_db, var_name);
  lp_data_variable_link(lp_data, lp_var, t);

  return lp_var;
}

void lp_data_variable_order_push(lp_data_t *lp_data) {
  scope_holder_push(&lp_data->scope,
                    &lp_data->lp_var_order_size,
                    NULL);
}

void lp_data_variable_order_pop(lp_data_t *lp_data) {
  scope_holder_pop(&lp_data->scope,
                   &lp_data->lp_var_order_size,
                   NULL);

  lp_variable_order_t* order = lp_data->lp_var_order;
  lp_assignment_t* assignment = lp_data->lp_assignment;
  while (lp_variable_order_size(order) > lp_data->lp_var_order_size) {
    lp_variable_t lp_var = lp_variable_order_top(order);
    lp_variable_order_pop(order);
    lp_assignment_set_value(assignment, lp_var, 0);
  }
}

void lp_data_add_to_model_and_context(lp_data_t *lp_data, lp_variable_t lp_var, const lp_value_t *lp_value) {
  lp_assignment_set_value(lp_data->lp_assignment, lp_var, lp_value);
  lp_variable_order_push(lp_data->lp_var_order, lp_var);
  lp_data->lp_var_order_size ++;
}

lp_variable_t lp_data_new_variable(const lp_data_t *lp_data, const char* var_name) {
  return lp_variable_db_new_variable(lp_data->lp_var_db, var_name);
}

lp_polynomial_t* lp_data_new_polynomial(const lp_data_t *lp_data) {
  return lp_polynomial_new(lp_data->lp_ctx);
}

void lp_data_variable_order_print(const lp_data_t *lp_data, FILE *file) {
  lp_variable_order_print(lp_data->lp_var_order, lp_data->lp_var_db, file);
}

const lp_int_ring_t* lp_data_get_ring(const lp_data_t *lp_data) {
  return lp_data->lp_ctx->K;
}

void lp_data_gc_sweep(lp_data_t *lp_data, const gc_info_t *gc_vars) {
  // - lp_data.lp_var_to_term_map (values)
  // - lp_data.term_to_lp_var_map (keys)
  // TODO keep terms that are associated with variables that are still in use.
//  gc_info_sweep_int_hmap_values(gc_vars, &lp_data->lp_var_to_term_map);
//  gc_info_sweep_int_hmap_keys(gc_vars, &lp_data->term_to_lp_var_map);
}
