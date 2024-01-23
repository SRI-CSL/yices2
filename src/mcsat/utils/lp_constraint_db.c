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

#include "lp_constraint_db.h"

#include <poly/polynomial.h>
#include <poly/variable_db.h>
#include <poly/variable_list.h>
#include <poly/feasibility_set.h>

#include "mcsat/tracing.h"

static
bool poly_constraint_ok(const poly_constraint_t* cstr) {
  switch (cstr->sgn_condition) {
  case LP_SGN_LT_0:
  case LP_SGN_LE_0:
  case LP_SGN_EQ_0:
  case LP_SGN_NE_0:
  case LP_SGN_GT_0:
  case LP_SGN_GE_0:
    break;
  default:
    return false;
  }
  return lp_polynomial_check_integrity(cstr->polynomial);;
}

static
bool poly_constraint_db_check(const poly_constraint_db_t* db) {
  uint32_t i;
  for (i = 0; i < db->constraints.size; ++ i) {
    if (!poly_constraint_ok(db->constraints.data[i])) {
      return false;
    }
  }
  return true;
}

void poly_constraint_db_construct(poly_constraint_db_t* db, lp_data_t* lp_data) {
  db->lp_data = lp_data;

  init_pvector(&db->constraints, 0);
  init_int_hmap(&db->var_to_constraint_map, 0);
  init_ivector(&db->all_constraint_variables, 0);
}

poly_constraint_db_t* poly_constraint_db_new(lp_data_t* lp_data) {
  poly_constraint_db_t* db;
  db = safe_malloc(sizeof(poly_constraint_db_t));
  poly_constraint_db_construct(db, lp_data);
  return db;
}

void poly_constraint_db_destruct(poly_constraint_db_t* db) {
  uint32_t i;
  poly_constraint_t* cstr;

  for (i = 0; i < db->constraints.size; i ++) {
    cstr = db->constraints.data[i];
    poly_constraint_delete(cstr);
  }

  delete_pvector(&db->constraints);
  delete_int_hmap(&db->var_to_constraint_map);
  delete_ivector(&db->all_constraint_variables);
}

void poly_constraint_db_delete(poly_constraint_db_t* db) {
  poly_constraint_db_destruct(db);
  safe_free(db);
}

void poly_constraint_construct_regular(poly_constraint_t* cstr, lp_polynomial_t* p, lp_sign_condition_t sgn_contition) {
  cstr->polynomial = p;
  cstr->sgn_condition = sgn_contition;
  cstr->x = lp_variable_null;
  cstr->root_index = 0;
}

void poly_constraint_construct_root(poly_constraint_t* cstr, lp_polynomial_t* p, lp_sign_condition_t sgn_contition, lp_variable_t x, uint32_t root_index) {
  cstr->polynomial = p;
  cstr->sgn_condition = sgn_contition;
  cstr->x = x;
  cstr->root_index = root_index;
}

poly_constraint_t* poly_constraint_new_regular(lp_polynomial_t* p, lp_sign_condition_t sgn_contition) {
  poly_constraint_t* cstr = safe_malloc(sizeof(poly_constraint_t));
  poly_constraint_construct_regular(cstr, p, sgn_contition);
  lp_polynomial_set_external(p);
  return cstr;
}

poly_constraint_t* poly_constraint_new_root(lp_polynomial_t* p, lp_sign_condition_t sgn_contition, lp_variable_t x, uint32_t root_index) {
  poly_constraint_t* cstr = safe_malloc(sizeof(poly_constraint_t));
  poly_constraint_construct_root(cstr, p, sgn_contition, x, root_index);
  lp_polynomial_set_external(p);
  return cstr;
}

void poly_constraint_destruct(poly_constraint_t* cstr) {
  lp_polynomial_delete(cstr->polynomial);
}

void poly_constraint_delete(poly_constraint_t* cstr) {
  poly_constraint_destruct(cstr);
  safe_free(cstr);
}

void poly_constraint_db_add_constraint(poly_constraint_db_t* db, variable_t constraint_var, poly_constraint_t* cstr) {
  assert(poly_constraint_ok(cstr));

  // id of the new constraint
  uint32_t index = db->constraints.size;
  // add the constraint
  pvector_push(&db->constraints, cstr);
  int_hmap_add(&db->var_to_constraint_map, constraint_var, index);
  ivector_push(&db->all_constraint_variables, constraint_var);
}

static
void mathematica_print_traverse(const lp_polynomial_context_t* ctx, lp_monomial_t* m, void* data) {
  FILE* out = data;

  fprintf(out, "(");
  lp_integer_print(&m->a, out);
  uint32_t i = 0;
  for (i = 0; i < m->n; ++ i) {
    fprintf(out, "*x%zu^%zu", m->p[i].x, m->p[i].d);
  }
  fprintf(out, ") + ");
}

void poly_constraint_print_mathematica(const poly_constraint_t* cstr, bool negated, FILE* out) {

  if (poly_constraint_is_root_constraint(cstr)) {
    fprintf(out, "(x%zu - ", cstr->x);
    fprintf(out, "Root[");
    lp_polynomial_traverse(cstr->polynomial, mathematica_print_traverse, out);
    fprintf(out, "0, %zu]", cstr->root_index);
    lp_sign_condition_print(cstr->sgn_condition, out);
    fprintf(out, ")");
  } else {
    fprintf(out, "(");
    lp_polynomial_traverse(cstr->polynomial, mathematica_print_traverse, out);
    fprintf(out, "0 ");
    lp_sign_condition_t sgn_condition = cstr->sgn_condition;
    if (negated) {
      sgn_condition = lp_sign_condition_negate(sgn_condition);
    }
    lp_sign_condition_print(sgn_condition, out);
    fprintf(out, ")");
  }
}

void poly_constraint_print(const poly_constraint_t* cstr, FILE* out) {

  const lp_polynomial_context_t* ctx = lp_polynomial_get_context(cstr->polynomial);

  if (poly_constraint_is_root_constraint(cstr)) {
    fprintf(out, "(%s - ", lp_variable_db_get_name(ctx->var_db, cstr->x));
    fprintf(out, "root(%zu, ", cstr->root_index);
    lp_polynomial_print(cstr->polynomial, out);
    fprintf(out, ") ");
    lp_sign_condition_print(cstr->sgn_condition, out);
    fprintf(out, ")");
  } else {
    fprintf(out, "(");
    lp_sign_condition_print(cstr->sgn_condition, out);
    fprintf(out, " (");
    lp_polynomial_print(cstr->polynomial, out);
    fprintf(out, ") 0)");
  }
}

bool poly_constraint_evaluate(const poly_constraint_t* cstr, lp_data_t *lp_data, bool* value_out) {

  assert(poly_constraint_ok(cstr));

  // Evaluate
  if (poly_constraint_is_root_constraint(cstr)) {
    if (cstr->x != lp_polynomial_top_variable(cstr->polynomial)) {
      // if not top, ignore
      return false;
    } else {
      *value_out = lp_polynomial_root_constraint_evaluate(cstr->polynomial, cstr->root_index, cstr->sgn_condition, lp_data->lp_assignment);
    }
  } else {
    *value_out = lp_polynomial_constraint_evaluate(cstr->polynomial, cstr->sgn_condition, lp_data->lp_assignment);
  }

  return true;
}

lp_feasibility_set_t* poly_constraint_get_feasible_set(const poly_constraint_t* cstr, const lp_assignment_t* m, bool negated) {

  lp_feasibility_set_t* feasible = NULL;

  if (poly_constraint_is_root_constraint(cstr)) {
    // Get the root constraint feasible set
    if (cstr->x != lp_polynomial_top_variable(cstr->polynomial)) {
      // x not top => constraint ignored
      feasible = lp_feasibility_set_new_full();
    } else {
      feasible = lp_polynomial_root_constraint_get_feasible_set(cstr->polynomial, cstr->root_index, cstr->sgn_condition, negated, m);
    }
  } else {
    // Get the polynomial feasible set
    feasible = lp_polynomial_constraint_get_feasible_set(cstr->polynomial, cstr->sgn_condition, negated, m);
  }

  return feasible;
}

bool poly_constraint_infer_bounds(const poly_constraint_t* cstr, bool negated, lp_interval_assignment_t* m, ivector_t* inferred_vars) {

  // TODO: is it possible to support root constraints
  if (poly_constraint_is_root_constraint(cstr)) {
    return false;
  }

  // Infer some bounds
  int inference_result = lp_polynomial_constraint_infer_bounds(cstr->polynomial, cstr->sgn_condition, negated, m);
  if (inference_result == 0) {
    return false;
  }
  if (inference_result == -1) {
    return true;
  }

  lp_variable_list_t vars;
  lp_variable_list_construct(&vars);
  lp_polynomial_get_variables(cstr->polynomial, &vars);
  uint32_t var_i;
  for (var_i = 0; var_i < vars.list_size; ++ var_i) {
    lp_variable_t x_lp = vars.list[var_i];
    const lp_interval_t* x_interval = lp_interval_assignment_get_interval(m, x_lp);
    if (x_interval != NULL) {
      // something is inferred
      ivector_push(inferred_vars, x_lp);
    }
  }
  lp_variable_list_destruct(&vars);

  return false;
}

lp_variable_t poly_constraint_get_top_variable(const poly_constraint_t* cstr) {
  return lp_polynomial_top_variable(cstr->polynomial);
}

bool poly_constraint_is_valid(const poly_constraint_t* cstr) {
  // Evaluate
  if (poly_constraint_is_root_constraint(cstr)) {
    return (cstr->x == lp_polynomial_top_variable(cstr->polynomial));
  } else {
    return true;
  }
}

bool poly_constraint_is_unit(const poly_constraint_t* cstr, const lp_assignment_t* M) {
  lp_variable_t x = lp_polynomial_top_variable(cstr->polynomial);
  if (lp_assignment_get_value(M, x)->type != LP_VALUE_NONE) {
    return false;
  }

  bool result = true;

  lp_variable_list_t vars;
  lp_variable_list_construct(&vars);
  lp_polynomial_get_variables(cstr->polynomial, &vars);
  uint32_t var_i;
  for (var_i = 0; var_i < vars.list_size; ++ var_i) {
    lp_variable_t x_lp = vars.list[var_i];
    if (x_lp != x && lp_assignment_get_value(M, x_lp)->type == LP_VALUE_NONE) {
      result = false;
      break;
    }
  }
  lp_variable_list_destruct(&vars);

  return result;
}

bool poly_constraint_db_has(poly_constraint_db_t* db, variable_t constraint_var) {
  return int_hmap_find(&db->var_to_constraint_map, constraint_var) != NULL;
}

const poly_constraint_t* poly_constraint_db_get(poly_constraint_db_t* db, variable_t constraint_var) {
  assert(poly_constraint_db_check(db));
  int_hmap_pair_t* find;
  find = int_hmap_find(&db->var_to_constraint_map, constraint_var);
  assert(find != NULL);
  assert(find->val < db->constraints.size);
  poly_constraint_t* constraint = db->constraints.data[find->val];
  assert(poly_constraint_ok(constraint));
  assert(poly_constraint_db_check(db));
  return constraint;
}

void poly_constraint_db_gc_sweep(poly_constraint_db_t* db, plugin_context_t* ctx, const gc_info_t* gc_vars) {

  pvector_t new_constraints;
  int_hmap_t new_var_to_constraint_map;

  init_pvector(&new_constraints, 0);
  init_int_hmap(&new_var_to_constraint_map, 0);

  // Move the constraints
  uint32_t i, to_keep = 0;
  for (i = 0; i < db->all_constraint_variables.size; ++ i) {
    variable_t old_constraint_var = db->all_constraint_variables.data[i];
    int_hmap_pair_t* it = int_hmap_find(&db->var_to_constraint_map, old_constraint_var);
    // Do we keep it
    variable_t new_constraint_var = gc_info_get_reloc(gc_vars, old_constraint_var);
    poly_constraint_t* constraint = db->constraints.data[it->val];
    if (new_constraint_var != gc_vars->null_value) {
      // Move it
      uint32_t new_index = new_constraints.size;
      pvector_push(&new_constraints, constraint);
      int_hmap_add(&new_var_to_constraint_map, new_constraint_var, new_index);
      db->all_constraint_variables.data[to_keep ++] = new_constraint_var;
    } else {
      if (ctx_trace_enabled(ctx, "lp::gc")) {
        ctx_trace_printf(ctx, "Removing constraint :");
        poly_constraint_print(constraint, ctx_trace_out(ctx));
        ctx_trace_printf(ctx, "\n");
      }
      // Delete it
      poly_constraint_delete(constraint);
    }
  }

  // Destroy and swap in the new ones
  delete_pvector(&db->constraints);
  delete_int_hmap(&db->var_to_constraint_map);
  db->constraints = new_constraints;
  db->var_to_constraint_map = new_var_to_constraint_map;
  ivector_shrink(&db->all_constraint_variables, to_keep);
}
