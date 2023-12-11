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
 
#include "mcsat/nra/poly_constraint.h"
#include "mcsat/nra/libpoly_utils.h"
#include "terms/terms.h"
#include "mcsat/tracing.h"
#include "mcsat/utils/lp_data.h"

#include <poly/variable_db.h>
#include <poly/variable_list.h>
#include <poly/feasibility_set.h>
#include <poly/interval.h>
#include <poly/assignment.h>
#include <poly/polynomial_vector.h>

/**
 * A constraint of the form sgn(p(x)) = sgn_conition.
 */
struct poly_constraint_struct {

  /** The polynomial of the constraint */
  lp_polynomial_t* polynomial;

  /** The sign condition */
  lp_sign_condition_t sgn_condition;

  /** If this is a root constraint, this is the variable */
  lp_variable_t x;

  /** If this is a root constraint, this is the root index */
  size_t root_index;
};

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

/** Database of constraints */
struct poly_constraint_db_struct {
  /** The plugin */
  nra_plugin_t* nra;

  /** Vector of constraints */
  pvector_t constraints;

  /** Map from variables to constraint references */
  int_hmap_t var_to_constraint_map;

  /** List of all constraint variables */
  ivector_t all_constraint_variables;
};

void poly_constraint_db_gc_sweep(poly_constraint_db_t* db, const gc_info_t* gc_vars) {

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
      if (ctx_trace_enabled(db->nra->ctx, "nra::gc")) {
        ctx_trace_printf(db->nra->ctx, "Removing constraint :");
        poly_constraint_print(constraint, ctx_trace_out(db->nra->ctx));
        ctx_trace_printf(db->nra->ctx, "\n");
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

lp_sign_condition_t poly_constraint_get_sign_condition(const poly_constraint_t* cstr) {
  return cstr->sgn_condition;
}

const lp_polynomial_t* poly_constraint_get_polynomial(const poly_constraint_t* cstr) {
  return cstr->polynomial;
}

bool poly_constraint_is_root_constraint(const poly_constraint_t* cstr) {
  return cstr->x != lp_variable_null;
}

lp_variable_t poly_constraint_get_variable(const poly_constraint_t* cstr) {
  return cstr->x;
}

uint32_t poly_constraint_get_root_index(const poly_constraint_t* cstr) {
  return cstr->root_index;
}

lp_feasibility_set_t* poly_constraint_get_feasible_set(const poly_constraint_t* cstr, const lp_assignment_t* m, bool negated) {

  lp_feasibility_set_t* feasible  = 0;

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

bool poly_constraint_resolve_fm(const poly_constraint_t* c0, bool c0_negated, const poly_constraint_t* c1, bool c1_negated, nra_plugin_t* nra, ivector_t* out) {

  lp_polynomial_context_t* ctx = nra->lp_data.lp_ctx;
  lp_assignment_t* m = nra->lp_data.lp_assignment;

  if (poly_constraint_is_root_constraint(c0) || poly_constraint_is_root_constraint(c1)) {
    return false;
  }

  if (ctx_trace_enabled(nra->ctx, "mcsat::nra::explain")) {
    ctx_trace_printf(nra->ctx, "c0 %s: ", c0_negated ? "(negated)" : "");
    poly_constraint_print(c0, ctx_trace_out(nra->ctx));
    ctx_trace_printf(nra->ctx, "\n");
    ctx_trace_printf(nra->ctx, "c1 %s: ", c1_negated ? "(negated)" : "");
    poly_constraint_print(c1, ctx_trace_out(nra->ctx));
    ctx_trace_printf(nra->ctx, "\n");
  }

  lp_polynomial_vector_t* assumptions = lp_polynomial_vector_new(ctx);

  lp_sign_condition_t R_sgn_condition;
  lp_polynomial_t* R = lp_polynomial_new(ctx);
  lp_sign_condition_t c0_sgn_condition = c0_negated ? lp_sign_condition_negate(c0->sgn_condition) : c0->sgn_condition;
  lp_sign_condition_t c1_sgn_condition = c1_negated ? lp_sign_condition_negate(c1->sgn_condition) : c1->sgn_condition;
  bool ok = lp_polynomial_constraint_resolve_fm(c0->polynomial, c0_sgn_condition, c1->polynomial, c1_sgn_condition, m, R, &R_sgn_condition, assumptions);
  if (ok) {
    // (C1 && C2 && assumptions && !(p R2 0)) => false
    term_manager_t* tm = nra->ctx->tm;
    size_t n = lp_polynomial_vector_size(assumptions);
    size_t i;
    for (i = 0; i < n; ++ i) {
      lp_polynomial_t* assumption_p_i = lp_polynomial_vector_at(assumptions, i);
      term_t assumption_i_p_term = lp_polynomial_to_yices_term_nra(assumption_p_i, nra);
      int assumption_i_p_sgn = lp_polynomial_sgn(assumption_p_i, m);
      //      term_t assumption_i = NULL_TERM; // infer dead store
      term_t assumption_i;
      if (assumption_i_p_sgn < 0) {
        assumption_i = mk_arith_term_lt0(tm, assumption_i_p_term);
      } else if (assumption_i_p_sgn > 0) {
        assumption_i = mk_arith_term_gt0(tm, assumption_i_p_term);
      } else {
        assumption_i = mk_arith_term_eq0(tm, assumption_i_p_term);
      }
      if (ctx_trace_enabled(nra->ctx, "mcsat::nra::explain")) {
        ctx_trace_printf(nra->ctx, "adding FM assumption: ");
        ctx_trace_term(nra->ctx, assumption_i);
      }
      ivector_push(out, assumption_i);
      lp_polynomial_delete(assumption_p_i);
    }
    term_t R_p_term = lp_polynomial_to_yices_term_nra(R, nra);
    term_t R_term = NULL_TERM;
    switch (R_sgn_condition) {
    case LP_SGN_LT_0:
      R_term = mk_arith_term_lt0(tm, R_p_term);
      break;
    case LP_SGN_LE_0:
      R_term = mk_arith_term_leq0(tm, R_p_term);
      break;
    case LP_SGN_EQ_0:
      R_term = mk_arith_term_eq0(tm, R_p_term);
      break;
    case LP_SGN_NE_0:
      R_term = mk_arith_term_neq0(tm, R_p_term);
      break;
    case LP_SGN_GT_0:
      R_term = mk_arith_term_gt0(tm, R_p_term);
      break;
    case LP_SGN_GE_0:
      R_term = mk_arith_term_geq0(tm, R_p_term);
      break;
    }
    R_term = opposite_term(R_term);
    if (ctx_trace_enabled(nra->ctx, "mcsat::nra::explain")) {
      ctx_trace_printf(nra->ctx, "adding resolvent: ");
      ctx_trace_term(nra->ctx, R_term);
    }
    ivector_push(out, R_term);
  }

  lp_polynomial_delete(R);
  lp_polynomial_vector_delete(assumptions);

  return ok;
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

lp_variable_t poly_constraint_get_top_variable(const poly_constraint_t* cstr) {
  return lp_polynomial_top_variable(cstr->polynomial);
}

void poly_constraint_db_construct(poly_constraint_db_t* db, nra_plugin_t* nra) {
  db->nra = nra;

  init_pvector(&db->constraints, 0);
  init_int_hmap(&db->var_to_constraint_map, 0);
  init_ivector(&db->all_constraint_variables, 0);
}

poly_constraint_db_t* poly_constraint_db_new(nra_plugin_t* nra) {
  poly_constraint_db_t* db;
  db = safe_malloc(sizeof(poly_constraint_db_t));
  poly_constraint_db_construct(db, nra);
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

const ivector_t* poly_constraint_db_get_constraints(const poly_constraint_db_t* db) {
  return &db->all_constraint_variables;
}


bool poly_constraint_db_check(const poly_constraint_db_t* db) {
  uint32_t i;
  for (i = 0; i < db->constraints.size; ++ i) {
    if (!poly_constraint_ok(db->constraints.data[i])) {
      return false;
    }
  }
  return true;
}

const poly_constraint_t* poly_constraint_db_get(poly_constraint_db_t* db, variable_t constraint_var) {

  // assert(poly_constraint_db_check(db));
  int_hmap_pair_t* find;
  find = int_hmap_find(&db->var_to_constraint_map, constraint_var);
  assert(find != NULL);
  assert(find->val < db->constraints.size);
  poly_constraint_t* constraint = db->constraints.data[find->val];
  // assert(poly_constraint_ok(constraint));
  // assert(poly_constraint_db_check(db));
  return constraint;
}

void poly_constraint_db_add(poly_constraint_db_t* db, variable_t constraint_var) {
  // assert(poly_constraint_db_check(db));

  if (int_hmap_find(&db->var_to_constraint_map, constraint_var) != NULL) {
    // Already added
    return;
  }

  term_t t1, t2;
  term_kind_t kind;
  term_t constraint_var_term;

  // Constraint components
  lp_polynomial_t* cstr_polynomial = 0;
  lp_variable_t cstr_root_variable = lp_variable_null;
  uint32_t cstr_root_index = 0;
  lp_sign_condition_t sgn_condition;

  // Result constraint
  poly_constraint_t* cstr;

  // Context
  variable_db_t* var_db = db->nra->ctx->var_db;
  term_table_t* terms = db->nra->ctx->terms;

  // Get the term of the variable
  constraint_var_term = variable_db_get_term(var_db, constraint_var);

  // Depending on the kind, make the constraints
  kind = term_kind(terms, constraint_var_term);
  switch (kind) {
  case ARITH_EQ_ATOM: {
    // p == 0
    t1 = arith_atom_arg(terms, constraint_var_term);
    cstr_polynomial = lp_polynomial_from_term_nra(db->nra, t1, NULL);
    sgn_condition = LP_SGN_EQ_0;
    break;
  }
  case ARITH_GE_ATOM:
    // p >= 0
    t1 = arith_atom_arg(terms, constraint_var_term);
    cstr_polynomial = lp_polynomial_from_term_nra(db->nra, t1, NULL);
    sgn_condition = LP_SGN_GE_0;
    break;
  case EQ_TERM:
  case ARITH_BINEQ_ATOM: {
    // LHS = RHS
    t1 = composite_term_arg(terms, constraint_var_term, 0);
    t2 = composite_term_arg(terms, constraint_var_term, 1);
    // Get the polynomials
    lp_integer_t t1_c, t2_c;
    lp_integer_construct(&t1_c);
    lp_integer_construct(&t2_c);
    lp_polynomial_t* t1_p = lp_polynomial_from_term_nra(db->nra, t1, &t1_c);
    lp_polynomial_t* t2_p = lp_polynomial_from_term_nra(db->nra, t2, &t2_c);
    //  t1_p/t1_c = t2_p/t2_c
    //  t1_p*t2_c - t2_p*t1_c
    lp_integer_neg(lp_Z, &t1_c, &t1_c);
    lp_polynomial_mul_integer(t1_p, t1_p, &t2_c);
    lp_polynomial_mul_integer(t2_p, t2_p, &t1_c);
    // Add them
    cstr_polynomial = lp_polynomial_new(db->nra->lp_data.lp_ctx);
    lp_polynomial_add(cstr_polynomial, t1_p, t2_p);
    // p1 = p2
    sgn_condition = LP_SGN_EQ_0;
    // Remove temps
    lp_polynomial_delete(t1_p);
    lp_polynomial_delete(t2_p);
    lp_integer_destruct(&t1_c);
    lp_integer_destruct(&t2_c);
    break;
  }
  case ARITH_ROOT_ATOM: {
    root_atom_t* r = arith_root_atom_desc(terms, constraint_var_term);
    cstr_polynomial = lp_polynomial_from_term_nra(db->nra, r->p, NULL);
    variable_t x = variable_db_get_variable_if_exists(db->nra->ctx->var_db, r->x);
    assert(x != variable_null);
    cstr_root_variable = lp_data_get_lp_variable(&db->nra->lp_data, x);
    cstr_root_index = r->k;
    switch (r->r) {
    case ROOT_ATOM_LT:
      sgn_condition = LP_SGN_LT_0;
      break;
    case ROOT_ATOM_LEQ:
      sgn_condition = LP_SGN_LE_0;
      break;
    case ROOT_ATOM_EQ:
      sgn_condition = LP_SGN_EQ_0;
      break;
    case ROOT_ATOM_NEQ:
      sgn_condition = LP_SGN_NE_0;
      break;
    case ROOT_ATOM_GEQ:
      sgn_condition = LP_SGN_GE_0;
      break;
    case ROOT_ATOM_GT:
      sgn_condition = LP_SGN_GT_0;
      break;
    default:
      sgn_condition = LP_SGN_EQ_0;
      assert(false);
      break;
    }
    break;
  }
  default: {
    // terms like (x+y), we create regular constraint (x+y) = x + y
    lp_integer_t t1_c, t2_c;
    lp_integer_construct_from_int(lp_Z, &t1_c, 1);
    lp_integer_construct(&t2_c);
    lp_polynomial_t* t1_p = lp_polynomial_alloc();
    lp_variable_t constraint_lp_var = lp_data_get_lp_variable(&db->nra->lp_data, constraint_var);
    lp_polynomial_construct_simple(t1_p, db->nra->lp_data.lp_ctx, &t1_c, constraint_lp_var, 1);
    lp_polynomial_t* t2_p = lp_polynomial_from_term_nra(db->nra, constraint_var_term, &t2_c);
    //  t1_p/t1_c = t2_p/t2_c
    //  t1_p*t2_c - t2_p*t1_c
    lp_integer_neg(lp_Z, &t1_c, &t1_c);
    lp_polynomial_mul_integer(t2_p, t2_p, &t1_c);
    lp_polynomial_mul_integer(t1_p, t1_p, &t2_c);
    // Add them
    cstr_polynomial = lp_polynomial_new(db->nra->lp_data.lp_ctx);
    lp_polynomial_add(cstr_polynomial, t1_p, t2_p);
    // p1 = p2
    sgn_condition = LP_SGN_EQ_0;
    // Remove temps
    lp_polynomial_delete(t1_p);
    lp_polynomial_delete(t2_p);
    lp_integer_destruct(&t1_c);
    lp_integer_destruct(&t2_c);

    break;
  }
  }

  // Id of the new constraint
  uint32_t index = db->constraints.size;

  // Create the appropriate constraint
  if (cstr_root_variable == lp_variable_null) {
    cstr = poly_constraint_new_regular(cstr_polynomial, sgn_condition);
    (*db->nra->stats.constraint_regular) ++;
  } else {
    cstr = poly_constraint_new_root(cstr_polynomial, sgn_condition, cstr_root_variable, cstr_root_index);
    (*db->nra->stats.constraint_root) ++;
  }


  if (ctx_trace_enabled(db->nra->ctx, "mcsat::new_term")) {
    ctx_trace_printf(db->nra->ctx, "poly_constraint_add: ");
    poly_constraint_print(cstr, ctx_trace_out(db->nra->ctx));
    ctx_trace_printf(db->nra->ctx, "\n");
  }

  assert(poly_constraint_ok(cstr));

  // Add the constraint
  pvector_push(&db->constraints, cstr);
  int_hmap_add(&db->var_to_constraint_map, constraint_var, index);
  ivector_push(&db->all_constraint_variables, constraint_var);

  // assert(poly_constraint_db_check(db));
}

bool poly_constraint_is_valid(const poly_constraint_t* cstr) {
  // Evaluate
  if (poly_constraint_is_root_constraint(cstr)) {
    return (cstr->x == lp_polynomial_top_variable(cstr->polynomial));
  } else {
    return true;
  }
}

bool poly_constraint_evaluate(const poly_constraint_t* cstr, nra_plugin_t* nra, bool* value_out) {

  assert(poly_constraint_ok(cstr));

  // Evaluate
  if (poly_constraint_is_root_constraint(cstr)) {
    if (cstr->x != lp_polynomial_top_variable(cstr->polynomial)) {
      // if not top, ignore
      return false;
    } else {
      *value_out = lp_polynomial_root_constraint_evaluate(cstr->polynomial, cstr->root_index, cstr->sgn_condition, nra->lp_data.lp_assignment);
    }
  } else {
    *value_out = lp_polynomial_constraint_evaluate(cstr->polynomial, cstr->sgn_condition, nra->lp_data.lp_assignment);
  }

  return true;
}

const mcsat_value_t* poly_constraint_db_approximate(poly_constraint_db_t* db, variable_t constraint_var, nra_plugin_t* nra) {
  const mcsat_value_t* result = NULL;

  // Get the constraints
  const poly_constraint_t* cstr = poly_constraint_db_get(db, constraint_var);
  if (poly_constraint_is_root_constraint(cstr)) {
    // TODO: check if possible
    return NULL;
  }

  // Reset the interval assignment
  lp_interval_assignment_t* m = nra->lp_data.lp_interval_assignment;
  lp_interval_assignment_reset(m);

  // Setup the assignment x -> I(x)
  assert(watch_list_manager_has_constraint(&nra->wlm, constraint_var));
  variable_list_ref_t var_list_ref = watch_list_manager_get_list_of(&nra->wlm, constraint_var);
  variable_t* vars = watch_list_manager_get_list(&nra->wlm, var_list_ref);
  for (; *vars != variable_null; vars++) {
    variable_t x = *vars;
    lp_variable_t x_lp = lp_data_get_lp_variable(&nra->lp_data, x);
    lp_interval_t x_interval;
    lp_interval_construct_full(&x_interval);
    feasible_set_db_approximate_value(nra->feasible_set_db, x, &x_interval);
    if (ctx_trace_enabled(nra->ctx, "mcsat::nra::learn")) {
      ctx_trace_printf(db->nra->ctx, " ");
      ctx_trace_term(db->nra->ctx, variable_db_get_term(db->nra->ctx->var_db, x));
      ctx_trace_printf(db->nra->ctx, " ");
      lp_interval_print(&x_interval, ctx_trace_out(db->nra->ctx));
      ctx_trace_printf(db->nra->ctx, "\n");
    }
    lp_interval_assignment_set_interval(m, x_lp, &x_interval);
    lp_interval_destruct(&x_interval);
  }

  // Evaluate the polynomial
  lp_interval_t value;
  lp_interval_construct_full(&value);
  lp_polynomial_interval_value(cstr->polynomial, m, &value);
  if (ctx_trace_enabled(nra->ctx, "mcsat::nra::learn")) {
    poly_constraint_print(cstr, ctx_trace_out(db->nra->ctx));
    ctx_trace_printf(db->nra->ctx, " -> ");
    lp_interval_print(&value, ctx_trace_out(db->nra->ctx));
    ctx_trace_printf(db->nra->ctx, "\n");
  }

  lp_sign_condition_t pos = cstr->sgn_condition;
  lp_sign_condition_t neg = lp_sign_condition_negate(cstr->sgn_condition);

  if (lp_sign_condition_consistent_interval(pos, &value)) {
    result = &mcsat_value_true;
  } else if (lp_sign_condition_consistent_interval(neg, &value)) {
    result = &mcsat_value_false;
  }

  // Remove temps
  lp_interval_destruct(&value);

  return result;
}
