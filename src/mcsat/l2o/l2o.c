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

#include "mcsat/l2o/l2o.h"
#include "mcsat/l2o/l2o_internal.h"
#include "mcsat/bool/bool_plugin.h"

#include "terms/term_explorer.h"
#include "utils/int_array_sort2.h"

#include <math.h>
#include <poly/feasibility_set.h>

static
void l2o_stats_init(l2o_t* l2o) {
  l2o->l2o_stats.n_runs = statistics_new_int(&l2o->stats, "l2o::runs");
  l2o->l2o_stats.n_terms = statistics_new_int(&l2o->stats, "l2o::terms");
  l2o->l2o_stats.n_eval_runs = statistics_new_int(&l2o->stats, "l2o::eval_runs");
}

void l2o_construct(l2o_t* l2o, term_table_t* terms, jmp_buf* handler, plugin_t* nra, plugin_t* bool_plugin) {
  l2o->terms = terms;
  l2o->nra = nra;
  l2o->bool_plugin = bool_plugin;
  init_ivector(&l2o->assertions, 0);

  init_int_hmmap(&l2o->var_member, 0);

  l2o->tracer = NULL;
  l2o->exception = handler;
  scope_holder_construct(&l2o->scope);

  statistics_construct(&l2o->stats);
  l2o_stats_init(l2o);
}

void l2o_set_tracer(l2o_t* l2o, tracer_t* tracer) {
  l2o->tracer = tracer;
}

void l2o_destruct(l2o_t* l2o) {
  delete_ivector(&l2o->assertions);
  delete_int_hmmap(&l2o->var_member);
  scope_holder_destruct(&l2o->scope);
  statistics_destruct(&l2o->stats);
}

void l2o_store_assertion(l2o_t* l2o, term_t assertion) {
  ivector_push(&l2o->assertions, assertion);
}

/** Checks whether the intersection between set_of_vars and the free variables in t is empty (0) or not (1) */
bool l2o_term_has_variables(l2o_t *l2o, term_t t, const ivector_t *set_of_vars) {
  term_t t_pos = unsigned_term(t);
  for (uint32_t i = 0; i < set_of_vars->size; ++i) {
    term_t t_var = set_of_vars->data[i];
    assert(is_pos_term(t_var));
    if (int_hmmap_contains(&l2o->var_member, t_pos, t_var)) {
      return true;
    }
  }
  return false;
}

static
void collect_free_vars(l2o_t *l2o, term_t t, ivector_t *v, uint32_t offset) {
  term_t current_term = unsigned_term(t);

  if(int_hmmap_find_all(&l2o->var_member, current_term, v) > 0) {
    // If already visited, continue
    return;
  }

  if(t == RESERVED_TERM || t == UNUSED_TERM) {
    return;
  }

  term_kind_t current_kind = term_kind(l2o->terms, current_term);

  if (current_kind == UNINTERPRETED_TERM) {
    // found a variable
    ivector_push(v, current_term);
    int_hmmap_add(&l2o->var_member, current_term, current_term);
    return;
  }

  ivector_t subterms;
  init_ivector(&subterms, 0);

  switch (current_kind) {
    case CONSTANT_TERM:
    case ARITH_CONSTANT:
    case BV64_CONSTANT:
    case BV_CONSTANT:
      break;

    case ARITH_POLY: {
      polynomial_t *poly_desc = poly_term_desc(l2o->terms, current_term);
      for (uint32_t i = 0; i < poly_desc->nterms; ++i) {
        term_t var = poly_desc->mono[i].var;
        if (var > 0) ivector_push(&subterms, var);
      }
      break;
    }

    case BV64_POLY: {
      bvpoly64_t *poly_desc = bvpoly64_term_desc(l2o->terms, current_term);
      for (uint32_t i = 0; i < poly_desc->nterms; ++i) {
        term_t var = poly_desc->mono[i].var;
        if (var > 0) ivector_push(&subterms, var);
      }
      break;
    }

    case BV_POLY: {
      bvpoly_t *poly_desc = bvpoly_term_desc(l2o->terms, current_term);
      for (uint32_t i = 0; i < poly_desc->nterms; ++i) {
        term_t var = poly_desc->mono[i].var;
        if (var > 0) ivector_push(&subterms, var);
      }
      break;
    }

    case POWER_PRODUCT: {
      pprod_t* ppdesc = pprod_term_desc(l2o->terms, current_term);
      for (uint32_t i = 0; i < ppdesc->len; ++ i) {
        term_t var = ppdesc->prod[i].var;
        assert(var != RESERVED_TERM);
        if (var > 0) ivector_push(&subterms, var);
      }
      break;
    }

    default: {
      composite_term_t *c = get_composite(l2o->terms, current_kind, current_term);
      for (int i = 0; i < c->arity; ++i) {
        term_t arg = c->arg[i];
        ivector_push(&subterms, arg);
      }
      break;
    }
  }

  // handle subterms
  for (uint32_t i = 0; i < subterms.size; ++i) {
    term_t arg = subterms.data[i];
    assert(good_term(l2o->terms, arg));
    collect_free_vars(l2o, arg, v, v->size);
  }
  delete_ivector(&subterms);

  // associates the term its variables
  assert(offset <= v->size);
  assert(!int_hmmap_contains_key(&l2o->var_member, current_term));
  for (uint32_t i = offset; i < v->size; ++i) {
    term_t var = v->data[i];
    assert(is_pos_term(var));
    assert(is_pos_term(current_term));
    // TODO sort and remove duplicates from v and use add
    int_hmmap_insert(&l2o->var_member, current_term, var);
  }
}

/**
 * Calculates the l2o value of a given term. The term must be fully evaluated in the evaluator.
 */
#define L2O_TRUE 0.0
#define L2O_FALSE 1.0
#define L2O_EPSILON 0.0000001

double l2o_calculate(l2o_t *l2o, term_t t, l2o_evaluator_t *eval) {
  term_table_t *terms = l2o->terms;
  term_kind_t kind = term_kind(l2o->terms, t);
  type_kind_t t_type = term_type_kind(terms, t);
  term_t tu = unsigned_term(t);

  switch (kind) {
    case CONSTANT_TERM:
      if (t == true_term) return L2O_TRUE;
      if (t == false_term) return L2O_FALSE;
      assert(false);
      break;

    case UNINTERPRETED_TERM:
      double val = l2o_evaluator_run_term(eval, t);
      if (t_type == BOOL_TYPE) {
        assert(val == 1.0 || val == 0.0);
        return (val == 1.0 ? L2O_TRUE : L2O_FALSE);
      } else if(t_type == INT_TYPE || t_type == REAL_TYPE) {
        return val;
      } else {
        assert(false);
      }
      break;

    case ARITH_CONSTANT:
    case ARITH_FLOOR:
    case ARITH_CEIL:
    case ARITH_ABS:
    case ARITH_RDIV:
    case ARITH_IDIV:
    case ARITH_MOD:
    case POWER_PRODUCT:
    case ARITH_POLY:
      assert(tu == t);
      assert(t_type == INT_TYPE || t_type == REAL_TYPE);
      return l2o_evaluator_run_term(eval, tu);

    case ARITH_EQ_ATOM: {
      term_t t1 = arith_eq_arg(terms, t);
      double x = l2o_evaluator_run_term(eval, t1);

      if (is_pos_term(t)) { // x == 0
        return fabs(x);
      } else { // x != 0
        return x != 0.0 ? L2O_TRUE : L2O_FALSE;
      }
    }

    case ARITH_GE_ATOM: {
      term_t t1 = arith_ge_arg(terms, t);
      double x = l2o_evaluator_run_term(eval, t1);

      if (is_pos_term(t)) { // x >= 0
        return x >= 0 ? 0 : fabs(x);
      } else { // x < 0
        return x < 0 ? 0 : fabs(x) + L2O_EPSILON;
      }
    }

    case ITE_TERM:
    case ITE_SPECIAL: {
      composite_term_t *desc = ite_term_desc(terms, t);
      assert(desc->arity == 3);
      term_t tc = desc->arg[0];
      assert(term_type_kind(l2o->terms, tc) == BOOL_TYPE);
      double cond_val = l2o_evaluator_run_term(eval, tc);
      assert(cond_val == 1.0 || cond_val == 0.0);
      term_t tv = (cond_val == 1.0 ? desc->arg[1] : desc->arg[2]);
      assert(!is_neg_term(t) || term_type_kind(l2o->terms, tv) == BOOL_TYPE);
      return l2o_calculate(l2o, is_neg_term(t) ? opposite_term(tv) : tv, eval);
    }

    case OR_TERM: {
      composite_term_t *desc = or_term_desc(terms, t);
      uint32_t n = desc->arity;
      double result;
      if (is_pos_term(t)) { // or term
        result = 1.0;
        for (int i = 0; i < n; ++i) {
          term_t tv = desc->arg[i];
          result *= l2o_calculate(l2o, tv, eval);
          if (result == 0.0) break;
        }
      } else { // and term
        result = 0.0;
        for (int i = 0; i < n; ++i) {
          term_t tv = desc->arg[i];
          result += l2o_calculate(l2o, opposite_term(tv), eval);
        }
      }
      return result;
    }

    case EQ_TERM: {
      composite_term_t *desc = get_composite(terms, kind, unsigned_term(t));
      assert(desc->arity == 2);
      term_t t1 = desc->arg[0];
      term_t t2 = desc->arg[1];

      if (is_pos_term(t)) { // t1 == t2
        double val1 = l2o_calculate(l2o, t1, eval);
        double val2 = l2o_calculate(l2o, t2, eval);
        return fabs(val1 - val2);
      } else { // t1 != t2
        double val1 = l2o_evaluator_run_term(eval, t1);
        double val2 = l2o_evaluator_run_term(eval, t2);
        return val1 != val2 ? L2O_TRUE : L2O_FALSE;
      }
    }

    case ARITH_BINEQ_ATOM: {
      composite_term_t *desc = get_composite(terms, kind, unsigned_term(t));
      assert(desc->arity == 2);

      term_t t1 = desc->arg[0];
      term_t t2 = desc->arg[1];
      double val1 = l2o_evaluator_run_term(eval, t1);
      double val2 = l2o_evaluator_run_term(eval, t2);

      if (is_pos_term(t)) { // t1 == t2
        return fabs(val1 - val2);
      } else { // t1 != t2
        return val1 != val2 ? L2O_TRUE : L2O_FALSE;
      }
    }

    default:
    case ARITH_ROOT_ATOM:
    case XOR_TERM:
      assert(false);
      break;
  }
}

/** Returns true if its a valid term. */
static
bool l2o_collect_free_vars(l2o_t* l2o, term_t t) {
  ivector_t v;
  init_ivector(&v, 0);
  collect_free_vars(l2o, t, &v, 0);
  delete_ivector(&v);
  return l2o_is_valid_term(l2o, t);
}

/** Returns true if all terms are valid. */
static
bool l2o_collect_free_vars_list(l2o_t *l2o, ivector_t *lits) {
  bool result = true;
  ivector_t v;
  init_ivector(&v, 0);
  for (uint32_t i = 0; i < lits->size; ++i) {
    term_t t = lits->data[i];
    collect_free_vars(l2o, t, &v, 0);
    ivector_reset(&v);
    result = result && l2o_is_valid_term(l2o, t);
  }
  delete_ivector(&v);
  return result;
}

void l2o_set_exception_handler(l2o_t* l2o, jmp_buf* handler) {
  l2o->exception = handler;
}

/*
 * Provide a hint to the trail cache
 */
static
void hint_value_to_trail(mcsat_trail_t* trail, variable_t v, const mcsat_value_t* val) {
  //mcsat_plugin_context_t* mctx;
  //mctx = (mcsat_plugin_context_t*) self;
  variable_t var = variable_db_get_variable_if_exists(trail->var_db, v);
  assert (var != variable_null);

  // update only if var has no value in the trail
  if(! trail_has_value(trail, var) ){
    mcsat_model_set_value(&trail->model, var, val);
  }
}

static
double mcsat_value_to_double(const mcsat_value_t* val){
  mcsat_value_type_t type = val->type;
  switch (type) {
  case VALUE_BOOLEAN:
    return val->b;

  case VALUE_RATIONAL: {
    rational_t r = val->q;
    return q_get_double(&r);
  }

  case VALUE_LIBPOLY: {
    const lp_value_t lp_v = val->lp_value;
    return lp_value_to_double(&lp_v);
  }

  default:
    assert(false);
    return 0.0;
  }
}

static
void double_to_mcsat_value(mcsat_value_t* val, mcsat_value_type_t type, double d) {
  switch (type) {
    case VALUE_BOOLEAN:
      mcsat_value_construct_bool(val, d != 0.0);
      break;
    case VALUE_RATIONAL: {
      rational_t r;
      q_init(&r);
      q_set_double(&r, d);
      mcsat_value_construct_rational(val, &r);
      q_clear(&r);
      break;
    }
    case VALUE_LIBPOLY: {
      lp_rational_t lp_r;
      lp_rational_construct_from_double(&lp_r, d);
      mcsat_value_construct_lp_value_direct(val, LP_VALUE_RATIONAL, &lp_r);
      lp_rational_destruct(&lp_r);
      break;
    }
    default:
      // not implemented
      assert(false);
      break;
  }
}

void l2o_search_state_construct_empty(l2o_search_state_t *state) {
  state->var = NULL;
  state->val = NULL;
  state->n_var = 0;
  state->n_var_fixed = 0;
}

void l2o_search_state_destruct(l2o_search_state_t *state) {
  free(state->var);
  free(state->val);
}

void l2o_search_state_print(const l2o_search_state_t *state, term_table_t *terms, FILE *file) {
  for (uint32_t i = 0; i < state->n_var; ++i) {
    term_print_to_file(file, terms, state->var[i]);
    if (i < state->n_var_fixed) {
      fprintf(file, "(F)");
    }
    fprintf(file, ": %f ", state->val[i]);
    fprintf(file, "%d\n", term_type_kind(terms, state->var[i]));
  }
}

bool l2o_is_valid_term(l2o_t *l2o, term_t t) {
  t = unsigned_term(t);

  switch (term_kind(l2o->terms, t)) {
    // invalid terms are always incorrect
    case UNUSED_TERM:
    case RESERVED_TERM:
      return false;

    // if it has no variables, we're safe
    case CONSTANT_TERM:
    case ARITH_CONSTANT:
    case ARITH_FF_CONSTANT:
    case BV64_CONSTANT:
    case BV_CONSTANT:
      return true;

    default:
      break;
  }

  if (int_hmmap_find(&l2o->var_member, t, 0) == NULL) {
    return false;
  }

  bool ok = true;
  ivector_t v;
  init_ivector(&v, 0);
  int_hmmap_find_all(&l2o->var_member, t, &v);
  // Check if there are non-arith and non-bool vars; if yes, return without doing anything
  for (uint32_t i = 0; i < v.size; ++ i) {
    term_t t_i = v.data[i];
    type_kind_t type_vi = term_type_kind(l2o->terms, t_i);
    // TODO don't even collect in the first place if its not of valid type
    if(type_vi != INT_TYPE && type_vi != REAL_TYPE && type_vi != BOOL_TYPE){
      ok = false;
      break;
    }
  }
  delete_ivector(&v);
  return ok;
}

extern const lp_feasibility_set_t* get_fs_by_term(plugin_t *plugin, term_t v);

static
double l2o_pick_fs_value(l2o_t *l2o, term_t var) {
  if (l2o->nra == NULL) {
    return 0.0;
  }

  double result;
  const lp_feasibility_set_t *fs = get_fs_by_term(l2o->nra, var);
  if (fs != NULL) {
    lp_value_t lp_val;
    lp_value_construct_zero(&lp_val);
    lp_feasibility_set_pick_value(fs, &lp_val);
    result = lp_value_to_double(&lp_val);
    lp_value_destruct(&lp_val);
  } else {
    result = 0.0;
  }
  return result;
}

/** checks if there is a cached value and if it is compatible with the feasible set if it exists. */
static
double l2o_pick_cache_value(l2o_t *l2o, term_t var, const mcsat_value_t *val_mcsat) {
  switch (val_mcsat->type) {
    case VALUE_BOOLEAN:
      return val_mcsat->b;
    case VALUE_RATIONAL:
      return mcsat_value_to_double(val_mcsat);
    case VALUE_NONE:
    case VALUE_BV:
    default:
      // not supported yet
      assert(false);
      return 0.0;
    case VALUE_LIBPOLY: {
      // check if we can find a feasible set
      double result;
      const lp_feasibility_set_t *fs = get_fs_by_term(l2o->nra, var);
      if (fs == NULL || lp_feasibility_set_contains(fs, &val_mcsat->lp_value)) {
        result = mcsat_value_to_double(val_mcsat);
      } else {
        lp_value_t lp_val;
        lp_value_construct_zero(&lp_val);
        lp_feasibility_set_pick_value(fs, &lp_val);
        result = lp_value_to_double(&lp_val);
        lp_value_destruct(&lp_val);
      }
      return result;
    }
  }
}

#ifdef L2O_VAR_PRIO_SORTING
static
bool l2o_compare_vars_vsids(void *data, int32_t a, int32_t b) {
  return var_queue_cmp_variables((const var_queue_t *)data, a, b) > 0;
}

static
bool l2o_compare_vars_bool(void *data, int32_t a, int32_t b) {
  const variable_db_t *var_db = (variable_db_t*)data;
  // return true iff a < b
  return variable_db_is_boolean(var_db, a) && !variable_db_is_boolean(var_db, b);
}
#endif

static
void l2o_search_state_create(l2o_t *l2o, l2o_cost_fx_t *fx, const mcsat_trail_t *trail, bool use_cached_values, const
var_queue_t *queue, l2o_search_state_t *state) {
  ivector_t vars_t;
  init_ivector(&vars_t, 0);

  fx->get_free_vars(fx, &vars_t);

  uint32_t n_var = vars_t.size;

  if (n_var == 0) {
    delete_ivector(&vars_t);
    return;
  }

  l2o_search_state_construct_empty(state);

  assert(state->val == NULL && state->var == NULL);
  state->n_var = n_var;
  state->val = safe_malloc(sizeof(double) * n_var);
  state->var = safe_malloc(sizeof(term_t) * n_var);

  double *val = state->val;
  term_t *v = state->var;

  ivector_t vars, vars_fixed;
  init_ivector(&vars, 0);
  init_ivector(&vars_fixed, 0);

  for (uint32_t i = 0; i < n_var; ++ i) {
    term_t t_i = vars_t.data[i];
    variable_t var_i = variable_db_get_variable_if_exists(trail->var_db, t_i);
    assert (var_i != variable_null);
    ivector_push(trail_has_value(trail, var_i) ? &vars_fixed : &vars, var_i);
  }
  state->n_var_fixed = vars_fixed.size;

  delete_ivector(&vars_t);

#ifdef L2O_VAR_PRIO_SORTING
  if (queue) {
    // sort non-fixed here by VSIDS
    int_array_sort2(vars.data, vars.size, (void *) queue, l2o_compare_vars_vsids);
    assert(vars.size < 2 || queue->activity[vars.data[0]] > queue->activity[vars.data[1]]);
  } else {
    // prefer boolean variables
    int_array_sort2(vars.data, vars.size, (void *) trail->var_db, l2o_compare_vars_bool);
  }
#endif

  // join vectors
  assert(vars_fixed.size + vars.size == n_var);
  uint32_t pos = 0;
  for (uint32_t i = 0; i < vars_fixed.size; ++ i) {
    variable_t var = vars_fixed.data[i];
    v[pos] = variable_db_get_term(trail->var_db, var);
    val[pos] = mcsat_value_to_double(trail_get_value(trail, var));
    pos++;
  }
  for (uint32_t i = 0; i < vars.size; ++ i) {
    variable_t var = vars.data[i];
    v[pos] = variable_db_get_term(trail->var_db, var);
    if (use_cached_values && trail_has_cached_value(trail, var)) {
      val[pos] = l2o_pick_cache_value(l2o, v[pos], trail_get_cached_value(trail, var));
    } else if (variable_db_is_boolean(trail->var_db, var)) {
      val[pos] = 1.0;
    } else {
      val[pos] = l2o_pick_fs_value(l2o, v[pos]);
    }
    pos++;
  }
  assert(pos == n_var);

  if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
    printf("\nn_var = %d", n_var);
    printf("\nn_var_fixed = %d", vars_fixed.size);
  }

  delete_ivector(&vars);
  delete_ivector(&vars_fixed);
}

// Given variables v and values s_mpq, set hint to the trail
static
void l2o_set_hint(l2o_t *l2o, mcsat_trail_t *trail, const l2o_search_state_t *state) {
  term_table_t* terms = l2o->terms;

  double val_d;
  mcsat_value_t val_mcsat;

  assert(state->n_var_fixed <= state->n_var);
  for (uint32_t i = state->n_var_fixed; i < state->n_var; ++ i) {
    type_kind_t vi_type = term_type_kind(terms, state->var[i]);
    val_d = state->val[i];

    if (vi_type == INT_TYPE) {
      // round the value to the nearest integer
      val_d = round(val_d);
    }

    assert(vi_type != BOOL_TYPE || val_d == 1.0 || val_d == 0.0);

    double_to_mcsat_value(&val_mcsat, vi_type == BOOL_TYPE ? VALUE_BOOLEAN : VALUE_LIBPOLY, val_d);
    hint_value_to_trail(trail, state->var[i], &val_mcsat);

    assert(vi_type != INT_TYPE || (val_mcsat.type == VALUE_LIBPOLY && lp_value_is_integer(&val_mcsat.lp_value)));
  }
}

/** Minimize L2O cost function and set hint to trail */
static
void l2o_minimize_and_set_hint(l2o_t *l2o, l2o_cost_fx_t *fx, mcsat_trail_t *trail, bool use_cached_values, const
var_queue_t
*queue) {
  if (trace_enabled(l2o->tracer, "mcsat::l2o")) {
    printf("\n\n  init l2o_minimize_and_set_hint\n");
  }

  l2o_search_state_t state;

  // create search state and cost fx
  l2o_search_state_create(l2o, fx, trail, use_cached_values, queue, &state);

  if (!l2o_search_state_is_empty(&state)) {
    // Improve val using hill_climbing
    hill_climbing(l2o, fx, &state);

    // Set hints
    l2o_set_hint(l2o, trail, &state);
  }

  // destroy state
  l2o_search_state_destruct(&state);
}

// TODO check for duplicate clauses
static
bool l2o_cost_fx_cnf_add(l2o_cost_fx_cnf_t *fx, term_t t) {
  const plugin_t *bool_plugin = fx->fx.l2o->bool_plugin;
  assert(bool_plugin);

  bool success = true;
  ivector_t clause_refs, terms;
  init_ivector(&clause_refs, 0);
  init_ivector(&terms, 0);
  if (bool_plugin_get_clauses_of_term(bool_plugin, t, &clause_refs)) {
    // non-unit clause
    for (uint32_t i = 0; i < clause_refs.size; ++i) {
      clause_ref_t ref = clause_refs.data[i];
      bool_plugin_query_clause(bool_plugin, ref, &terms);
      // TODO filter true_term and false_term accordingly
      l2o_cost_fx_cnf_add_clause(fx, &terms);
      success = success && l2o_collect_free_vars_list(fx->fx.l2o, &terms);
      ivector_reset(&terms);
    }
  } else {
    // no clause found, assume unit clause
    ivector_push(&terms, t);
    l2o_cost_fx_cnf_add_clause(fx, &terms);
    success = l2o_collect_free_vars_list(fx->fx.l2o, &terms);
  }
  delete_ivector(&clause_refs);
  delete_ivector(&terms);
  return success;
}

static
l2o_cost_fx_t* l2o_make_cost_fx_cnf(l2o_t* l2o, const mcsat_trail_t *trail) {
  const ivector_t *assertions = &l2o->assertions;
  const plugin_t *bool_plugin = l2o->bool_plugin;
  assert(bool_plugin);
  bool success = true;

  l2o_cost_fx_cnf_t fx;
  l2o_cost_fx_cnf_construct(l2o, &fx);
  for (uint32_t i = 0; i < assertions->size; ++ i) {
    term_t t = assertions->data[i];
    success = l2o_cost_fx_cnf_add(&fx, t);
    if (!success) break;
  }

  if (success) {
    l2o_cost_fx_cnf_t *fx_m = safe_malloc(sizeof(l2o_cost_fx_cnf_t));
    *fx_m = fx;
    return (l2o_cost_fx_t*) fx_m;
  } else {
    fx.fx.destruct((l2o_cost_fx_t*)&fx);
    return NULL;
  }
}

static
l2o_cost_fx_t* l2o_make_cost_fx_l2o(l2o_t* l2o, const mcsat_trail_t *trail) {
  const ivector_t* assertions = &l2o->assertions;

  // ensure that the term has freevares are collected
  for (uint32_t i = 0; i < assertions->size; ++ i) {
    term_t t = assertions->data[i];
    if (!l2o_collect_free_vars(l2o, t)) {
      return NULL;
    }
  }

  l2o_cost_fx_term_t *ret = safe_malloc(sizeof(l2o_cost_fx_term_t));
  l2o_cost_fx_term_construct(l2o, ret);
  for (uint32_t i = 0; i < assertions->size; ++ i) {
    term_t t = assertions->data[i];
    l2o_cost_fx_term_add(ret, t);
  }

  return (l2o_cost_fx_t*)ret;
}

void l2o_run(l2o_t* l2o, mcsat_trail_t* trail, bool use_cached_values, const var_queue_t *queue) {
  l2o_cost_fx_t *fx =
#if 0
      l2o_make_cost_fx_l2o(l2o, trail);
#else
      l2o_make_cost_fx_cnf(l2o, trail);
#endif

  if (fx) {
    l2o_minimize_and_set_hint(l2o, fx, trail, use_cached_values, queue);
    // TODO make proper dynamic free function
    fx->destruct(fx);
    safe_free(fx);
    (*l2o->l2o_stats.n_runs)++;
  }
}
