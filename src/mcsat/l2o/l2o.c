/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "mcsat/l2o/l2o.h"
#include "mcsat/l2o/l2o_internal.h"
#include "mcsat/bool/bool_plugin.h"

#include "terms/term_explorer.h"
#include "utils/int_array_sort2.h"
#include "utils/int_hash_sets.h"

#include <math.h>
#include <poly/feasibility_set.h>

static
void l2o_stats_init(l2o_t* l2o) {
  l2o->l2o_stats.n_runs = statistics_new_int(&l2o->stats, "l2o::runs");
  l2o->l2o_stats.n_terms = statistics_new_int(&l2o->stats, "l2o::terms");
  l2o->l2o_stats.n_eval_runs = statistics_new_int(&l2o->stats, "l2o::eval_runs");
}

void l2o_construct(l2o_t* l2o, term_table_t* terms, jmp_buf* handler, plugin_t* na_plugin, plugin_t* bool_plugin) {
  l2o->terms = terms;
  l2o->na_plugin = na_plugin;
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
    case ARITH_FF_CONSTANT:
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

    case ARITH_FF_POLY: {
      polynomial_t *poly_desc = finitefield_poly_term_desc(l2o->terms, current_term);
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
      for (uint32_t i = 0; i < c->arity; ++i) {
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
// Approximate equality for the lossy double evaluation: |x-y| within a
// magnitude-scaled tolerance. Arguments must be side-effect free.
#define L2O_APPROX_EQ(x, y) (fabs((x) - (y)) <= L2O_EPSILON * fmax(1.0, fmax(fabs((x)), fabs((y)))))

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

    case UNINTERPRETED_TERM: {
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
    }

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
        return !L2O_APPROX_EQ(x, 0.0) ? L2O_TRUE : L2O_FALSE;
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
        for (uint32_t i = 0; i < n; ++i) {
          term_t tv = desc->arg[i];
          result *= l2o_calculate(l2o, tv, eval);
          if (result == 0.0) break;
        }
      } else { // and term
        result = 0.0;
        for (uint32_t i = 0; i < n; ++i) {
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
        return !L2O_APPROX_EQ(val1, val2) ? L2O_TRUE : L2O_FALSE;
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
        return !L2O_APPROX_EQ(val1, val2) ? L2O_TRUE : L2O_FALSE;
      }
    }

    default:
    case ARITH_ROOT_ATOM:
    case XOR_TERM:
      assert(false);
      break;
  }
  return 0.0;
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

// Cap on the denominator when turning a hill-climbing double into a rational
// hint. mpq_set_d is exact, so a value like 0.1 becomes a ~2^52 fraction;
// instead approximate by the simplest p/q with q <= this bound, so libpoly's
// exact arithmetic doesn't carry a huge denominator downstream.
#define L2O_HINT_MAX_DENOM 1024u  // 2^10

/*
 * Approximate x by the simplest rational p/q with q <= max_den, using the
 * continued-fraction convergents. Recovers exact simple rationals (0.5 -> 1/2,
 * 0.1 -> 1/10, integers -> n/1) and bounds the denominator. The hint is
 * advisory, so the approximation loss is harmless; the search is fast: the
 * convergent denominators grow at least Fibonacci-style, so the loop breaks in
 * O(log(max_den)) iterations of plain double/int64 arithmetic.
 */
static
void rational_from_double_capped(lp_rational_t* out, double x, unsigned long max_den) {
  // Non-finite has no rational value; callers must not pass one (l2o_set_hint
  // filters it). Guard defensively so we never hand mpq_set_d a NaN/Inf.
  if (!isfinite(x)) {
    assert(false);
    lp_rational_construct_from_int(out, 0, 1);
    return;
  }
  // |x| >= 2^52 is already integral, so the exact conversion is cheap (it has
  // denominator 1) and there is no fractional part to simplify. Also keeps the
  // continued-fraction integer part from overflowing int64.
  if (fabs(x) >= (double) (1LL << 52)) {
    lp_rational_construct_from_double(out, x);
    return;
  }

  long sign = (x < 0.0) ? -1 : 1;
  double frac = fabs(x);

  // convergents: p1/q1 current, p2/q2 previous (init to the -1/-2 terms)
  int64_t p2 = 0, p1 = 1;
  int64_t q2 = 1, q1 = 0;

  for (int it = 0; it < 64; ++it) {
    double fl = floor(frac);
    int64_t ai = (int64_t) fl;

    // Stop before this term pushes the denominator past the cap. Testing via
    // division (rather than computing q first) also keeps ai*q1 and ai*p1 from
    // overflowing int64. q1 == 0 only on the first iteration, where the
    // integer-part convergent ai/1 is always taken regardless of ai.
    if (q1 != 0 && ai > ((int64_t) max_den - q2) / q1) {
      break;
    }

    int64_t p = ai * p1 + p2;
    int64_t q = ai * q1 + q2;
    p2 = p1; p1 = p;
    q2 = q1; q1 = q;

    double rem = frac - fl;
    if (rem <= 0.0) {
      break;  // exact
    }
    frac = 1.0 / rem;
    if (!isfinite(frac)) {
      break;
    }
  }

  // q1 >= 1: the integer-part convergent is always taken on the first iteration
  lp_rational_construct_from_int(out, sign * p1, (unsigned long) q1);
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
      rational_from_double_capped(&lp_r, d, L2O_HINT_MAX_DENOM);
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

/**
 * True if var currently has an empty feasible set: no value is consistent with
 * the trail. This is a not-yet-reported conflict (l2o_run executes before the
 * next propagation that would detect it), so any l2o hint would be computed
 * over a doomed assignment.
 */
static
bool l2o_var_is_infeasible(l2o_t *l2o, term_t var) {
  if (l2o->na_plugin == NULL) {
    return false;
  }
  const lp_feasibility_set_t *fs = get_fs_by_term(l2o->na_plugin, var);
  return fs != NULL && lp_feasibility_set_is_empty(fs);
}

static
double l2o_pick_fs_value(l2o_t *l2o, term_t var) {
  if (l2o->na_plugin == NULL) {
    return 0.0;
  }

  double result;
  const lp_feasibility_set_t *fs = get_fs_by_term(l2o->na_plugin, var);
  if (fs != NULL) {
    assert(!lp_feasibility_set_is_empty(fs)); // l2o_run bails before this on an empty set
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
      const lp_feasibility_set_t *fs = get_fs_by_term(l2o->na_plugin, var);
      assert(fs == NULL || !lp_feasibility_set_is_empty(fs)); // l2o_run bails before this on an empty set
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

  // empty state by default, so the caller always sees a valid (skippable) state
  l2o_search_state_construct_empty(state);

  if (n_var == 0) {
    delete_ivector(&vars_t);
    return;
  }

  // If any variable is currently infeasible, the trail is heading for a conflict
  // that the next propagation will report; a hint computed now would be over a
  // doomed assignment, so skip this l2o run.
  for (uint32_t i = 0; i < n_var; ++ i) {
    if (l2o_var_is_infeasible(l2o, vars_t.data[i])) {
      delete_ivector(&vars_t);
      return;
    }
  }

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

    // A non-finite value has no rational representation (double_to_mcsat_value
    // would feed NaN/Inf to mpq_set_d); skip the hint for this variable. The
    // hint is advisory, so leaving it unset is safe.
    if (!isfinite(val_d)) {
      continue;
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

/**
 * Returns true iff every subterm of t has a kind that the l2o cost function and
 * evaluator can handle. Assertions containing an unsupported kind are rejected
 * (so l2o_run is skipped) instead of crashing collect_free_vars / the evaluator
 * at run time. The supported set is the intersection of what l2o_calculate and
 * l2o_evaluator_run_term implement.
 */
static
bool l2o_term_is_supported(l2o_t *l2o, term_t t) {
  term_table_t *terms = l2o->terms;
  bool supported = true;

  int_hset_t visited;
  init_int_hset(&visited, 0);

  ivector_t stack;
  init_ivector(&stack, 0);
  ivector_push(&stack, unsigned_term(t));

  while (stack.size > 0) {
    term_t current = unsigned_term(ivector_last(&stack));
    ivector_pop(&stack);
    if (!int_hset_add(&visited, current)) {
      continue; // already visited
    }

    term_kind_t kind = term_kind(terms, current);
    switch (kind) {
    case CONSTANT_TERM:
    case ARITH_CONSTANT:
    case UNINTERPRETED_TERM:
      break;

    case POWER_PRODUCT: {
      pprod_t *pp = pprod_term_desc(terms, current);
      for (uint32_t i = 0; i < pp->len; ++i) {
        ivector_push(&stack, unsigned_term(pp->prod[i].var));
      }
      break;
    }

    case ARITH_POLY: {
      polynomial_t *p = poly_term_desc(terms, current);
      for (uint32_t i = 0; i < p->nterms; ++i) {
        term_t var = p->mono[i].var;
        if (good_term(terms, var)) {
          ivector_push(&stack, unsigned_term(var));
        }
      }
      break;
    }

    case ITE_TERM:
    case ITE_SPECIAL:
    case OR_TERM:
    case EQ_TERM:
    case ARITH_EQ_ATOM:
    case ARITH_BINEQ_ATOM:
    case ARITH_GE_ATOM:
    case ARITH_FLOOR:
    case ARITH_CEIL:
    case ARITH_ABS:
    case ARITH_RDIV:
    case ARITH_IDIV:
    case ARITH_MOD: {
      composite_term_t *c = get_composite(terms, kind, current);
      for (uint32_t i = 0; i < c->arity; ++i) {
        ivector_push(&stack, unsigned_term(c->arg[i]));
      }
      break;
    }

    default:
      supported = false;
      break;
    }

    if (!supported) {
      break;
    }
  }

  delete_ivector(&stack);
  delete_int_hset(&visited);
  return supported;
}

static
l2o_cost_fx_t* l2o_make_cost_fx_l2o(l2o_t* l2o, const mcsat_trail_t *trail) {
  const ivector_t* assertions = &l2o->assertions;

  // ensure that the term has free vars are collected
  for (uint32_t i = 0; i < assertions->size; ++ i) {
    term_t t = assertions->data[i];
    // reject (skip l2o) assertions with kinds the cost fx / evaluator can't handle;
    // checked before collect_free_vars so it never walks an unsupported term
    if (!l2o_term_is_supported(l2o, t) || !l2o_collect_free_vars(l2o, t)) {
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
  l2o_cost_fx_t* fx = l2o_make_cost_fx_l2o(l2o, trail);

  if (fx) {
    l2o_minimize_and_set_hint(l2o, fx, trail, use_cached_values, queue);
    fx->destruct(fx);
    safe_free(fx);
    (*l2o->l2o_stats.n_runs)++;
  }
}
