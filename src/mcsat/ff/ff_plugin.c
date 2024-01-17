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

/*
 * Anything that includes "yices.h" requires these macros.
 * Otherwise the code doesn't build on Windows or Cygwin.
 */
#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include "mcsat/ff/ff_plugin.h"
#include "mcsat/ff/ff_plugin_internal.h"
#include "mcsat/ff/ff_plugin_explain.h"
#include "mcsat/ff/ff_libpoly.h"
#include "mcsat/tracing.h"

#include "utils/int_array_sort2.h"

static
void ff_plugin_stats_init(ff_plugin_t* ff) {
  // Add statistics
  ff->stats.propagations = statistics_new_int(ff->ctx->stats, "mcsat::ff::propagations");
  ff->stats.conflicts = statistics_new_int(ff->ctx->stats, "mcsat::ff::conflicts");
  ff->stats.conflicts_assumption = statistics_new_int(ff->ctx->stats, "mcsat::ff::conflicts_assumption");
  ff->stats.constraints_attached = statistics_new_int(ff->ctx->stats, "mcsat::ff::constraints_attached");
  ff->stats.evaluations = statistics_new_int(ff->ctx->stats, "mcsat::ff::evaluations");
  ff->stats.constraint = statistics_new_int(ff->ctx->stats, "mcsat::ff::constraints");
}

static
void ff_plugin_heuristics_init(ff_plugin_t* ff) {
  // Initialize heuristic
}

static
void ff_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  ff->ctx = ctx;
  ff->trail_i = 0;
  ff->conflict_variable = variable_null;

  watch_list_manager_construct(&ff->wlm, ctx->var_db);
  scope_holder_construct(&ff->scope);

  constraint_unit_info_init(&ff->unit_info);

  // Atoms
  ctx->request_term_notification_by_kind(ctx, ARITH_FF_EQ_ATOM, false);
  ctx->request_term_notification_by_kind(ctx, ARITH_FF_BINEQ_ATOM, false);

  // Terms
  ctx->request_term_notification_by_kind(ctx, ARITH_FF_CONSTANT, false);
  ctx->request_term_notification_by_kind(ctx, ARITH_FF_POLY, false);
  ctx->request_term_notification_by_kind(ctx, POWER_PRODUCT, false);

  // Types
  ctx->request_term_notification_by_type(ctx, FF_TYPE);
  ctx->request_decision_calls(ctx, FF_TYPE);

  // Constraint db and libpoly are set once the field size is known
  ff->constraint_db = NULL;
  ff->lp_data = NULL;

  init_rba_buffer(&ff->buffer, ctx->terms->pprods);

  ff_plugin_stats_init(ff);
  ff_plugin_heuristics_init(ff);
}

static
void ff_plugin_destruct(plugin_t* plugin) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  constraint_unit_info_destruct(&ff->unit_info);

  if (ff->lp_data) {
    lp_data_destruct(ff->lp_data);
    assert(ff->constraint_db);
    poly_constraint_db_delete(ff->constraint_db);
  }

  watch_list_manager_destruct(&ff->wlm);
  scope_holder_destruct(&ff->scope);
  delete_rba_buffer(&ff->buffer);
}

static inline
bool ff_plugin_has_assignment(const ff_plugin_t* ff, variable_t x) {
  return trail_has_value(ff->ctx->trail, x) && trail_get_index(ff->ctx->trail, x) < ff->trail_i;
}

static inline
bool ff_plugin_trail_variable_compare(void *data, variable_t t1, variable_t t2) {
  return trail_variable_compare((const mcsat_trail_t *)data, t1, t2);
}

static
const mcsat_value_t* ff_plugin_constraint_evaluate(ff_plugin_t* ff, variable_t cstr_var, uint32_t* cstr_level) {

  assert(ff->lp_data);
  assert(!trail_has_value(ff->ctx->trail, cstr_var));

  // Check if it is a valid constraints
  const poly_constraint_t* cstr = poly_constraint_db_get(ff->constraint_db, cstr_var);
  if (!poly_constraint_is_valid(cstr)) {
    return NULL;
  }
  assert(!poly_constraint_is_root_constraint(cstr));

  // Constraint var list
  variable_list_ref_t var_list_ref = watch_list_manager_get_list_of(&ff->wlm, cstr_var);
  const variable_t* var_list = watch_list_manager_get_list(&ff->wlm, var_list_ref);

  // Get the timestamp and level
  uint32_t cstr_timestamp = 0;
  *cstr_level = ff->ctx->trail->decision_level_base;
  const mcsat_trail_t* trail = ff->ctx->trail;
  const variable_t* var_i = var_list;
  while (*var_i != variable_null) {
    if (ff_plugin_has_assignment(ff, *var_i)) {
      uint32_t timestamp_i = trail_get_value_timestamp(trail, *var_i);
      assert(timestamp_i > 0);
      if (cstr_timestamp < timestamp_i) {
        cstr_timestamp = timestamp_i;
      }
      uint32_t level_i = trail_get_level(trail, *var_i);
      if (level_i > *cstr_level) {
        *cstr_level = level_i;
      }
    } else {
      // Doesn't evaluate
      return NULL;
    }
    var_i ++;
  }

  bool cstr_value = false;

#if 0
  // Check the cache
  int_hmap_pair_t* find_value = int_hmap_find(&ff->evaluation_value_cache, cstr_var);
  int_hmap_pair_t* find_timestamp = NULL;
  if (find_value != NULL) {
    find_timestamp = int_hmap_find(&ff->evaluation_timestamp_cache, cstr_var);
    assert(find_timestamp != NULL);
    if (find_timestamp->val == cstr_timestamp) {
      // Can use the cached value;
      cstr_value = find_value->val;
      return cstr_value ? &mcsat_value_true : &mcsat_value_false;
    }
  }
#endif

  // NOTE: with/without caching can change search. Some poly constraints
  // do not evaluate (see ok below, but we can evaluate them in the cache)

  // Compute the evaluation
  bool ok = poly_constraint_evaluate(cstr, ff->lp_data, &cstr_value);
  (void) ok;
  assert(ok);
  (*ff->stats.evaluations) ++;

#if 0
  // Set the cache
  if (find_value != NULL) {
    find_value->val = cstr_value;
    find_timestamp->val = cstr_timestamp;
  } else {
    int_hmap_add(&ff->evaluation_value_cache, cstr_var, cstr_value);
    int_hmap_add(&ff->evaluation_timestamp_cache, cstr_var, cstr_timestamp);
  }
#endif

  return cstr_value ? &mcsat_value_true : &mcsat_value_false;
}

static
void ff_plugin_process_fully_assigned_constraint(ff_plugin_t* ff, trail_token_t* prop, variable_t cstr_var) {

  uint32_t cstr_level = 0;
  const mcsat_value_t* cstr_value = NULL;

  assert(!trail_has_value(ff->ctx->trail, cstr_var));

  if (ctx_trace_enabled(ff->ctx, "ff::evaluate")) {
    trail_print(ff->ctx->trail, ctx_trace_out(ff->ctx));
    ctx_trace_term(ff->ctx, variable_db_get_term(ff->ctx->var_db, cstr_var));
  }

  // Compute the evaluation timestamp
  cstr_value = ff_plugin_constraint_evaluate(ff, cstr_var, &cstr_level);

  // Propagate
  if (cstr_value) {
    bool ok = prop->add_at_level(prop, cstr_var, cstr_value, cstr_level);
    (void)ok;
    assert(ok);
    assert(cstr_level < ff->ctx->trail->decision_level);
  }

  if (ctx_trace_enabled(ff->ctx, "ff::evaluate")) {
    trail_print(ff->ctx->trail, ctx_trace_out(ff->ctx));
  }
}

static
void ff_plugin_set_lp_data(ff_plugin_t *ff, term_t t) {
  type_t tau = term_type(ff->ctx->terms, t);
  assert(is_ff_type(ff->ctx->types, tau));

  mpz_t order;
  mpz_init(order);
  rational_t *order_q = ff_type_size(ff->ctx->types, tau);
  q_get_mpz(order_q, order);

  if (ff->lp_data) {
    assert(ff->constraint_db);

    // TODO error reporting instead of assertion
    assert(lp_data_is_order(ff->lp_data, order));
  } else {
    ff->lp_data = lp_data_new(order);
    ff->constraint_db = poly_constraint_db_new(ff->lp_data);
  }
  mpz_clear(order);

  assert(ff->lp_data);
  assert(ff->constraint_db);
}

static
void ff_plugin_new_term_notify(plugin_t* plugin, term_t t, trail_token_t* prop) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;
  term_table_t* terms = ff->ctx->terms;

  if (ctx_trace_enabled(ff->ctx, "mcsat::new_term")) {
    ctx_trace_printf(ff->ctx, "ff_plugin_new_term_notify: ");
    ctx_trace_term(ff->ctx, t);
  }

  assert(!is_neg_term(t));

  term_kind_t t_kind = term_kind(terms, t);

  if (t_kind == POWER_PRODUCT && !is_finitefield_term(terms, t)) {
    return;
  }

  // The variable
  variable_t t_var = variable_db_get_variable(ff->ctx->var_db, t);

// uninterpreted terms are just variables
//  if (t_kind == UNINTERPRETED_TERM && term_type_kind(terms, t) != FF_TYPE) {
//    assert(0);
//    return;
//  }

  int_mset_t t_variables;
  int_mset_construct(&t_variables, variable_null);
  ff_plugin_get_constraint_variables(ff, t, &t_variables);

  bool is_constraint = t_variables.element_list.size != 1 || t_variables.element_list.data[0] != t_var;

  if (is_constraint) {

    // Get the list of variables
    ivector_t* t_variables_list = int_mset_get_list(&t_variables);

    assert(t_variables_list->size > 0);

    // Register all the variables to libpoly (these are mcsat_variables)
    for (uint32_t i = 0; i < t_variables_list->size; ++ i) {
      term_t tt = variable_db_get_term(ff->ctx->var_db, t_variables_list->data[i]);
      ff_plugin_set_lp_data(ff, tt);
      if (!lp_data_variable_has_term(ff->lp_data, tt)) {
        lp_data_add_lp_variable(ff->lp_data, terms, tt);
      }
    }

    // Bump variables
    for (uint32_t i = 0; i < t_variables_list->size; ++ i) {
      variable_t x = t_variables_list->data[i];
      uint32_t deg = int_mset_contains(&t_variables, x);
      ff->ctx->bump_variable_n(ff->ctx, x, deg);
    }

    // Sort variables by trail index
    int_array_sort2(t_variables_list->data, t_variables_list->size, (void*) ff->ctx->trail, ff_plugin_trail_variable_compare);

    if (ctx_trace_enabled(ff->ctx, "mcsat::new_term")) {
      ctx_trace_printf(ff->ctx, "ff_plugin_new_term_notify: vars: \n");
      for (uint32_t i = 0; i < t_variables_list->size; ++ i) {
        ctx_trace_term(ff->ctx, variable_db_get_term(ff->ctx->var_db, t_variables_list->data[i]));
      }
    }

    variable_list_ref_t var_list = watch_list_manager_new_list(&ff->wlm, t_variables_list->data, t_variables_list->size, t_var);

    // Add first variable to watch list
    watch_list_manager_add_to_watch(&ff->wlm, var_list, t_variables_list->data[0]);

    // Add second variable to watch list
    if (t_variables_list->size > 1) {
      watch_list_manager_add_to_watch(&ff->wlm, var_list, t_variables_list->data[1]);
    }

    // Check the current status of the constraint
    variable_t top_var = t_variables_list->data[0];
    constraint_unit_state_t unit_status = CONSTRAINT_UNKNOWN;
    if (ff_plugin_has_assignment(ff, top_var)) {
      // All variables assigned,
      unit_status = CONSTRAINT_FULLY_ASSIGNED;
    } else {
      if (t_variables_list->size == 1) {
        // Single variable, unassigned => unit
        unit_status = CONSTRAINT_UNIT;
      } else if (ff_plugin_has_assignment(ff, t_variables_list->data[1])) {
        // Second one is assigned and processed, so we're unit
        unit_status = CONSTRAINT_UNIT;
      }
    }

    // Set the status of the constraint
    constraint_unit_info_set(&ff->unit_info, t_var, unit_status == CONSTRAINT_UNIT ? top_var : variable_null, unit_status);

    // Add the constraint to the database
    ff_poly_constraint_create(ff, t_var);

    // Propagate if fully assigned
    if (unit_status == CONSTRAINT_FULLY_ASSIGNED) {
      ff_plugin_process_fully_assigned_constraint(ff, prop, t_var);
    }

    // Stats
    (*ff->stats.constraints_attached) ++;
  } else {
    if (t_kind == ARITH_FF_CONSTANT) {
      lp_integer_t int_value;
      lp_integer_construct(&int_value);
      q_get_mpz(finitefield_term_desc(terms, t), &int_value);
      lp_value_t lp_value;
      lp_value_construct(&lp_value, LP_VALUE_INTEGER, &int_value);
      mcsat_value_t mcsat_value;
      mcsat_value_construct_lp_value(&mcsat_value, &lp_value);
      prop->add_at_level(prop, t_var, &mcsat_value, ff->ctx->trail->decision_level_base);
      mcsat_value_destruct(&mcsat_value);
      lp_value_destruct(&lp_value);
      lp_integer_destruct(&int_value);
    } else {
      // create variable for t if not existent
      variable_db_get_variable(ff->ctx->var_db, t);
      ff_plugin_set_lp_data(ff, t);
      // register lp_variable for t if not existent
      if (!lp_data_variable_has_term(ff->lp_data, t)) {
        lp_data_add_lp_variable(ff->lp_data, terms, t);
      }
    }
  }

  // Remove the variables vector
  int_mset_destruct(&t_variables);
}

/**
 * Propagates the trail with BCP. When done, either the trail is fully
 * propagated, or the trail is in an inconsistent state.
 */
static
void ff_plugin_propagate(plugin_t* plugin, trail_token_t* prop) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  if (ctx_trace_enabled(ff->ctx, "ff::check_assignment")) {
    // TODO ff_plugin_check_assignment(ff);
  }

  // Context
  const mcsat_trail_t* trail = ff->ctx->trail;
  variable_db_t* var_db = ff->ctx->var_db;

  if (ctx_trace_enabled(ff->ctx, "ff::propagate")) {
    ctx_trace_printf(ff->ctx, "trail:\n");
    trail_print(trail, ff->ctx->tracer->file);
  }

  /* two jobs:
   *  - propagate information, like x = y, propagate f(x) = f(y).
   *    In my case propagate a truth value of a constraint if I know the constraint is fully assigned
   *    (can create new terms, keep track why I created new term (lazy explanation, mcsat might ask later about the explanation))
   *  - base minimum: find a conflict (no assignment for one variable)
   *    report like in uf_plugin.c:390
   *    then mcsat calls get_conflict and I fill the conflict vector
   *
   *
   *    propagate stuff like x == \alpha, because it forces a model value.
   *    maybe keep x != \alpha internally.
   */


  // TODO implement
}

/*
 * Check sat mod assignment (given a partial model at is-sat call).
 * The decide_assignment is just recording an external assignment. Register a forced value from outside.
 * decide is deciding on a theory variable by the solver. Pick a value and return it to the solver.
 */

static
void ff_plugin_decide(plugin_t* plugin, variable_t x, trail_token_t* decide_token, bool must) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  assert(variable_db_is_finitefield(ff->ctx->var_db, x));

  (void)ff;
  // TODO implement
  assert(false);
}

static
void ff_plugin_get_conflict(plugin_t* plugin, ivector_t* conflict) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  if (ctx_trace_enabled(ff->ctx, "ff::conflict")) {
    ctx_trace_printf(ff->ctx, "ff_plugin_get_conflict(): START\n");
  }

  // TODO implement
}

static
term_t ff_plugin_explain_propagation(plugin_t* plugin, variable_t var, ivector_t* reasons) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  (void)ff;
  // TODO implement
}

static
bool ff_plugin_explain_evaluation(plugin_t* plugin, term_t t, int_mset_t* vars, mcsat_value_t* value) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  bool result = true;

  // TODO implement
  (void)ff;

  // All variables assigned
  return result;
}


/*
 * It is dealing with trail addition and rollback.
 * Push and Pop trail frames
 *
 */

static
void ff_plugin_push(plugin_t* plugin) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  (void)ff;
  // TODO implement
}

static
void ff_plugin_pop(plugin_t* plugin) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  (void)ff;
  // TODO implement
}

static
void ff_plugin_gc_mark(plugin_t* plugin, gc_info_t* gc_vars) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  (void)ff;
  // TODO implement
}

static
void ff_plugin_gc_sweep(plugin_t* plugin, const gc_info_t* gc_vars) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  constraint_unit_info_gc_sweep(&ff->unit_info, gc_vars);
  if (ff->lp_data) {
    lp_data_gc_sweep(ff->lp_data, gc_vars);
  }

  // TODO add further
}

static
void ff_plugin_event_notify(plugin_t* plugin, plugin_notify_kind_t kind) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;
  (void)ff;

  switch (kind) {
    case MCSAT_SOLVER_START:
      // Re-initialize the heuristics
      break;
    case MCSAT_SOLVER_RESTART:
      // Check if clause compaction needed
      break;
    case MCSAT_SOLVER_CONFLICT:
      // Decay the scores each conflict
      break;
    case MCSAT_SOLVER_POP:
      // Not much to do
      break;
    default:
      assert(false);
  }
}

static
void ff_plugin_new_lemma_notify(plugin_t* plugin, ivector_t* lemma, trail_token_t* prop) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  (void)ff;
  // TODO implement
}

static
void ff_plugin_set_exception_handler(plugin_t* plugin, jmp_buf* handler) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;
  ff->exception = handler;
}

static
void ff_plugin_decide_assignment(plugin_t* plugin, variable_t x, const mcsat_value_t* value, trail_token_t* decide) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  (void)ff;
  // TODO implement
}

static
void ff_plugin_learn(plugin_t* plugin, trail_token_t* prop) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;
  const mcsat_trail_t* trail = ff->ctx->trail;

  if (ctx_trace_enabled(ff->ctx, "mcsat::ff::learn")) {
    ctx_trace_printf(ff->ctx, "ff_plugin_learn(): trail = ");
    trail_print(trail, ctx_trace_out(ff->ctx));
  }

  /*
   * heavy propagation at the base level (when no decisions are made yet).
   * General lemmas that are assignment independent are thus never undone.
   * Should be called at every restart. Currently, it's only called once at the beginning of the search.
   */

  // TODO implement
}

bool ff_plugin_simplify_conflict_literal(plugin_t* plugin, term_t lit, ivector_t* output) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  // TODO implement
  (void)ff;
  return false;
}

plugin_t* ff_plugin_allocator(void) {
  ff_plugin_t* plugin = safe_malloc(sizeof(ff_plugin_t));
  plugin_construct((plugin_t*) plugin);
  plugin->plugin_interface.construct           = ff_plugin_construct;
  plugin->plugin_interface.destruct            = ff_plugin_destruct;
  plugin->plugin_interface.new_term_notify     = ff_plugin_new_term_notify;
  plugin->plugin_interface.new_lemma_notify    = ff_plugin_new_lemma_notify;
  plugin->plugin_interface.event_notify        = ff_plugin_event_notify;
  plugin->plugin_interface.propagate           = ff_plugin_propagate;
  plugin->plugin_interface.decide              = ff_plugin_decide;
//  plugin->plugin_interface.decide_assignment   = ff_plugin_decide_assignment;
//  plugin->plugin_interface.learn               = ff_plugin_learn;
  plugin->plugin_interface.get_conflict        = ff_plugin_get_conflict;
  plugin->plugin_interface.explain_propagation = ff_plugin_explain_propagation;
  plugin->plugin_interface.explain_evaluation  = ff_plugin_explain_evaluation;
//  plugin->plugin_interface.simplify_conflict_literal = ff_plugin_simplify_conflict_literal;
  plugin->plugin_interface.push                = ff_plugin_push;
  plugin->plugin_interface.pop                 = ff_plugin_pop;
  plugin->plugin_interface.gc_mark             = ff_plugin_gc_mark;
  plugin->plugin_interface.gc_sweep            = ff_plugin_gc_sweep;
//  plugin->plugin_interface.set_exception_handler = ff_plugin_set_exception_handler;

  return (plugin_t*) plugin;
}

/*
 * Difference between explain prop and evaluation:
 *  evaluation of a term to true/false. (explain_evaluation: which variables did contribute to the evaluation. see nra method, can I produce a full explanation)
 *  propagation creates new terms. (explain_propagate: explains the propagation)
 */
