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

#include "uf_plugin.h"
#include "app_reps.h"
#include "uf_feasible_set_db.h"

#include "mcsat/trail.h"
#include "mcsat/tracing.h"
#include "mcsat/watch_list_manager.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/value.h"

#include "mcsat/eq/equality_graph.h"

#include "utils/int_array_sort2.h"
#include "model/models.h"

#include "terms/terms.h"

#include "inttypes.h"

typedef enum {
  PROPAGATED_BY_UF_PLUGIN,
  PROPAGATED_BY_EQ_GRAPH
} uf_propagation_source_t;

typedef struct {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

  /** Watch list manager for equalities */
  watch_list_manager_t wlm_eqs;

  /** App representatives */
  app_reps_t app_reps;

  /** Next index of the trail to process */
  uint32_t trail_i;

  /** Scope holder for the int variables */
  scope_holder_t scope;

  /** Map from application representatives to value representatives */
  int_hmap_t app_rep_to_val_rep;

  /** List of app representatives that have a value representative */
  ivector_t app_reps_with_val_rep;

  /** Conflict  */
  ivector_t conflict;

  /** All function applications ever seen */
  ivector_t all_apps;

  /** All uninterpreted symbols */
  ivector_t all_uvars;

  /** Feasible sets for uninterpreted terms */
  uf_feasible_set_db_t* feasible;

  /** The term manager (no ITE simplification) */
  term_manager_t* tm;

  /** Equality graph */
  eq_graph_t eq_graph;

  /** Stuff added to eq_graph */
  ivector_t eq_graph_addition_trail;

  /** List of propagated variables */
  ivector_t propagated_by_eq_graph_list;

  /** Map from variables, to reason of propagation */
  int_hmap_t propagated_by_eq_graph;

  /** Exception handler */
  jmp_buf* exception;

} uf_plugin_t;

static
void uf_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  uf->ctx = ctx;

  watch_list_manager_construct(&uf->wlm_eqs, uf->ctx->var_db);
  app_reps_construct(&uf->app_reps, 0, ctx->var_db, ctx->trail, ctx->terms);
  scope_holder_construct(&uf->scope);
  init_int_hmap(&uf->app_rep_to_val_rep, 0);
  init_ivector(&uf->app_reps_with_val_rep, 0);
  init_ivector(&uf->all_apps, 0);
  init_ivector(&uf->all_uvars, 0);
  init_ivector(&uf->conflict, 0);

  uf->feasible = uf_feasible_set_db_new(ctx->terms, ctx->var_db, ctx->trail);

  uf->trail_i = 0;

  // Terms
  ctx->request_term_notification_by_kind(ctx, APP_TERM);
  ctx->request_term_notification_by_kind(ctx, ARITH_RDIV);
  ctx->request_term_notification_by_kind(ctx, ARITH_IDIV);
  ctx->request_term_notification_by_kind(ctx, ARITH_MOD);
  ctx->request_term_notification_by_kind(ctx, EQ_TERM);

  // Types
  ctx->request_term_notification_by_type(ctx, UNINTERPRETED_TYPE);

  // Decisions
  ctx->request_decision_calls(ctx, UNINTERPRETED_TYPE);

  // Equality graph
  eq_graph_construct(&uf->eq_graph, ctx, "uf");
  init_ivector(&uf->eq_graph_addition_trail, 0);

  // Propagation
  init_ivector(&uf->propagated_by_eq_graph_list, 0);
  init_int_hmap(&uf->propagated_by_eq_graph, 0);

  // Term manager
  uf->tm = &ctx->var_db->tm;
}

static
void uf_plugin_destruct(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;
  watch_list_manager_destruct(&uf->wlm_eqs);
  app_reps_destruct(&uf->app_reps);
  scope_holder_destruct(&uf->scope);
  delete_int_hmap(&uf->app_rep_to_val_rep);
  delete_ivector(&uf->app_reps_with_val_rep);
  delete_ivector(&uf->all_apps);
  delete_ivector(&uf->all_uvars);
  delete_ivector(&uf->conflict);
  uf_feasible_set_db_delete(uf->feasible);
  eq_graph_destruct(&uf->eq_graph);
  delete_ivector(&uf->eq_graph_addition_trail);
  delete_ivector(&uf->propagated_by_eq_graph_list);
  delete_int_hmap(&uf->propagated_by_eq_graph);
}

static
bool uf_plugin_trail_variable_compare(void *data, variable_t t1, variable_t t2) {
  const mcsat_trail_t* trail;
  bool t1_has_value, t2_has_value;
  uint32_t t1_level, t2_level;

  trail = data;

  // We compare variables based on the trail level, unassigned to the front,
  // then assigned ones by decreasing level

  // Literals with no value
  t1_has_value = trail_has_value(trail, t1);
  t2_has_value = trail_has_value(trail, t2);
  if (!t1_has_value && !t2_has_value) {
    // Both have no value, just order by variable
    return t1 < t2;
  }

  // At least one has a value
  if (!t1_has_value) {
    // t1 < t2, goes to front
    return true;
  }
  if (!t2_has_value) {
    // t2 < t1, goes to front
    return false;
  }

  // Both literals have a value, sort by decreasing level
  t1_level = trail_get_level(trail, t1);
  t2_level = trail_get_level(trail, t2);
  if (t1_level != t2_level) {
    // t1 > t2 goes to front
    return t1_level > t2_level;
  } else {
    return t1 < t2;
  }
}

static inline
void uf_plugin_propagate_var(uf_plugin_t* uf, trail_token_t* prop, variable_t x, const mcsat_value_t* v, uf_propagation_source_t source, int32_t level) {
  if (level < 0) {
    prop->add(prop, x, v);
  } else {
    prop->add_at_level(prop, x, v, level);
  }
  if (source == PROPAGATED_BY_EQ_GRAPH) {
    int_hmap_pair_t* find = int_hmap_get(&uf->propagated_by_eq_graph, x);
    assert(find->val < 0);
    find->val = 1;
    ivector_push(&uf->propagated_by_eq_graph_list, x);
  }
}

static
void uf_plugin_process_eq_graph_propagations(uf_plugin_t* uf, trail_token_t* prop) {
  // Process any propagated terms
  if (eq_graph_has_propagated_terms(&uf->eq_graph)) {
    uint32_t i = 0;
    ivector_t eq_propagations;
    init_ivector(&eq_propagations, 0);
    eq_graph_get_propagated_terms(&uf->eq_graph, &eq_propagations);
    for (; trail_is_consistent(uf->ctx->trail) && i < eq_propagations.size; ++ i) {
      term_t t = eq_propagations.data[i];
      variable_t t_var = variable_db_get_variable_if_exists(uf->ctx->var_db, t);
      if (t_var != variable_null && !trail_has_value(uf->ctx->trail, t_var)) {
        const mcsat_value_t* v = eq_graph_get_propagated_term_value(&uf->eq_graph, t);
        if (ctx_trace_enabled(uf->ctx, "mcsat::eq::propagate")) {
          ctx_trace_term(uf->ctx, t);
          fprintf(ctx_trace_out(uf->ctx), " -> ");
          mcsat_value_print(v, ctx_trace_out(uf->ctx));
          fprintf(ctx_trace_out(uf->ctx), "\n");
        }
        uf_plugin_propagate_var(uf, prop, t_var, v, PROPAGATED_BY_EQ_GRAPH, -1);
      }
    }
    delete_ivector(&eq_propagations);
  }
}

static
void uf_plugin_add_to_eq_graph(uf_plugin_t* uf, term_t t, bool record) {

  term_table_t* terms = uf->ctx->terms;

  // The kind
  term_kind_t t_kind = term_kind(terms, t);

  // Add to equality graph
  composite_term_t* t_desc = NULL;
  uint32_t children_start = 0;
  switch (t_kind) {
  case APP_TERM:
    t_desc = app_term_desc(terms, t);
    eq_graph_add_ufun_term(&uf->eq_graph, t, t_desc->arg[0], t_desc->arity - 1, t_desc->arg + 1);
    children_start = 1;
    break;
  case ARITH_RDIV:
    t_desc = arith_rdiv_term_desc(terms, t);
    eq_graph_add_ifun_term(&uf->eq_graph, t, ARITH_RDIV, 2, t_desc->arg);
    break;
  case ARITH_IDIV:
    t_desc = arith_idiv_term_desc(terms, t);
    eq_graph_add_ifun_term(&uf->eq_graph, t, ARITH_IDIV, 2, t_desc->arg);
    break;
  case ARITH_MOD:
    t_desc = arith_mod_term_desc(terms, t);
    eq_graph_add_ifun_term(&uf->eq_graph, t, ARITH_MOD, 2, t_desc->arg);
    break;
  case EQ_TERM:
    t_desc = eq_term_desc(terms, t);
    eq_graph_add_ifun_term(&uf->eq_graph, t, EQ_TERM, 2, t_desc->arg);
    break;
  default:
    assert(false);
  }

  // Make sure the subterms are registered
  uint32_t i;
  for (i = children_start; i < t_desc->arity; ++ i) {
    term_t c = t_desc->arg[i];
    variable_db_get_variable(uf->ctx->var_db, c);
  }

  // Record addition so we can re-add on backtracks
  if (record) {
    ivector_push(&uf->eq_graph_addition_trail, t);
  }
}

static
void uf_plugin_new_eq(uf_plugin_t* uf, term_t eq_term, trail_token_t* prop) {

  variable_db_t* var_db = uf->ctx->var_db;
  term_table_t* terms = uf->ctx->terms;
  const mcsat_trail_t* trail = uf->ctx->trail;

  // Variable of the eq term
  variable_t eq_term_var = variable_db_get_variable(var_db, eq_term);
  composite_term_t* eq_desc = eq_term_desc(terms, eq_term);

  term_t lhs_term = eq_desc->arg[0];
  term_t rhs_term = eq_desc->arg[1];
  variable_t lhs_term_var = variable_db_get_variable(var_db, lhs_term);
  variable_t rhs_term_var = variable_db_get_variable(var_db, rhs_term);

  // Ignore interpreted equalities
  if (term_type_kind(terms, lhs_term) != UNINTERPRETED_TYPE) {
    return;
  }

  // Setup the variable list
  variable_t vars[3];
  vars[0] = eq_term_var;
  vars[1] = lhs_term_var;
  vars[2] = rhs_term_var;

  // Bump vars
  uf->ctx->bump_variable(uf->ctx, lhs_term_var);
  uf->ctx->bump_variable(uf->ctx, rhs_term_var);

  // Sort variables by trail index
  int_array_sort2(vars, 3, (void*) trail, uf_plugin_trail_variable_compare);

  // Make the variable list
  variable_list_ref_t var_list = watch_list_manager_new_list(&uf->wlm_eqs, vars, 3, eq_term_var);

  // Add first two variables to watch list
  watch_list_manager_add_to_watch(&uf->wlm_eqs, var_list, vars[0]);
  watch_list_manager_add_to_watch(&uf->wlm_eqs, var_list, vars[1]);

  // If both assigned, propagate
  if (trail_has_value(trail, lhs_term_var) && trail_has_value(trail, rhs_term_var)) {
    const mcsat_value_t* lhs_value = trail_get_value(trail, lhs_term_var);
    const mcsat_value_t* rhs_value = trail_get_value(trail, rhs_term_var);
    int lhs_eq_rhs = mcsat_value_eq(lhs_value, rhs_value);

    uint32_t lhs_level = trail_get_level(trail, lhs_term_var);
    uint32_t rhs_level = trail_get_level(trail, rhs_term_var);
    uint32_t level = lhs_level > rhs_level ? lhs_level : rhs_level;

    assert (!trail_has_value(trail, eq_term_var));
    if (lhs_eq_rhs) {
      uf_plugin_propagate_var(uf, prop, eq_term_var, &mcsat_value_true, PROPAGATED_BY_UF_PLUGIN, level);
    } else {
      uf_plugin_propagate_var(uf, prop, eq_term_var, &mcsat_value_false, PROPAGATED_BY_UF_PLUGIN, level);
    }
  }

  // Add terms to equality
  uf_plugin_add_to_eq_graph(uf, eq_term, true);
}

static
void uf_plugin_new_term_notify(plugin_t* plugin, term_t t, trail_token_t* prop) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  if (ctx_trace_enabled(uf->ctx, "mcsat::new_term")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_new_term_notify: ");
    ctx_trace_term(uf->ctx, t);
  }

  term_kind_t t_kind = term_kind(uf->ctx->terms, t);

  switch (t_kind) {
  case ARITH_MOD:
  case ARITH_IDIV:
  case ARITH_RDIV:
  case APP_TERM:
    // Application terms (or other terms we treat as uninterpreted)
    uf_plugin_add_to_eq_graph(uf, t, true);
    break;
  case EQ_TERM:
    // Equality terms (for uninterpreted sorts)
    uf_plugin_new_eq(uf, t, prop);
    break;
  default:
    // All other is of uninterpreted sort, and we treat as variables
    ivector_push(&uf->all_uvars, variable_db_get_variable(uf->ctx->var_db, t));
    break;
  }

}

/** Get the value representative of the application representative. */
static inline
variable_t uf_plugin_get_val_rep(uf_plugin_t* uf, variable_t app_rep) {
  int_hmap_pair_t* find = int_hmap_find(&uf->app_rep_to_val_rep, app_rep);
  if (find == NULL) {
    return variable_null;
  } else {
    return find->val;
  }
}

static
void uf_plugin_propagate_eqs(uf_plugin_t* uf, variable_t var, trail_token_t* prop) {
  const mcsat_trail_t* trail = uf->ctx->trail;
  variable_db_t* var_db = uf->ctx->var_db;

  // Go through all the variable lists (constraints) where we're watching var
  remove_iterator_t it;
  variable_list_ref_t var_list_ref;
  variable_t* var_list;
  variable_t* var_list_it;

  // Get the watch-list and process
  remove_iterator_construct(&it, &uf->wlm_eqs, var);
  while (trail_is_consistent(trail) && !remove_iterator_done(&it)) {

    // Get the current list where var appears
    var_list_ref = remove_iterator_get_list_ref(&it);
    var_list = watch_list_manager_get_list(&uf->wlm_eqs, var_list_ref);

    // x = y variable
    variable_t eq_var = watch_list_manager_get_constraint(&uf->wlm_eqs, var_list_ref);
    if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
      ctx_trace_printf(uf->ctx, "uf_plugin_propagate: eq_var = ");
      ctx_trace_term(uf->ctx, variable_db_get_term(var_db, eq_var));
    }

    // Put the variable to [1] so that [0] is the unit one
    if (var_list[0] == var && var_list[1] != variable_null) {
      var_list[0] = var_list[1];
      var_list[1] = var;
    }

    // Find a new watch (start from [2])
    var_list_it = var_list + 1;
    if (*var_list_it != variable_null) {
      for (++var_list_it; *var_list_it != variable_null; ++var_list_it) {
        if (!trail_has_value(trail, *var_list_it)) {
          // Swap with var_list[1]
          var_list[1] = *var_list_it;
          *var_list_it = var;
          // Add to new watch
          watch_list_manager_add_to_watch(&uf->wlm_eqs, var_list_ref, var_list[1]);
          // Don't watch this one
          remove_iterator_next_and_remove(&it);
          break;
        }
      }
    }

    if (*var_list_it == variable_null) {
      if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
        ctx_trace_printf(uf->ctx, "no watch found\n");
      }
      // We did not find a new watch so vars[1], ..., vars[n] are assigned.
      // If vars[0] is an equality, we propagate it, otherwise, we update
      // the feasibility set
      if (var_list[0] == eq_var) {

        // lhs = rhs
        variable_t lhs = var_list[1];
        variable_t rhs = var_list[2];

        // Check the model value
        const mcsat_value_t* lhs_value = trail_get_value(trail, lhs);
        const mcsat_value_t* rhs_value = trail_get_value(trail, rhs);
        int lhs_eq_rhs = mcsat_value_eq(lhs_value, rhs_value);

        // Evaluate the equality if it doesn't have a value
        if (!trail_has_value(trail, eq_var)) {
          if (lhs_eq_rhs) {
            uf_plugin_propagate_var(uf, prop, eq_var, &mcsat_value_true, PROPAGATED_BY_UF_PLUGIN, -1);
          } else {
            uf_plugin_propagate_var(uf, prop, eq_var, &mcsat_value_false, PROPAGATED_BY_UF_PLUGIN, -1);
          }
        } else {
          // Equality already has a value, check that it's the right one
          bool eq_var_value = trail_get_boolean_value(trail, eq_var);
          if (eq_var_value != lhs_eq_rhs) {
            if (ctx_trace_enabled(uf->ctx, "uf_plugin::conflict")) {
              ctx_trace_printf(uf->ctx, "eq conflict 1\n");
            }
            term_t eq_term = variable_db_get_term(var_db, eq_var);
            // Equality can not be both true and false at the same time
            ivector_reset(&uf->conflict);
            ivector_push(&uf->conflict, eq_term);
            ivector_push(&uf->conflict, opposite_term(eq_term));
            prop->conflict(prop);
            assert(false); // EQ should catch
          }
        }
      } else {

        // Check if equality is true or false and add to feasibility db
        variable_t lhs = var_list[0];
        variable_t rhs = var_list[1] == eq_var ? var_list[2] : var_list[1];

        // Is the equality true
        bool eq_true = trail_get_boolean_value(trail, eq_var);

        // Get the value of the right-hand side (have to cast, since yices rationals
        // don't have const parameters.
        mcsat_value_t* rhs_val = (mcsat_value_t*) trail_get_value(trail, rhs);
        assert(rhs_val->type == VALUE_RATIONAL);
        assert(q_fits_int32(&rhs_val->q));
        int32_t rhs_val_int;
        q_get32(&rhs_val->q, &rhs_val_int);

        // Update the feasible set
        bool feasible = true;
        if (eq_true) {
          feasible = uf_feasible_set_db_set_equal(uf->feasible, lhs, rhs_val_int, eq_var);

          // Also propagate the value
          if (!trail_has_value(trail, lhs)) {
            rational_t q;
            q_init(&q);
            q_set32(&q, rhs_val_int);
            mcsat_value_t value;
            mcsat_value_construct_rational(&value, &q);
            uf_plugin_propagate_var(uf, prop, lhs, &value, PROPAGATED_BY_UF_PLUGIN, -1);
            mcsat_value_destruct(&value);
            q_clear(&q);
          }

        } else {
          feasible = uf_feasible_set_db_set_disequal(uf->feasible, lhs, rhs_val_int, eq_var);
        }

        // Ooops, a conflict
        if (!feasible) {
          if (ctx_trace_enabled(uf->ctx, "uf_plugin::conflict")) {
            ctx_trace_printf(uf->ctx, "eq conflict 2\n");
          }
          ivector_reset(&uf->conflict);
          uf_feasible_set_db_get_conflict(uf->feasible, lhs, &uf->conflict);
          prop->conflict(prop);
          assert(false); // EQ should catch
        }
      }

      // Keep the watch, and continue
      remove_iterator_next_and_keep(&it);
    }
  }

  // Done, destruct the iterator
  remove_iterator_destruct(&it);
}

static
void uf_plugin_propagate(plugin_t* plugin, trail_token_t* prop) {

  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_propagate()\n");
  }

  // If we're not watching anything, we just ignore
  if (watch_list_manager_size(&uf->wlm_eqs) == 0 && eq_graph_term_size(&uf->eq_graph) == 0) {
    return;
  }

  // Propagate known terms
  eq_graph_propagate_trail(&uf->eq_graph);

  // Check for conflicts
  if (uf->eq_graph.in_conflict) {
    // Report conflict
    prop->conflict(prop);
    // Construct the conflict
    eq_graph_get_conflict(&uf->eq_graph, &uf->conflict, NULL);
  } else {
    uf_plugin_process_eq_graph_propagations(uf, prop);
  }

  // Context
  const mcsat_trail_t* trail = uf->ctx->trail;
  variable_db_t* var_db = uf->ctx->var_db;

  // Propagate
  variable_t var;
  for(; trail_is_consistent(trail) && uf->trail_i < trail_size(trail); ++ uf->trail_i) {
    // Current trail element
    var = trail_at(trail, uf->trail_i);

    if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
      ctx_trace_printf(uf->ctx, "uf_plugin_propagate: ");
      ctx_trace_term(uf->ctx, variable_db_get_term(var_db, var));
      ctx_trace_printf(uf->ctx, "trail: ");
      trail_print(trail, ctx_trace_out(uf->ctx));
    }

    // Propagate equalities
    if (trail_is_consistent(trail)) {
      uf_plugin_propagate_eqs(uf, var, prop);
    }
  }
}

static
void uf_plugin_push(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  // Pop the int variable values
  scope_holder_push(&uf->scope,
      &uf->trail_i,
      &uf->app_reps_with_val_rep.size,
      &uf->all_apps.size,
      &uf->propagated_by_eq_graph_list.size,
      &uf->eq_graph_addition_trail.size,
      NULL);

  app_reps_push(&uf->app_reps);
  uf_feasible_set_db_push(uf->feasible);
  eq_graph_push(&uf->eq_graph);
}

static
void uf_plugin_pop(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  uint32_t old_app_reps_with_val_rep_size;
  uint32_t old_all_apps_size;
  uint32_t old_propagated_vars_size;
  uint32_t old_eq_graph_addition_trail_size;

  // Pop the int variable values
  scope_holder_pop(&uf->scope,
      &uf->trail_i,
      &old_app_reps_with_val_rep_size,
      &old_all_apps_size,
      &old_propagated_vars_size,
      &old_eq_graph_addition_trail_size,
      NULL);

  while (uf->app_reps_with_val_rep.size > old_app_reps_with_val_rep_size) {
    variable_t app_rep = ivector_pop2(&uf->app_reps_with_val_rep);
    int_hmap_pair_t* find = int_hmap_find(&uf->app_rep_to_val_rep, app_rep);
    assert(find != NULL);
    int_hmap_erase(&uf->app_rep_to_val_rep, find);
  }

  while (uf->all_apps.size > old_all_apps_size) {
    ivector_pop(&uf->all_apps);
  }

  while (uf->propagated_by_eq_graph_list.size > old_propagated_vars_size) {
    variable_t x = ivector_pop2(&uf->propagated_by_eq_graph_list);
    int_hmap_pair_t* find = int_hmap_find(&uf->propagated_by_eq_graph, x);
    assert(find != NULL);
    int_hmap_erase(&uf->propagated_by_eq_graph, find);
  }

  app_reps_pop(&uf->app_reps);
  uf_feasible_set_db_pop(uf->feasible);
  eq_graph_pop(&uf->eq_graph);

  // Re-add all the terms to eq graph
  uint32_t i;
  for (i = old_eq_graph_addition_trail_size; i < uf->eq_graph_addition_trail.size; ++ i) {
    term_t t = uf->eq_graph_addition_trail.data[i];
    uf_plugin_add_to_eq_graph(uf, t, false);
  }
}


static
void uf_plugin_decide(plugin_t* plugin, variable_t x, trail_token_t* decide, bool must) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_decide: ");
    ctx_trace_term(uf->ctx, variable_db_get_term(uf->ctx->var_db, x));
  }

  assert(eq_graph_is_trail_propagated(&uf->eq_graph));

  // Get the actual value
  uint32_t int_value = uf_feasible_set_db_get(uf->feasible, x);

  // Make the yices rational
  rational_t q;
  q_init(&q);
  q_set32(&q, int_value);

  // Make the mcsat value
  mcsat_value_t value;
  mcsat_value_construct_rational(&value, &q);

  // Set the value
  decide->add(decide, x, &value);

  // Remove temps
  mcsat_value_destruct(&value);
  q_clear(&q);
}

static
void uf_plugin_gc_mark(plugin_t* plugin, gc_info_t* gc_vars) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  if (gc_vars->level == 0) {
    // All terms for now
    eq_graph_gc_mark_all_terms(&uf->eq_graph, gc_vars);


    // Feasible set marks reasons, and those need to be kept
    uf_feasible_set_db_gc_mark(uf->feasible, gc_vars);

    // Mark all the uninterpreted variables, these are kept
    uint32_t i, n;
    n = uf->all_uvars.size;
    for (i = 0; i < n; ++ i) {
      variable_t uvar = uf->all_uvars.data[i];
      gc_info_mark(gc_vars, uvar);
    }
  }
}

static
void uf_plugin_gc_sweep(plugin_t* plugin, const gc_info_t* gc_vars) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  // Table of representatives
  int_hmap_t new_app_rep_to_val_rep;
  init_int_hmap(&new_app_rep_to_val_rep, 0);

  // List of app representatives
  uint32_t i, n = uf->app_reps_with_val_rep.size;
  for (i = 0; i < n; i ++) {
    variable_t app = uf->app_reps_with_val_rep.data[i];
    variable_t val = uf_plugin_get_val_rep(uf, app);
    app = gc_info_get_reloc(gc_vars, app);
    if (val != variable_null) {
      val = gc_info_get_reloc(gc_vars, val);
      int_hmap_add(&new_app_rep_to_val_rep, app, val);
    }
    assert(app != variable_null);
    uf->app_reps_with_val_rep.data[i] = app;
  }

  // Swap in the representative table
  delete_int_hmap(&uf->app_rep_to_val_rep);
  uf->app_rep_to_val_rep = new_app_rep_to_val_rep;

  // The representatives table
  app_reps_gc_sweep(&uf->app_reps, gc_vars);

  // Feasible sets
  uf_feasible_set_db_gc_sweep(uf->feasible, gc_vars);

  // Watch list manager
  watch_list_manager_gc_sweep_lists(&uf->wlm_eqs, gc_vars);

  // All apps
  n = uf->all_apps.size;
  for (i = 0; i < n; ++ i) {
    variable_t app = uf->all_apps.data[i];
    app = gc_info_get_reloc(gc_vars, app);
    assert(app != variable_null);
    uf->all_apps.data[i] = app;
  }
}

static
void uf_plugin_get_conflict(plugin_t* plugin, ivector_t* conflict) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;
  ivector_swap(conflict, &uf->conflict);
  ivector_reset(&uf->conflict);
}

static
term_t uf_plugin_explain_propagation(plugin_t* plugin, variable_t var, ivector_t* reasons) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  term_table_t* terms = uf->ctx->terms;
  variable_db_t* var_db = uf->ctx->var_db;

  // We only propagate equalities due to evaluation, so the reason is the
  // literal itself

  term_t var_term = variable_db_get_term(var_db, var);

  if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_explain_propagation():\n");
    ctx_trace_term(uf->ctx, var_term);
    ctx_trace_printf(uf->ctx, "var = %"PRIu32"\n", var);
  }

  type_kind_t type_kind = term_type_kind(terms, var_term);

  // If equality propagation, just explain it
  int_hmap_pair_t* find = int_hmap_find(&uf->propagated_by_eq_graph, var);
  if (find != NULL) {
    return eq_graph_explain_term_propagation(&uf->eq_graph, var_term, reasons, NULL);
  }

  if (type_kind == BOOL_TYPE) {

    bool value = trail_get_boolean_value(uf->ctx->trail, var);
    if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
      ctx_trace_printf(uf->ctx, "assigned to %s\n", value ? "true" : "false");
    }

    if (value) {
      // atom => atom = true
      ivector_push(reasons, var_term);
      return bool2term(true);
    } else {
      // neg atom => atom = false
      ivector_push(reasons, opposite_term(var_term));
      return bool2term(false);
    }
  } else {
    assert(type_kind == UNINTERPRETED_TYPE);

    // We have an equality x = y that propagated x
    // Explanation is x = y => replace x with y

    term_t x = variable_db_get_term(var_db, var);
    variable_t x_eq_y_var = uf_feasible_set_db_get_eq_reason(uf->feasible, var);
    term_t x_eq_y = variable_db_get_term(var_db, x_eq_y_var);
    assert(term_kind(terms, x_eq_y) == EQ_TERM);
    composite_term_t* eq_desc = eq_term_desc(terms, x_eq_y);
    term_t y = eq_desc->arg[0] == x ? eq_desc->arg[1] : eq_desc->arg[0];
    ivector_push(reasons, x_eq_y);
    return y;
  }

}

static
bool uf_plugin_explain_evaluation(plugin_t* plugin, term_t t, int_mset_t* vars, mcsat_value_t* value) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  term_table_t* terms = uf->ctx->terms;
  variable_db_t* var_db = uf->ctx->var_db;
  const mcsat_trail_t* trail = uf->ctx->trail;

  if (value == NULL) {

    // Get all the variables and make sure they are all assigned.
    term_t atom = unsigned_term(t);
    assert(term_kind(terms, atom) == EQ_TERM);
    composite_term_t* eq_desc = eq_term_desc(terms, atom);

    term_t lhs_term = eq_desc->arg[0];
    term_t rhs_term = eq_desc->arg[1];
    variable_t lhs_var = variable_db_get_variable_if_exists(var_db, lhs_term);
    variable_t rhs_var = variable_db_get_variable_if_exists(var_db, rhs_term);
    assert(lhs_var != variable_null);
    assert(rhs_var != variable_null);

    // Check if both are assigned
    if (!trail_has_value(trail, lhs_var)) { return false; }
    if (!trail_has_value(trail, rhs_var)) { return false; }

    int_mset_add(vars, lhs_var);
    int_mset_add(vars, rhs_var);

    // Both variables assigned, we evaluate
    return true;

  } else {
    // We don't propagate values (yet)
    assert(false);
  }

  return true;
}

static
void uf_plugin_set_exception_handler(plugin_t* plugin, jmp_buf* handler) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;
  uf->exception = handler;
}

typedef struct {
  term_table_t* terms;
  variable_db_t* var_db;
} model_sort_data_t;


static
bool uf_plugin_build_model_compare(void *data, variable_t t1_var, variable_t t2_var) {
  model_sort_data_t* ctx = (model_sort_data_t*) data;
  term_t t1 = variable_db_get_term(ctx->var_db, t1_var);
  term_t t2 = variable_db_get_term(ctx->var_db, t2_var);
  int32_t t1_app = app_reps_get_uf(ctx->terms, t1);
  int32_t t2_app = app_reps_get_uf(ctx->terms, t2);
  if (t1_app == t2_app) {
    return t1 < t2;
  }
  return t1_app < t2_app;
}

static
void uf_plugin_build_model(plugin_t* plugin, model_t* model) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  term_table_t* terms = uf->ctx->terms;
  type_table_t* types = uf->ctx->types;
  value_table_t* values = &model->vtbl;
  variable_db_t* var_db = uf->ctx->var_db;
  const mcsat_trail_t* trail = uf->ctx->trail;

  // Data for sorting
  model_sort_data_t sort_ctx;
  sort_ctx.terms = terms;
  sort_ctx.var_db = var_db;

  // Sort the representatives by function used: we get a list of function
  // applications where we can easily collect them by linear scan
  ivector_t app_reps;
  init_ivector(&app_reps, uf->app_reps_with_val_rep.size);
  ivector_copy(&app_reps, uf->app_reps_with_val_rep.data, uf->app_reps_with_val_rep.size);
  int_array_sort2(app_reps.data, app_reps.size, &sort_ctx, uf_plugin_build_model_compare);

  // Mappings that we collect for a single function
  ivector_t mappings;
  init_ivector(&mappings, 0);

  // Temp for arguments of a one concrete mapping
  ivector_t arguments;
  init_ivector(&arguments, 0);

  // Got through all the representatives that have a set value and
  // - while same function, collect the concrete mappings
  // - if different function, construct the function and add to model
  uint32_t i;
  int32_t app_f, prev_app_f = 0;  // Current and previous function symbol
  term_t app_term, prev_app_term; // Current and previous function application term
  variable_t app_var;        // Current function application term variable
  type_t app_type;           // Current function application term type
  for (i = 0, prev_app_term = NULL_TERM; i < app_reps.size; ++ i) {

    // Current representative application
    app_var = app_reps.data[i];
    app_term = variable_db_get_term(var_db, app_var);
    app_type = term_type(terms, app_term);

    if (ctx_trace_enabled(uf->ctx, "uf_plugin::model")) {
      ctx_trace_printf(uf->ctx, "processing app rep:");
      ctx_trace_term(uf->ctx, app_term);
    }

    // Current function symbol
    app_f = app_reps_get_uf(terms, app_term);
    composite_term_t* app_comp = app_reps_get_uf_descriptor(uf->ctx->terms, app_term);

    // For division operators, we only use the ones that divide by 0
    if (app_f < 0) {
      assert(app_comp->arity == 2);
      term_t divisor_term = app_comp->arg[1];
      variable_t divisor_var = variable_db_get_variable(var_db, divisor_term);
      const mcsat_value_t* divisor_value = trail_get_value(trail, divisor_var);
      if (!mcsat_value_is_zero(divisor_value)) {
        continue;
      }
    }

    // If we changed the function, construct the previous one
    if (prev_app_term != NULL_TERM && app_f != prev_app_f) {
      type_t tau = app_reps_get_uf_type(&uf->app_reps, prev_app_term);
      value_t f_value = vtbl_mk_function(values, tau, mappings.size, mappings.data, vtbl_mk_unknown(values));
      if (prev_app_f < 0) {
        // Arithmetic stuffs
        switch (prev_app_f) {
        case APP_REP_IDIV_ID:
          vtbl_set_zero_idiv(values, f_value);
          break;
        case APP_REP_RDIV_ID:
          vtbl_set_zero_rdiv(values, f_value);
          break;
        case APP_REP_MOD_ID:
          vtbl_set_zero_mod(values, f_value);
          break;
        }
      } else {
        // Regular UF function
        model_map_term(model, prev_app_f, f_value);
      }
      ivector_reset(&mappings);
    }

    // Next concrete mapping f : (x1, x2, ..., xn) -> v
    // a) Get the v value
    mcsat_value_t* v_mcsat = (mcsat_value_t*) trail_get_value(trail, app_var);
    assert(v_mcsat->type != VALUE_NONE);
    value_t v = mcsat_value_to_value(v_mcsat, types, app_type, values);
    // b) Get the argument values
    uint32_t arg_i;
    uint32_t arg_start = app_reps_get_uf_start(uf->ctx->terms, app_term);
    uint32_t arg_end = app_f < 0 ? app_comp->arity - 1 : app_comp->arity;
    ivector_reset(&arguments);
    for (arg_i = arg_start; arg_i < arg_end; ++ arg_i) {
      term_t arg_term = app_comp->arg[arg_i];
      type_t arg_type = term_type(terms, arg_term);
      variable_t arg_var = variable_db_get_variable(var_db, arg_term);
      v_mcsat = (mcsat_value_t*) trail_get_value(trail, arg_var);
      assert(v_mcsat->type != VALUE_NONE);
      value_t arg_v = mcsat_value_to_value(v_mcsat, types, arg_type, values);
      ivector_push(&arguments, arg_v);
    }
    // c) Construct the concrete mapping, and save in the list for f
    value_t map_value = vtbl_mk_map(values, arguments.size, arguments.data, v);
    ivector_push(&mappings, map_value);

    // Remember the previous one
    prev_app_f = app_f;
    prev_app_term = app_term;
  }

  if (app_reps.size > 0 && mappings.size > 0) {
    // Construct the last function
    type_t tau = app_reps_get_uf_type(&uf->app_reps, app_term);
    value_t f_value = vtbl_mk_function(values, tau, mappings.size, mappings.data, vtbl_mk_unknown(values));
    if (app_f < 0) {
      // Arithmetic stuffs
      switch (app_f) {
      case APP_REP_IDIV_ID:
        vtbl_set_zero_idiv(values, f_value);
        break;
      case APP_REP_RDIV_ID:
        vtbl_set_zero_rdiv(values, f_value);
        break;
      case APP_REP_MOD_ID:
        vtbl_set_zero_mod(values, f_value);
        break;
      }
    } else {
      // Regular UF function
      model_map_term(model, app_f, f_value);
    }
  }

  // Remove temps
  delete_ivector(&arguments);
  delete_ivector(&mappings);
  delete_ivector(&app_reps);
}

plugin_t* uf_plugin_allocator(void) {
  uf_plugin_t* plugin = safe_malloc(sizeof(uf_plugin_t));
  plugin_construct((plugin_t*) plugin);
  plugin->plugin_interface.construct             = uf_plugin_construct;
  plugin->plugin_interface.destruct              = uf_plugin_destruct;
  plugin->plugin_interface.new_term_notify       = uf_plugin_new_term_notify;
  plugin->plugin_interface.new_lemma_notify      = 0;
  plugin->plugin_interface.event_notify          = 0;
  plugin->plugin_interface.propagate             = uf_plugin_propagate;
  plugin->plugin_interface.decide                = uf_plugin_decide;
  plugin->plugin_interface.get_conflict          = uf_plugin_get_conflict;
  plugin->plugin_interface.explain_propagation   = uf_plugin_explain_propagation;
  plugin->plugin_interface.explain_evaluation    = uf_plugin_explain_evaluation;
  plugin->plugin_interface.push                  = uf_plugin_push;
  plugin->plugin_interface.pop                   = uf_plugin_pop;
  plugin->plugin_interface.build_model           = uf_plugin_build_model;
  plugin->plugin_interface.gc_mark               = uf_plugin_gc_mark;
  plugin->plugin_interface.gc_sweep              = uf_plugin_gc_sweep;
  plugin->plugin_interface.set_exception_handler = uf_plugin_set_exception_handler;

  return (plugin_t*) plugin;
}
