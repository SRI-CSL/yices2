/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include "uf_plugin.h"
#include "app_reps.h"
#include "uf_feasible_set_db.h"

#include "mcsat/trail.h"
#include "mcsat/tracing.h"
#include "mcsat/watch_list_manager.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/value.h"

#include "utils/int_array_sort2.h"
#include "model/models.h"

#include "terms/terms.h"
#include "yices.h"

typedef struct {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

  /** Watch list manager for applications */
  watch_list_manager_t wlm_apps;

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

  /** Exception handler */
  jmp_buf* exception;

} uf_plugin_t;

static
void uf_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  uf->ctx = ctx;

  watch_list_manager_construct(&uf->wlm_apps, uf->ctx->var_db);
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
}

static
void uf_plugin_destruct(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;
  watch_list_manager_destruct(&uf->wlm_apps);
  watch_list_manager_destruct(&uf->wlm_eqs);
  app_reps_destruct(&uf->app_reps);
  scope_holder_destruct(&uf->scope);
  delete_int_hmap(&uf->app_rep_to_val_rep);
  delete_ivector(&uf->app_reps_with_val_rep);
  delete_ivector(&uf->all_apps);
  delete_ivector(&uf->all_uvars);
  delete_ivector(&uf->conflict);
  uf_feasible_set_db_delete(uf->feasible);
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
      prop->add_at_level(prop, eq_term_var, &mcsat_value_true, level);
    } else {
      prop->add_at_level(prop, eq_term_var, &mcsat_value_false, level);
    }
  }
}

static
void uf_plugin_new_fun_application(uf_plugin_t* uf, term_t app_term, trail_token_t* prop) {

  uint32_t i;

  variable_db_t* var_db = uf->ctx->var_db;
  term_table_t* terms = uf->ctx->terms;
  const mcsat_trail_t* trail = uf->ctx->trail;

  // Variable of the application term
  variable_t app_term_var = variable_db_get_variable(var_db, app_term);
  ivector_push(&uf->all_apps, app_term_var);

  // Get the children
  int_mset_t arguments;
  int_mset_construct(&arguments, variable_null);
  composite_term_t* app_desc = app_reps_get_uf_descriptor(terms, app_term);
  uint32_t arity = app_desc->arity;

  i = app_reps_get_uf_start(terms, app_term);
  for (; i < arity; ++ i) {
    variable_t arg_var = variable_db_get_variable(var_db, app_desc->arg[i]);
    int_mset_add(&arguments, arg_var);
  }

  // Is the variable fully assigned
  bool is_fully_assigned = false;

  if (arguments.size > 0) {

    variable_t* arguments_vars = arguments.element_list.data;
    uint32_t size = arguments.element_list.size;

    // Sort variables by trail index
    int_array_sort2(arguments_vars, size, (void*) trail, uf_plugin_trail_variable_compare);

    // Make the variable list
    variable_list_ref_t var_list = watch_list_manager_new_list(&uf->wlm_apps, arguments_vars, size, app_term_var);

    // Add first variable to watch list
    watch_list_manager_add_to_watch(&uf->wlm_apps, var_list, arguments_vars[0]);

    // Check the current status of the variables
    variable_t top_var = arguments_vars[0];
    is_fully_assigned = trail_has_value(trail, top_var);

  } else {
    // No variables => fully assigned
    is_fully_assigned = true;
  }

  if (is_fully_assigned) {
    // Here, the new terms can not have assigned value, so we don't need to
    // check for conflicts
    app_reps_get_rep(&uf->app_reps, app_term_var);
  }

  // Remove temps
  int_mset_destruct(&arguments);
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
    uf_plugin_new_fun_application(uf, t, prop);
    break;
  case EQ_TERM:
    // Equality terms (for uninterpreted sorts)
    uf_plugin_new_eq(uf, t, prop);
    break;
  case UNINTERPRETED_TERM:
    ivector_push(&uf->all_uvars, variable_db_get_variable(uf->ctx->var_db, t));
    break;
  default:
    // Noting for now
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

/** Set the value representative of the application representative. */
static inline
void uf_plugin_set_val_rep(uf_plugin_t* uf, variable_t app_rep, variable_t val_rep) {
  assert(uf_plugin_get_val_rep(uf, app_rep) == variable_null);
  int_hmap_add(&uf->app_rep_to_val_rep, app_rep, val_rep);
  ivector_push(&uf->app_reps_with_val_rep, app_rep);
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
            prop->add(prop, eq_var, &mcsat_value_true);
          } else {
            prop->add(prop, eq_var, &mcsat_value_false);
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
          }
        }
      } else {

        // Check if equality is true or false and add to feasibility db
        variable_t lhs = var_list[0];
        variable_t rhs = var_list[1] == eq_var ? var_list[2] : var_list[1];

        // Is the equailty true
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
            prop->add(prop, lhs, &value);
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
void uf_plugin_get_app_conflict(uf_plugin_t* uf, variable_t lhs, variable_t rhs) {

  // CRAP ABOUT TERM NORMALIZATION: We CANT normalize the terms, since otherwise
  // terms like 1 + x = 1 + y would normalize to x = y. To be on the safe side,
  // We always make equalities as binary arith equalities

  ivector_reset(&uf->conflict);

  variable_db_t* var_db = uf->ctx->var_db;
  term_table_t* terms = uf->ctx->terms;
  const mcsat_trail_t* trail = uf->ctx->trail;

  // We have a conflict x1 != y1 or .... or xn != y2 or f(x) != f(y)

  // Add function equality first
  term_t fx = variable_db_get_term(var_db, lhs);
  term_t fy = variable_db_get_term(var_db, rhs);
  assert(fx != fy);
  // Check the type, we treat Booleans specially
  type_kind_t f_type = term_type_kind(terms, fx);
  if (f_type == BOOL_TYPE) {
    if (trail_get_boolean_value(trail, lhs)) {
      ivector_push(&uf->conflict, fx);
    } else {
      ivector_push(&uf->conflict, opposite_term(fx));
    }
    if (trail_get_boolean_value(trail, rhs)) {
      ivector_push(&uf->conflict, fy);
    } else {
      ivector_push(&uf->conflict, opposite_term(fy));
    }
  } else {
    term_t fx_eq_fy = yices_eq(fx, fy);
    ivector_push(&uf->conflict, opposite_term(fx_eq_fy));
  }

  // Now add all the intermediate equalities
  composite_term_t* fx_app = app_reps_get_uf_descriptor(terms, fx);
  composite_term_t* fy_app = app_reps_get_uf_descriptor(terms, fy);
  assert(app_reps_get_uf(terms, fx) == app_reps_get_uf(terms, fy));
  assert(fx_app->arity == fy_app->arity);
  uint32_t i = app_reps_get_uf_start(terms, fx);
  uint32_t n = fx_app->arity;
  for (; i < n; ++ i) {
    term_t x = fx_app->arg[i];
    term_t y = fy_app->arg[i];
    type_kind_t type = term_type_kind(terms, x);
    if (type == BOOL_TYPE) {
      variable_t x_var = variable_db_get_variable(var_db, x);
      variable_t y_var = variable_db_get_variable(var_db, y);
      if (trail_get_boolean_value(trail, x_var)) {
        ivector_push(&uf->conflict, x);
      } else {
        ivector_push(&uf->conflict, opposite_term(x));
      }
      if (trail_get_boolean_value(trail, y_var)) {
        ivector_push(&uf->conflict, y);
      } else {
        ivector_push(&uf->conflict, opposite_term(y));
      }
    } else {
      term_t x_eq_y = yices_eq(x, y);
      // Don't add trivially true facts
      if (x_eq_y != bool2term(true)) {
        ivector_push(&uf->conflict, x_eq_y);
      }
    }
  }
}

static
void uf_plugin_propagate_apps(uf_plugin_t* uf, variable_t var, trail_token_t* prop) {

  const mcsat_trail_t* trail = uf->ctx->trail;
  variable_db_t* var_db = uf->ctx->var_db;

  // Go through all the variable lists (constraints) where we're watching var
  remove_iterator_t it;
  variable_list_ref_t var_list_ref;
  variable_t* var_list;
  variable_t* var_list_it;

  // Get the watch-list and process
  remove_iterator_construct(&it, &uf->wlm_apps, var);
  while (trail_is_consistent(trail) && !remove_iterator_done(&it)) {

    // Get the current list where var appears
    var_list_ref = remove_iterator_get_list_ref(&it);
    var_list = watch_list_manager_get_list(&uf->wlm_apps, var_list_ref);

    // f(x) variable
    variable_t app_var = watch_list_manager_get_constraint(&uf->wlm_apps, var_list_ref);
    if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
      ctx_trace_printf(uf->ctx, "uf_plugin_propagate: app_var = ");
      ctx_trace_term(uf->ctx, variable_db_get_term(var_db, app_var));
    }

    // Find a new watch (start from [1])
    var_list_it = var_list + 1;
    assert(var == var_list[0]);
    for (; *var_list_it != variable_null; ++var_list_it) {
      if (!trail_has_value(trail, *var_list_it)) {
        // Swap with var_list[1]
        var_list[0] = *var_list_it;
        *var_list_it = var;
        // Add to new watch
        watch_list_manager_add_to_watch(&uf->wlm_apps, var_list_ref, var_list[0]);
        // Don't watch this one
        remove_iterator_next_and_remove(&it);
        break;
      }
    }

    if (*var_list_it == variable_null) {
      // We did not find a new watch so vars[1], ..., vars[n] are assigned.
      // Add and get the representative of this assignment.
      variable_t rep_var = app_reps_get_rep(&uf->app_reps, app_var);
      assert(rep_var != variable_null);
      if (trail_has_value(trail, app_var)) {
        variable_t val_rep_var = uf_plugin_get_val_rep(uf, rep_var);
        // If already has one, and both assigned to a value, check if it's the same value
        if (val_rep_var == variable_null) {
          uf_plugin_set_val_rep(uf, rep_var, app_var);
        } else if (val_rep_var != app_var) {
          const mcsat_value_t* app_value = trail_get_value(trail, app_var);
          const mcsat_value_t* val_rep_value = trail_get_value(trail, val_rep_var);
          if (!mcsat_value_eq(app_value, val_rep_value)) {
            if (ctx_trace_enabled(uf->ctx, "uf_plugin::conflict")) {
              ctx_trace_printf(uf->ctx, "app conflict 1\n");
            }
            uf_plugin_get_app_conflict(uf, app_var, val_rep_var);
            prop->conflict(prop);
          }
        }
      }
      // Keep the watch, and continue
      remove_iterator_next_and_keep(&it);
    }
  }

  // If a function application, check if it's fully assigned
  term_t var_term = variable_db_get_term(uf->ctx->var_db, var);
  if (app_reps_is_uf(uf->ctx->terms, var_term)) {
    // Get the application representative, if any
    variable_t rep_var = app_reps_get_rep(&uf->app_reps, var);
    if (rep_var != variable_null) {
      // Get the value representative
      variable_t val_rep_var = uf_plugin_get_val_rep(uf, rep_var);
      if (val_rep_var == variable_null) {
        // No value reps yet, take it over
        uf_plugin_set_val_rep(uf, rep_var, var);
      } else if (val_rep_var != var) {
        const mcsat_value_t* var_value = trail_get_value(trail, var);
        const mcsat_value_t* val_rep_value = trail_get_value(trail, val_rep_var);
        if (!mcsat_value_eq(var_value, val_rep_value)) {
          if (ctx_trace_enabled(uf->ctx, "uf_plugin::conflict")) {
            ctx_trace_printf(uf->ctx, "app conflict 2\n");
          }
          uf_plugin_get_app_conflict(uf, var, val_rep_var);
          prop->conflict(prop);
        }
      }
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
  if (watch_list_manager_size(&uf->wlm_apps) == 0 && watch_list_manager_size(&uf->wlm_eqs) == 0) {
    return;
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
      trail_print(trail, stderr);
    }

    // Propagate function applications
    if (trail_is_consistent(trail)) {
      uf_plugin_propagate_apps(uf, var, prop);
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
      NULL);

  app_reps_push(&uf->app_reps);
  uf_feasible_set_db_push(uf->feasible);
}

static
void uf_plugin_pop(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  uint32_t old_app_reps_with_val_rep_size;
  uint32_t old_all_apps_size;

  // Pop the int variable values
  scope_holder_pop(&uf->scope,
      &uf->trail_i,
      &old_app_reps_with_val_rep_size,
      &old_all_apps_size,
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

  app_reps_pop(&uf->app_reps);
  uf_feasible_set_db_pop(uf->feasible);
}


static
void uf_plugin_decide(plugin_t* plugin, variable_t x, trail_token_t* decide, bool must) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_decide: ");
    ctx_trace_term(uf->ctx, variable_db_get_term(uf->ctx->var_db, x));
  }

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
  term_table_t* terms = uf->ctx->terms;
  variable_db_t* var_db = uf->ctx->var_db;

  if (gc_vars->level == 0) {
    // UF only needs to make sure that all the applications are kept
    uint32_t i, j, m, n = uf->all_apps.size;
    for (i = 0; i < n; ++ i) {
      variable_t app_var = uf->all_apps.data[i];
      gc_info_mark(gc_vars, app_var);
      // Also mark the immediate children
      term_t app_term = variable_db_get_term(var_db, app_var);
      composite_term_t* app_desc = app_reps_get_uf_descriptor(terms, app_term);
      m = app_desc->arity;
      j = app_reps_get_uf_start(terms, app_term);
      for (; j < m; ++ j) {
        variable_t arg_i = variable_db_get_variable(var_db, app_desc->arg[j]);
        gc_info_mark(gc_vars, arg_i);
      }
    }

    // Feasible set marks reasons, and those need to be kept
    uf_feasible_set_db_gc_mark(uf->feasible, gc_vars);

    // Mark all the uninterpreted variables, these are kept
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
  watch_list_manager_gc_sweep_lists(&uf->wlm_apps, gc_vars);
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

  // We only propagate equalities dues to propagation, so the reason is the
  // literal itself

  term_t atom = variable_db_get_term(var_db, var);

  if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_explain_propagation():\n");
    ctx_trace_term(uf->ctx, atom);
  }

  type_kind_t type_kind = term_type_kind(terms, atom);

  if (type_kind == BOOL_TYPE) {

    bool value = trail_get_boolean_value(uf->ctx->trail, var);
    if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
      ctx_trace_printf(uf->ctx, "assigned to %s\n", value ? "true" : "false");
    }

    if (value) {
      // atom => atom = true
      ivector_push(reasons, atom);
      return bool2term(true);
    } else {
      // neg atom => atom = false
      ivector_push(reasons, opposite_term(atom));
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
  int32_t t2_app = app_reps_get_uf(ctx->terms, t1);
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
