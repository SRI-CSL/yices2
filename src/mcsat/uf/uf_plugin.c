/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "uf_plugin.h"
#include "app_reps.h"

#include "mcsat/trail.h"
#include "mcsat/tracing.h"
#include "mcsat/watch_list_manager.h"
#include "mcsat/utils/scope_holder.h"

#include "utils/int_array_sort2.h"

#include "yices.h"

typedef struct {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

  /** The watch list manager */
  watch_list_manager_t wlm;

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

  /** Conflict x = y => f(x) = f(y) */
  variable_t conflict_lhs, conflict_rhs;

} uf_plugin_t;

static
void uf_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  uf->ctx = ctx;

  watch_list_manager_construct(&uf->wlm, uf->ctx->var_db);
  app_reps_construct(&uf->app_reps, 0, ctx->var_db, ctx->trail, ctx->terms);
  scope_holder_construct(&uf->scope);
  init_int_hmap(&uf->app_rep_to_val_rep, 0);
  init_ivector(&uf->app_reps_with_val_rep, 0);

  uf->trail_i = 0;
  uf->conflict_lhs = variable_null;
  uf->conflict_rhs = variable_null;

  ctx->request_term_notification_by_kind(ctx, APP_TERM);
}

static
void uf_plugin_destruct(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;
  watch_list_manager_destruct(&uf->wlm);
  app_reps_destruct(&uf->app_reps);
  scope_holder_destruct(&uf->scope);
  delete_int_hmap(&uf->app_rep_to_val_rep);
  delete_ivector(&uf->app_reps_with_val_rep);
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
void uf_plugin_new_fun_application(uf_plugin_t* uf, term_t app_term, trail_token_t* prop) {

  uint32_t i;

  variable_db_t* var_db = uf->ctx->var_db;
  term_table_t* terms = uf->ctx->terms;
  const mcsat_trail_t* trail = uf->ctx->trail;

  // Variable of the application term
  variable_t app_term_var = variable_db_get_variable(var_db, app_term);

  // Get the children
  assert(term_kind(terms, app_term) == APP_TERM);
  int_mset_t arguments;
  int_mset_construct(&arguments, variable_null);
  composite_term_t* app_desc = app_term_desc(terms, app_term);
  uint32_t arity = app_desc->arity;
  for (i = 1; i < arity; ++ i) {
    variable_t arg_var = variable_db_get_variable(var_db, app_desc->arg[i]);
    int_mset_add(&arguments, arg_var);
  }

  // Is the variable fully assigned
  bool is_fully_assigned = false;

  if (arguments.size > 0) {

    variable_t* arguments_vars = arguments.element_list.data;
    uint32_t size = arguments.size;

    // Sort variables by trail index
    int_array_sort2(arguments_vars, size, (void*) trail, uf_plugin_trail_variable_compare);

    // Make the variable list
    variable_list_ref_t var_list = watch_list_manager_new_list(&uf->wlm, arguments_vars, size, app_term_var);

    // Add first variable to watch list
    watch_list_manager_add_to_watch(&uf->wlm, var_list, arguments_vars[0]);

    // Add second variable to watch list
    if (size > 1) {
      watch_list_manager_add_to_watch(&uf->wlm, var_list, arguments_vars[1]);
    }

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
    app_reps_get_rep(&uf->app_reps, app_term);
  }
}

static
void uf_plugin_new_term_notify(plugin_t* plugin, term_t t, trail_token_t* prop) {
  uf_plugin_t* eq = (uf_plugin_t*) plugin;

  if (ctx_trace_enabled(eq->ctx, "mcsat::new_term")) {
    ctx_trace_printf(eq->ctx, "uf_plugin_new_term_notify: ");
    ctx_trace_term(eq->ctx, t);
  }

  term_kind_t t_kind = term_kind(eq->ctx->terms, t);

  switch (t_kind) {
  case APP_TERM:
    // We just care about the application terms
    uf_plugin_new_fun_application(eq, t, prop);
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
void uf_plugin_propagate(plugin_t* plugin, trail_token_t* prop) {

  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_propagate()\n");
  }

  // If we're not watching anything, we just ignore
  if (watch_list_manager_size(&uf->wlm) == 0) {
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

    // Go through all the variable lists (constraints) where we're watching var
    remove_iterator_t it;
    variable_list_ref_t var_list_ref;
    variable_t* var_list;
    variable_t* var_list_it;

    // Get the watch-list and process
    remove_iterator_construct(&it, &uf->wlm, var);
    while (trail_is_consistent(trail) && !remove_iterator_done(&it)) {

      // Get the current list where var appears
      var_list_ref = remove_iterator_get_list_ref(&it);
      var_list = watch_list_manager_get_list(&uf->wlm, var_list_ref);

      // f(x) variable
      variable_t app_var = watch_list_manager_get_constraint(&uf->wlm, var_list_ref);
      if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
        ctx_trace_printf(uf->ctx, "uf_plugin_propagate: app_var = ");
        ctx_trace_term(uf->ctx, variable_db_get_term(var_db, app_var));
      }

      // Find a new watch (start from [1])
      var_list_it = var_list + 1;
      if (*var_list_it != variable_null) {
        for (++ var_list_it; *var_list_it != variable_null; ++ var_list_it) {
          if (!trail_has_value(trail, *var_list_it)) {
            // Swap with var_list[1]
            var_list[0] = *var_list_it;
            *var_list_it = var;
            // Add to new watch
            watch_list_manager_add_to_watch(&uf->wlm, var_list_ref, var_list[0]);
            // Don't watch this one
            remove_iterator_next_and_remove(&it);
            break;
          }
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
              uf->conflict_lhs = app_var;
              uf->conflict_rhs = val_rep_var;
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
    if (term_kind(uf->ctx->terms, var_term) == APP_TERM) {
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
            uf->conflict_lhs = var;
            uf->conflict_rhs = val_rep_var;
            prop->conflict(prop);
          }
        }
      }
    }

    // Done, destruct the iterator
    remove_iterator_destruct(&it);
  }
}

static
void uf_plugin_push(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  // Pop the int variable values
  scope_holder_push(&uf->scope,
      &uf->trail_i,
      &uf->app_reps_with_val_rep.size,
      NULL);

  app_reps_push(&uf->app_reps);
}

static
void uf_plugin_pop(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  uint32_t old_app_reps_with_val_rep_size;

  // Pop the int variable values
  scope_holder_pop(&uf->scope,
      &uf->trail_i,
      &old_app_reps_with_val_rep_size,
      NULL);

  while (uf->app_reps_with_val_rep.size > old_app_reps_with_val_rep_size) {
    variable_t app_rep = ivector_pop2(&uf->app_reps_with_val_rep);
    int_hmap_pair_t* find = int_hmap_find(&uf->app_rep_to_val_rep, app_rep);
    assert(find != NULL);
    int_hmap_erase(&uf->app_rep_to_val_rep, find);
  }

  // Pop the representatives
  app_reps_pop(&uf->app_reps);
}

static
void uf_plugin_gc_mark(plugin_t* plugin, gc_info_t* gc) {
}

static
void uf_plugin_gc_collect(plugin_t* plugin, const gc_info_t* gc) {
}

static inline
term_t make_eq(term_table_t* terms, term_t x, term_t y) {
  if (x == y) {
    return bool2term(true);
  } else if (x < y) {
    return arith_bineq_atom(terms, x, y);
  } else {
    return arith_bineq_atom(terms, y, x);
  }
}

static
void uf_plugin_get_conflict(plugin_t* plugin, ivector_t* conflict) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  // CRAP ABOUT TERM NORMALIZATION: We CANT normalize the terms, since otherwise
  // terms like 1 + x = 1 + y would normalize to x = y. To be on the safe side,
  // We always make equalities as binary arith equalities

  variable_db_t* var_db = uf->ctx->var_db;
  term_table_t* terms = uf->ctx->terms;

  assert(uf->conflict_lhs != variable_null);
  assert(uf->conflict_rhs != variable_null);

  // We have a conflict x1 != y1 or .... or xn != y2 or f(x) != f(y)

  // Add function equality first
  term_t fx = variable_db_get_term(var_db, uf->conflict_lhs);
  term_t fy = variable_db_get_term(var_db, uf->conflict_rhs);
  assert(fx != fy);
  term_t fx_eq_fy = yices_eq(fx, fy);
  ivector_push(conflict, opposite_term(fx_eq_fy));

  // Now add all the intermediate equalities
  composite_term_t* fx_app = app_term_desc(terms, fx);
  composite_term_t* fy_app = app_term_desc(terms, fy);
  assert(fx_app->arg[0] == fy_app->arg[0]);
  assert(fx_app->arity == fy_app->arity);
  uint32_t i, n = fx_app->arity;
  for (i = 1; i < n; ++ i) {
    term_t x = fx_app->arg[i];
    term_t y = fy_app->arg[i];
    term_t x_eq_y = yices_eq(x, y);
    // Don't add trivially true facts
    if (x_eq_y != bool2term(true)) {
      ivector_push(conflict, x_eq_y);
    }
  }

  uf->conflict_lhs = variable_null;
  uf->conflict_rhs = variable_null;
}

plugin_t* uf_plugin_allocator(void) {
  uf_plugin_t* plugin = safe_malloc(sizeof(uf_plugin_t));
  plugin_construct((plugin_t*) plugin);
  plugin->plugin_interface.construct           = uf_plugin_construct;
  plugin->plugin_interface.destruct            = uf_plugin_destruct;
  plugin->plugin_interface.new_term_notify     = uf_plugin_new_term_notify;
  plugin->plugin_interface.new_lemma_notify    = 0;
  plugin->plugin_interface.event_notify        = 0;
  plugin->plugin_interface.propagate           = uf_plugin_propagate;
  plugin->plugin_interface.decide              = 0;
  plugin->plugin_interface.get_conflict        = uf_plugin_get_conflict;
  plugin->plugin_interface.explain_propagation = 0;
  plugin->plugin_interface.explain_evaluation  = 0;
  plugin->plugin_interface.push                = uf_plugin_push;
  plugin->plugin_interface.pop                 = uf_plugin_pop;
  plugin->plugin_interface.gc_mark             = uf_plugin_gc_mark;
  plugin->plugin_interface.gc_sweep            = uf_plugin_gc_collect;
  return (plugin_t*) plugin;
}
