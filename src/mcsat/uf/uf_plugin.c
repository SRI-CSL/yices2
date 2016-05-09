/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "uf_plugin.h"

#include "mcsat/trail.h"
#include "mcsat/tracing.h"
#include "mcsat/watch_list_manager.h"

#include "utils/int_array_sort2.h"

typedef struct {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

  /** The watch list manager */
  watch_list_manager_t wlm;

  /** Next index of the trail to process */
  uint32_t trail_i;

} uf_plugin_t;

static
void uf_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  uf_plugin_t* eq = (uf_plugin_t*) plugin;

  watch_list_manager_construct(&eq->wlm, eq->ctx->var_db);

  eq->ctx = ctx;
  ctx->request_term_notification_by_kind(ctx, APP_TERM);
}

static
void uf_plugin_destruct(plugin_t* plugin) {
  uf_plugin_t* eq = (uf_plugin_t*) plugin;
  watch_list_manager_destruct(&eq->wlm);
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

/**
 * f(x_1, ..., x_n), with x assigned to v, mark this, and set f(x) as the
 * representative for all f(y) with y assigned to v. If one already exists, it
 * is returned.
 */
variable_t set_app_representative(uf_plugin_t* eq, variable_t app_term) {
  return app_term;
}

static
void uf_plugin_new_fun_application(uf_plugin_t* eq, term_t app_term, trail_token_t* prop) {

  uint32_t i;

  variable_db_t* var_db = eq->ctx->var_db;
  term_table_t* terms = eq->ctx->terms;
  const mcsat_trail_t* trail = eq->ctx->trail;

  // Variable of the application term
  variable_t app_term_var = variable_db_get_variable(var_db, app_term);

  // Get the children
  assert(term_kind(terms, app_term) == APP_TERM);
  int_mset_t arguments;
  int_mset_construct(&arguments, variable_null);
  composite_term_t* app_desc = app_term_desc(terms, app_term);
  uint32_t arity = app_desc->arity;
  for (i = 0; i < arity; ++ i) {
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
    variable_list_ref_t var_list = watch_list_manager_new_list(&eq->wlm, arguments_vars, size, app_term_var);

    // Add first variable to watch list
    watch_list_manager_add_to_watch(&eq->wlm, var_list, arguments_vars[0]);

    // Add second variable to watch list
    if (size > 1) {
      watch_list_manager_add_to_watch(&eq->wlm, var_list, arguments_vars[1]);
    }

    // Check the current status of the variables
    variable_t top_var = arguments_vars[0];
    is_fully_assigned = trail_has_value(trail, top_var);

  } else {
    // No variables => fully assigned
    is_fully_assigned = true;
  }

  if (is_fully_assigned) {
    set_app_representative(eq, app_term);
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

static
void uf_plugin_new_lemma_notify(plugin_t* plugin, ivector_t* lemma, trail_token_t* prop) {
  uf_plugin_t* eq = (uf_plugin_t*) plugin;
  (void)eq;
  (void)prop;
}

static
void uf_plugin_propagate(plugin_t* plugin, trail_token_t* prop) {

  uf_plugin_t* eq = (uf_plugin_t*) plugin;

  if (ctx_trace_enabled(eq->ctx, "uf_plugin")) {
    ctx_trace_printf(eq->ctx, "uf_plugin_propagate()\n");
  }

  // If we're not watching anything, we just ignore
  if (watch_list_manager_size(&eq->wlm) == 0) {
    return;
  }

  // Context
  const mcsat_trail_t* trail = eq->ctx->trail;
  variable_db_t* var_db = eq->ctx->var_db;

  // Propagate
  variable_t var;
  for(; trail_is_consistent(trail) && eq->trail_i < trail_size(trail); ++ eq->trail_i) {
    // Current trail element
    var = trail_at(trail, eq->trail_i);

    if (ctx_trace_enabled(eq->ctx, "uf_plugin")) {
      ctx_trace_printf(eq->ctx, "uf_plugin_propagate: ");
      ctx_trace_term(eq->ctx, variable_db_get_term(var_db, var));
    }

    // Go through all the variable lists (constraints) where we're watching var
    remove_iterator_t it;
    variable_list_ref_t var_list_ref;
    variable_t* var_list;
    variable_t* var_list_it;

    // Get the watch-list and process
    remove_iterator_construct(&it, &eq->wlm, var);
    while (trail_is_consistent(trail) && !remove_iterator_done(&it)) {

      // Get the current list where var appears
      var_list_ref = remove_iterator_get_list_ref(&it);
      var_list = watch_list_manager_get_list(&eq->wlm, var_list_ref);

      // f(x) variable
      variable_t app_var = watch_list_manager_get_constraint(&eq->wlm, var_list_ref);

      // Find a new watch (start from [1])
      var_list_it = var_list + 1;
      if (*var_list_it != variable_null) {
        for (++ var_list_it; *var_list_it != variable_null; ++ var_list_it) {
          if (!trail_has_value(trail, *var_list_it)) {
            // Swap with var_list[1]
            var_list[0] = *var_list_it;
            *var_list_it = var;
            // Add to new watch
            watch_list_manager_add_to_watch(&eq->wlm, var_list_ref, var_list[0]);
            // Don't watch this one
            remove_iterator_next_and_remove(&it);
            break;
          }
        }
      }

      if (*var_list_it == variable_null) {
        // We did not find a new watch so vars[1], ..., vars[n] are assigned
        variable_t rep_var = set_app_representative(eq, app_var);
        // If already has one, and both assigned to a value, check if it's the same value
        if (rep_var != app_var) {
          if (trail_has_value(trail, rep_var) && trail_has_value(trail, app_var)) {
            const mcsat_value_t* app_value = trail_get_value(trail, app_var);
            const mcsat_value_t* rep_value = trail_get_value(trail, rep_var);
            if (!mcsat_value_eq(app_value, rep_value)) {
              // TODO: Conflict
            }
          }
        }
        // Keep the watch, and continue
        remove_iterator_next_and_keep(&it);
      }
    }

    // Done, destruct the iterator
    remove_iterator_destruct(&it);
  }

  // TODO: expand all the conflicts with ackerman
}

static
void uf_plugin_decide(plugin_t* plugin, variable_t x, trail_token_t* decide, bool must) {
  // We don't decide
  assert(false);
}

static
void uf_plugin_get_conflict(plugin_t* plugin, ivector_t* conflict) {
  // Never any conflicts
  assert(false);
}

static
term_t uf_plugin_explain_propagation(plugin_t* plugin, variable_t x, ivector_t* reason) {
  uf_plugin_t* eq = (uf_plugin_t*) plugin;
  (void)eq;
  assert(false);
  return NULL_TERM;
}

static
bool uf_plugin_explain_evaluation(plugin_t* plugin, term_t t, int_mset_t* vars, mcsat_value_t* value) {
  uf_plugin_t* eq = (uf_plugin_t*) plugin;
  (void)eq;
  // Evaluate the equality
  assert(false);
  return true;
}

static
void uf_plugin_push(plugin_t* plugin) {
}

static
void uf_plugin_pop(plugin_t* plugin) {
}

static
void uf_plugin_gc_mark(plugin_t* plugin, gc_info_t* gc) {
}

static
void uf_plugin_gc_collect(plugin_t* plugin, const gc_info_t* gc) {
}

static
void uf_plugin_event_notify(plugin_t* plugin, plugin_notify_kind_t kind) {
  uf_plugin_t* eq = (uf_plugin_t*) plugin;
  (void)eq;

  switch (kind) {
  case MCSAT_SOLVER_START:
    break;
  case MCSAT_SOLVER_RESTART:
    break;
  case MCSAT_SOLVER_CONFLICT:
    break;
  default:
    assert(false);
  }
}

plugin_t* uf_plugin_allocator(void) {
  uf_plugin_t* plugin = safe_malloc(sizeof(uf_plugin_t));
  plugin_construct((plugin_t*) plugin);
  plugin->plugin_interface.construct           = uf_plugin_construct;
  plugin->plugin_interface.destruct            = uf_plugin_destruct;
  plugin->plugin_interface.new_term_notify     = uf_plugin_new_term_notify;
  plugin->plugin_interface.new_lemma_notify    = uf_plugin_new_lemma_notify;
  plugin->plugin_interface.event_notify        = uf_plugin_event_notify;
  plugin->plugin_interface.propagate           = uf_plugin_propagate;
  plugin->plugin_interface.decide              = uf_plugin_decide;
  plugin->plugin_interface.get_conflict        = uf_plugin_get_conflict;
  plugin->plugin_interface.explain_propagation = uf_plugin_explain_propagation;
  plugin->plugin_interface.explain_evaluation  = uf_plugin_explain_evaluation;
  plugin->plugin_interface.push                = uf_plugin_push;
  plugin->plugin_interface.pop                 = uf_plugin_pop;
  plugin->plugin_interface.gc_mark             = uf_plugin_gc_mark;
  plugin->plugin_interface.gc_sweep            = uf_plugin_gc_collect;
  return (plugin_t*) plugin;
}
