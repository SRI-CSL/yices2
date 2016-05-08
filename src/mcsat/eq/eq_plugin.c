/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "mcsat/eq/eq_plugin.h"

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

} eq_plugin_t;

static
void eq_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  eq_plugin_t* eq_plugin = (eq_plugin_t*) plugin;

  eq_plugin->ctx = ctx;
  ctx->request_term_notification_by_kind(ctx, APP_TERM);
}

static
void eq_plugin_destruct(plugin_t* plugin) {
  eq_plugin_t* eq = (eq_plugin_t*) plugin;
  (void)eq;
}

static
bool eq_plugin_trail_variable_compare(void *data, variable_t t1, variable_t t2) {
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
void eq_plugin_new_fun_application(eq_plugin_t* eq, term_t app_term, trail_token_t* prop) {

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
    int_array_sort2(arguments_vars, size, (void*) trail, eq_plugin_trail_variable_compare);

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
    // TODO: mark it
  }
}

static
void eq_plugin_new_term_notify(plugin_t* plugin, term_t t, trail_token_t* prop) {
  eq_plugin_t* eq = (eq_plugin_t*) plugin;

  if (ctx_trace_enabled(eq->ctx, "mcsat::new_term")) {
    ctx_trace_printf(eq->ctx, "eq_plugin_new_term_notify: ");
    ctx_trace_term(eq->ctx, t);
  }

  term_kind_t t_kind = term_kind(eq->ctx->terms, t);

  switch (t_kind) {
  case APP_TERM:
    // We just care about the application terms
    eq_plugin_new_fun_application(eq, t, prop);
    break;
  default:
    // Noting for now
    break;
  }

}

static
void eq_plugin_new_lemma_notify(plugin_t* plugin, ivector_t* lemma, trail_token_t* prop) {
  eq_plugin_t* eq = (eq_plugin_t*) plugin;
  (void)eq;
  (void)prop;
}

static
void eq_plugin_propagate(plugin_t* plugin, trail_token_t* prop) {
  eq_plugin_t* eq = (eq_plugin_t*) plugin;
  (void)eq;
}

static
void eq_plugin_decide(plugin_t* plugin, variable_t x, trail_token_t* decide, bool must) {
  eq_plugin_t* eq = (eq_plugin_t*) plugin;
  (void)eq;
}

static
void eq_plugin_get_conflict(plugin_t* plugin, ivector_t* conflict) {
  eq_plugin_t* eq = (eq_plugin_t*) plugin;
  (void)eq;
  assert(false);
}

static
term_t eq_plugin_explain_propagation(plugin_t* plugin, variable_t x, ivector_t* reason) {
  eq_plugin_t* eq = (eq_plugin_t*) plugin;
  (void)eq;
  assert(false);
  return NULL_TERM;
}

static
bool eq_plugin_explain_evaluation(plugin_t* plugin, term_t t, int_mset_t* vars, mcsat_value_t* value) {
  eq_plugin_t* eq = (eq_plugin_t*) plugin;
  (void)eq;
  // Evaluate the equality
  assert(false);
  return true;
}

static
void eq_plugin_push(plugin_t* plugin) {
}

static
void eq_plugin_pop(plugin_t* plugin) {
}

static
void eq_plugin_gc_mark(plugin_t* plugin, gc_info_t* gc) {
}

static
void eq_plugin_gc_collect(plugin_t* plugin, const gc_info_t* gc) {
}

static
void eq_plugin_event_notify(plugin_t* plugin, plugin_notify_kind_t kind) {
  eq_plugin_t* eq = (eq_plugin_t*) plugin;
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

plugin_t* eq_plugin_allocator(void) {
  eq_plugin_t* plugin = safe_malloc(sizeof(eq_plugin_t));
  plugin_construct((plugin_t*) plugin);
  plugin->plugin_interface.construct           = eq_plugin_construct;
  plugin->plugin_interface.destruct            = eq_plugin_destruct;
  plugin->plugin_interface.new_term_notify     = eq_plugin_new_term_notify;
  plugin->plugin_interface.new_lemma_notify    = eq_plugin_new_lemma_notify;
  plugin->plugin_interface.event_notify        = eq_plugin_event_notify;
  plugin->plugin_interface.propagate           = eq_plugin_propagate;
  plugin->plugin_interface.decide              = eq_plugin_decide;
  plugin->plugin_interface.get_conflict        = eq_plugin_get_conflict;
  plugin->plugin_interface.explain_propagation = eq_plugin_explain_propagation;
  plugin->plugin_interface.explain_evaluation  = eq_plugin_explain_evaluation;
  plugin->plugin_interface.push                = eq_plugin_push;
  plugin->plugin_interface.pop                 = eq_plugin_pop;
  plugin->plugin_interface.gc_mark             = eq_plugin_gc_mark;
  plugin->plugin_interface.gc_sweep          = eq_plugin_gc_collect;
  return (plugin_t*) plugin;
}
