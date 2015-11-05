/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "mcsat/eq/eq_plugin.h"

#include "mcsat/bool/clause_db.h"
#include "mcsat/tracing.h"

typedef struct {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

} eq_plugin_t;

static
void eq_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  eq_plugin_t* eq_plugin = (eq_plugin_t*) plugin;

  eq_plugin->ctx = ctx;
  // ctx->request_term_notification_by_kind(ctx, EQ_TERM);
}

static
void eq_plugin_destruct(plugin_t* plugin) {
  eq_plugin_t* eq = (eq_plugin_t*) plugin;
  (void)eq;
}

static
void eq_plugin_new_term_notify(plugin_t* plugin, term_t term, trail_token_t* prop) {
  eq_plugin_t* eq = (eq_plugin_t*) plugin;

  if (ctx_trace_enabled(eq->ctx, "mcsat::new_term")) {
    ctx_trace_printf(eq->ctx, "eq_plugin_new_term_notify: ");
    ctx_trace_term(eq->ctx, term);
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
