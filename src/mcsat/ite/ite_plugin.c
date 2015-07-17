/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "mcsat/ite/ite_plugin.h"

#include "mcsat/tracing.h"

typedef struct {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

} ite_plugin_t;

void ite_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;

  ite->ctx = ctx;
  ctx->request_term_notification_by_kind(ctx, ITE_TERM);
}

void ite_plugin_destruct(plugin_t* plugin) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  (void)ite;
}

void ite_plugin_new_term_notify(plugin_t* plugin, term_t term, trail_token_t* prop) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  (void)ite;

  if (ctx_trace_enabled(ite->ctx, "mcsat::new_term")) {
    ctx_trace_printf(ite->ctx, "ite_plugin_new_term_notify: ");
    ctx_trace_term(ite->ctx, term);
  }
}

void ite_plugin_new_lemma_notify(plugin_t* plugin, ivector_t* lemma, trail_token_t* prop) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  (void)ite;
  (void)prop;
}

void ite_plugin_propagate(plugin_t* plugin, trail_token_t* prop) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  (void)ite;

}

void ite_plugin_decide(plugin_t* plugin, variable_t x, trail_token_t* decide, bool must) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  (void)ite;
  assert(false);
}

void ite_plugin_get_conflict(plugin_t* plugin, ivector_t* conflict) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  (void)ite;
}

term_t ite_plugin_explain_propagation(plugin_t* plugin, variable_t var, ivector_t* reason) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  (void)ite;
  assert(false);
  return NULL_TERM;
}

bool ite_plugin_explain_evaluation(plugin_t* plugin, term_t t, int_mset_t* vars, mcsat_value_t* value) {
  // Evaluate the branch that's true
  assert(false);
  return true;
}

static
void ite_plugin_push(plugin_t* plugin) {
}

static
void ite_plugin_pop(plugin_t* plugin) {
}

static
void ite_plugin_gc_mark(plugin_t* plugin, gc_info_t* gc) {
}

static
void ite_plugin_gc_collect(plugin_t* plugin, const gc_info_t* gc) {
}

static
void ite_plugin_event_notify(plugin_t* plugin, plugin_notify_kind_t kind) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  (void)ite;

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

plugin_t* ite_plugin_allocator() {
  ite_plugin_t* plugin = malloc(sizeof(ite_plugin_t));
  plugin_construct((plugin_t*) plugin);
  plugin->plugin_interface.construct           = ite_plugin_construct;
  plugin->plugin_interface.destruct            = ite_plugin_destruct;
  plugin->plugin_interface.new_term_notify     = ite_plugin_new_term_notify;
  plugin->plugin_interface.new_lemma_notify    = ite_plugin_new_lemma_notify;
  plugin->plugin_interface.event_notify        = ite_plugin_event_notify;
  plugin->plugin_interface.propagate           = ite_plugin_propagate;
  plugin->plugin_interface.decide              = ite_plugin_decide;
  plugin->plugin_interface.get_conflict        = ite_plugin_get_conflict;
  plugin->plugin_interface.explain_propagation = ite_plugin_explain_propagation;
  plugin->plugin_interface.explain_evaluation  = ite_plugin_explain_evaluation;
  plugin->plugin_interface.push                = ite_plugin_push;
  plugin->plugin_interface.pop                 = ite_plugin_pop;
  plugin->plugin_interface.gc_mark             = ite_plugin_gc_mark;
  plugin->plugin_interface.gc_sweep          = ite_plugin_gc_collect;
  return (plugin_t*) plugin;
}
