/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "mcsat/ite/ite_plugin.h"
#include "terms/term_manager.h"
#include "mcsat/tracing.h"

typedef struct {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

  /** A term manager */
  term_manager_t tm;

  /** Exception handler */
  jmp_buf* exception;

} ite_plugin_t;

void ite_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  ite->ctx = ctx;
  ctx->request_term_notification_by_kind(ctx, ITE_TERM);
  ctx->request_term_notification_by_kind(ctx, ITE_SPECIAL);
  init_term_manager(&ite->tm, ctx->terms);
  ite->tm.simplify_ite = false;
}

void ite_plugin_destruct(plugin_t* plugin) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  delete_term_manager(&ite->tm);
}

void ite_plugin_new_term_notify(plugin_t* plugin, term_t term, trail_token_t* prop) {
  ite_plugin_t* ite_plugin = (ite_plugin_t*) plugin;

  if (ctx_trace_enabled(ite_plugin->ctx, "mcsat::new_term")) {
    ctx_trace_printf(ite_plugin->ctx, "ite_plugin_new_term_notify: ");
    ctx_trace_term(ite_plugin->ctx, term);
  }

  assert(term_kind(ite_plugin->ctx->terms, term) == ITE_TERM || term_kind(ite_plugin->ctx->terms, term) == ITE_SPECIAL);

  // Ignore the Boolean ITE terms
  if (term_type_kind(ite_plugin->ctx->terms, term) == BOOL_TYPE) {
    return;
  }

  // Get the ITE parts
  composite_term_t* ite_desc = ite_term_desc(ite_plugin->ctx->terms, term);
  term_t c = ite_desc->arg[0];
  term_t t_true = ite_desc->arg[1];
  term_t t_false = ite_desc->arg[2];

  // Make the lemmas
  term_manager_t* tm = &ite_plugin->tm;
  term_t eq_true = arith_bineq_atom(ite_plugin->ctx->terms, term, t_true);
  term_t eq_false = arith_bineq_atom(ite_plugin->ctx->terms, term, t_false);
  term_t imp1 = mk_implies(tm, c, eq_true);
  term_t imp2 = mk_implies(tm, opposite_term(c), eq_false);
  term_t disj = mk_binary_or(tm, eq_true, eq_false);

  // Send off the lemmas
  prop->lemma(prop, imp1);
  prop->lemma(prop, imp2);
  prop->lemma(prop, disj);
}

static
void ite_plugin_set_exception_handler(plugin_t* plugin, jmp_buf* handler) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  ite->exception = handler;
}


plugin_t* ite_plugin_allocator(void) {
  ite_plugin_t* plugin = safe_malloc(sizeof(ite_plugin_t));
  plugin_construct((plugin_t*) plugin);
  plugin->plugin_interface.construct           = ite_plugin_construct;
  plugin->plugin_interface.destruct            = ite_plugin_destruct;
  plugin->plugin_interface.new_term_notify     = ite_plugin_new_term_notify;
  plugin->plugin_interface.new_lemma_notify    = 0;
  plugin->plugin_interface.event_notify        = 0;
  plugin->plugin_interface.propagate           = 0;
  plugin->plugin_interface.decide              = 0;
  plugin->plugin_interface.get_conflict        = 0;
  plugin->plugin_interface.explain_propagation = 0;
  plugin->plugin_interface.explain_evaluation  = 0;
  plugin->plugin_interface.push                = 0;
  plugin->plugin_interface.pop                 = 0;
  plugin->plugin_interface.gc_mark             = 0;
  plugin->plugin_interface.gc_sweep            = 0;
  plugin->plugin_interface.set_exception_handler = ite_plugin_set_exception_handler;

  return (plugin_t*) plugin;
}
