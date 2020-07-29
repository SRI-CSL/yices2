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
 
#include "mcsat/ite/ite_plugin.h"
#include "terms/term_manager.h"
#include "mcsat/tracing.h"

typedef struct {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

  /** Exception handler */
  jmp_buf* exception;

} ite_plugin_t;

void ite_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  ite_plugin_t* ite = (ite_plugin_t*) plugin;
  ite->ctx = ctx;
  ctx->request_term_notification_by_kind(ctx, ITE_TERM, false);
  ctx->request_term_notification_by_kind(ctx, ITE_SPECIAL, false);
}

void ite_plugin_destruct(plugin_t* plugin) {
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
  term_manager_t* tm = ite_plugin->ctx->tm;
  term_t eq_true = mk_eq(tm, term, t_true);
  term_t eq_false = mk_eq(tm, term, t_false);
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
  plugin->plugin_interface.new_lemma_notify    = NULL;
  plugin->plugin_interface.event_notify        = NULL;
  plugin->plugin_interface.propagate           = NULL;
  plugin->plugin_interface.decide              = NULL;
  plugin->plugin_interface.decide_assignment   = NULL;
  plugin->plugin_interface.get_conflict        = NULL;
  plugin->plugin_interface.explain_propagation = NULL;
  plugin->plugin_interface.explain_evaluation  = NULL;
  plugin->plugin_interface.push                = NULL;
  plugin->plugin_interface.pop                 = NULL;
  plugin->plugin_interface.gc_mark             = NULL;
  plugin->plugin_interface.gc_sweep            = NULL;
  plugin->plugin_interface.set_exception_handler = ite_plugin_set_exception_handler;

  return (plugin_t*) plugin;
}
