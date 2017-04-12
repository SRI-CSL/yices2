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

#include "bv_plugin.h"

#include "mcsat/trail.h"
#include "mcsat/tracing.h"
#include "mcsat/watch_list_manager.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/value.h"

#include "model/models.h"

#include "terms/terms.h"
#include "yices.h"

#include <cudd.h>

typedef struct {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

  /** Next index of the trail to process */
  uint32_t trail_i;

  /** Scope holder for the int variables */
  scope_holder_t scope;

  /** Conflict  */
  ivector_t conflict;

  /** Exception handler */
  jmp_buf* exception;

} bv_plugin_t;

static
void bv_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  bv->ctx = ctx;
  scope_holder_construct(&bv->scope);
  bv->trail_i = 0;

  // Terms
  ctx->request_term_notification_by_kind(ctx, BV_ARRAY);
  ctx->request_term_notification_by_kind(ctx, BV_DIV);
  ctx->request_term_notification_by_kind(ctx, BV_REM);
  ctx->request_term_notification_by_kind(ctx, BV_SDIV);
  ctx->request_term_notification_by_kind(ctx, BV_SREM);
  ctx->request_term_notification_by_kind(ctx, BV_SMOD);
  ctx->request_term_notification_by_kind(ctx, BV_SHL);
  ctx->request_term_notification_by_kind(ctx, BV_LSHR);
  ctx->request_term_notification_by_kind(ctx, BV_ASHR);
  ctx->request_term_notification_by_kind(ctx, BV_EQ_ATOM);
  ctx->request_term_notification_by_kind(ctx, BV_GE_ATOM);
  ctx->request_term_notification_by_kind(ctx, BV_SGE_ATOM);
  ctx->request_term_notification_by_kind(ctx, SELECT_TERM);
  ctx->request_term_notification_by_kind(ctx, BIT_TERM);

  // Types
  ctx->request_term_notification_by_type(ctx, BITVECTOR_TYPE);

  // Decisions
  ctx->request_decision_calls(ctx, BITVECTOR_TYPE);
}

static
void bv_plugin_destruct(plugin_t* plugin) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  scope_holder_destruct(&bv->scope);
}

static
void bv_plugin_new_term_notify(plugin_t* plugin, term_t t, trail_token_t* prop) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  if (ctx_trace_enabled(bv->ctx, "mcsat::new_term")) {
    ctx_trace_printf(bv->ctx, "bv_plugin_new_term_notify: ");
    ctx_trace_term(bv->ctx, t);
  }

  term_kind_t t_kind = term_kind(bv->ctx->terms, t);

  switch (t_kind) {
  case BV_ARRAY:
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR:
  case BV_EQ_ATOM:
  case BV_GE_ATOM:
  case BV_SGE_ATOM:
  case SELECT_TERM:
  case BIT_TERM:
    assert(false);
  default:
    // Noting for now
    break;
  }

}

static
void bv_plugin_propagate(plugin_t* plugin, trail_token_t* prop) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  (void) bv;

  // TODO
  assert(false);
}

static
void bv_plugin_push(plugin_t* plugin) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  // Pop the int variable values
  scope_holder_push(&bv->scope,
      &bv->trail_i,
      NULL);
}

static
void bv_plugin_pop(plugin_t* plugin) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;

  // Pop the int variable values
  scope_holder_pop(&bv->scope,
      &bv->trail_i,
      NULL);
}


static
void bv_plugin_decide(plugin_t* plugin, variable_t x, trail_token_t* decide, bool must) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  (void) bv;

  // TODO
  assert(false);
}

static
void bv_plugin_gc_mark(plugin_t* plugin, gc_info_t* gc_vars) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  (void) bv;

  // TODO
  assert(false);
}

static
void bv_plugin_gc_sweep(plugin_t* plugin, const gc_info_t* gc_vars) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  (void) bv;

  // TODO
  assert(false);
}

static
void bv_plugin_get_conflict(plugin_t* plugin, ivector_t* conflict) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  ivector_swap(conflict, &bv->conflict);
  ivector_reset(&bv->conflict);
}

static
term_t bv_plugin_explain_propagation(plugin_t* plugin, variable_t var, ivector_t* reasons) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  (void) bv;

  // TODO
  assert(false);

  return NULL_TERM;
}

static
bool bv_plugin_explain_evaluation(plugin_t* plugin, term_t t, int_mset_t* vars, mcsat_value_t* value) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  (void) bv;

  // TODO
  assert(false);

  return true;
}

static
void bv_plugin_set_exception_handler(plugin_t* plugin, jmp_buf* handler) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  bv->exception = handler;
}

static
void bv_plugin_build_model(plugin_t* plugin, model_t* model) {
  bv_plugin_t* bv = (bv_plugin_t*) plugin;
  (void) bv;

  // TODO
  assert(false);
}

plugin_t* bv_plugin_allocator(void) {
  bv_plugin_t* plugin = safe_malloc(sizeof(bv_plugin_t));
  plugin_construct((plugin_t*) plugin);
  plugin->plugin_interface.construct             = bv_plugin_construct;
  plugin->plugin_interface.destruct              = bv_plugin_destruct;
  plugin->plugin_interface.new_term_notify       = bv_plugin_new_term_notify;
  plugin->plugin_interface.new_lemma_notify      = 0;
  plugin->plugin_interface.event_notify          = 0;
  plugin->plugin_interface.propagate             = bv_plugin_propagate;
  plugin->plugin_interface.decide                = bv_plugin_decide;
  plugin->plugin_interface.get_conflict          = bv_plugin_get_conflict;
  plugin->plugin_interface.explain_propagation   = bv_plugin_explain_propagation;
  plugin->plugin_interface.explain_evaluation    = bv_plugin_explain_evaluation;
  plugin->plugin_interface.push                  = bv_plugin_push;
  plugin->plugin_interface.pop                   = bv_plugin_pop;
  plugin->plugin_interface.build_model           = bv_plugin_build_model;
  plugin->plugin_interface.gc_mark               = bv_plugin_gc_mark;
  plugin->plugin_interface.gc_sweep              = bv_plugin_gc_sweep;
  plugin->plugin_interface.set_exception_handler = bv_plugin_set_exception_handler;

  return (plugin_t*) plugin;
}
