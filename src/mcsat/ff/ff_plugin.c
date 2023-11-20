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

/*
 * Anything that includes "yices.h" requires these macros.
 * Otherwise the code doesn't build on Windows or Cygwin.
 */
#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include "mcsat/ff/ff_plugin.h"
#include "mcsat/ff/ff_plugin_internal.h"
#include "mcsat/ff/ff_plugin_explain.h"
#include "mcsat/tracing.h"

#include "utils/int_array_sort2.h"


static
void ff_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  // TODO implement
}

static
void ff_plugin_destruct(plugin_t* plugin) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  // TODO implement
}

static
void ff_plugin_new_term_notify(plugin_t* plugin, term_t t, trail_token_t* prop) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;
  term_table_t* terms = ff->ctx->terms;

  if (ctx_trace_enabled(ff->ctx, "mcsat::new_term")) {
    ctx_trace_printf(ff->ctx, "ff_plugin_new_term_notify: ");
    ctx_trace_term(ff->ctx, t);
  }

  assert(!is_neg_term(t));

  term_kind_t t_kind = term_kind(terms, t);

  // TODO implement
}

/**
 * Propagates the trail with BCP. When done, either the trail is fully
 * propagated, or the trail is in an inconsistent state.
 */
static
void ff_plugin_propagate(plugin_t* plugin, trail_token_t* prop) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  // TODO implement
}

static
void ff_plugin_decide(plugin_t* plugin, variable_t x, trail_token_t* decide_token, bool must) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  assert(variable_db_is_real(ff->ctx->var_db, x) || variable_db_is_int(ff->ctx->var_db, x));

  // TODO implement
}

static
void ff_plugin_get_conflict(plugin_t* plugin, ivector_t* conflict) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  if (ctx_trace_enabled(ff->ctx, "ff::conflict")) {
    ctx_trace_printf(ff->ctx, "ff_plugin_get_conflict(): START\n");
  }

  // TODO implement
}

static
term_t ff_plugin_explain_propagation(plugin_t* plugin, variable_t var, ivector_t* reasons) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  // TODO implement
}

static
bool ff_plugin_explain_evaluation(plugin_t* plugin, term_t t, int_mset_t* vars, mcsat_value_t* value) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  bool result = true;

  // TODO implement

  // All variables assigned
  return result;
}

static
void ff_plugin_push(plugin_t* plugin) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  // TODO implement
}

static
void ff_plugin_pop(plugin_t* plugin) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;
  const mcsat_trail_t* trail = ff->ctx->trail;

  // TODO implement
}

static
void ff_plugin_gc_mark(plugin_t* plugin, gc_info_t* gc_vars) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  // TODO implement
}

static
void ff_plugin_gc_sweep(plugin_t* plugin, const gc_info_t* gc_vars) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  // TODO implement
}

static
void ff_plugin_event_notify(plugin_t* plugin, plugin_notify_kind_t kind) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;
  (void)ff;

  switch (kind) {
    case MCSAT_SOLVER_START:
      // Re-initialize the heuristics
      break;
    case MCSAT_SOLVER_RESTART:
      // Check if clause compaction needed
      break;
    case MCSAT_SOLVER_CONFLICT:
      // Decay the scores each conflict
      break;
    case MCSAT_SOLVER_POP:
      // Not much to do
      break;
    default:
      assert(false);
  }
}

static
void ff_plugin_new_lemma_notify(plugin_t* plugin, ivector_t* lemma, trail_token_t* prop) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  // TODO implement
}

static
void ff_plugin_set_exception_handler(plugin_t* plugin, jmp_buf* handler) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;
  ff->exception = handler;
}

static
void ff_plugin_decide_assignment(plugin_t* plugin, variable_t x, const mcsat_value_t* value, trail_token_t* decide) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  // TODO implement
}

static
void ff_plugin_learn(plugin_t* plugin, trail_token_t* prop) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;
  const mcsat_trail_t* trail = ff->ctx->trail;

  if (ctx_trace_enabled(ff->ctx, "mcsat::ff::learn")) {
    ctx_trace_printf(ff->ctx, "ff_plugin_learn(): trail = ");
    trail_print(trail, ctx_trace_out(ff->ctx));
  }

  // TODO implement
}

bool ff_plugin_simplify_conflict_literal(plugin_t* plugin, term_t lit, ivector_t* output) {
  ff_plugin_t* ff = (ff_plugin_t*) plugin;

  uint32_t start = output->size;

  // TODO implement

  return true;
}

plugin_t* ff_plugin_allocator(void) {
  ff_plugin_t* plugin = safe_malloc(sizeof(ff_plugin_t));
  plugin_construct((plugin_t*) plugin);
  plugin->plugin_interface.construct           = ff_plugin_construct;
  plugin->plugin_interface.destruct            = ff_plugin_destruct;
//  plugin->plugin_interface.new_term_notify     = ff_plugin_new_term_notify;
//  plugin->plugin_interface.new_lemma_notify    = ff_plugin_new_lemma_notify;
//  plugin->plugin_interface.event_notify        = ff_plugin_event_notify;
//  plugin->plugin_interface.propagate           = ff_plugin_propagate;
//  plugin->plugin_interface.decide              = ff_plugin_decide;
//  plugin->plugin_interface.decide_assignment   = ff_plugin_decide_assignment;
//  plugin->plugin_interface.learn               = ff_plugin_learn;
//  plugin->plugin_interface.get_conflict        = ff_plugin_get_conflict;
//  plugin->plugin_interface.explain_propagation = ff_plugin_explain_propagation;
//  plugin->plugin_interface.explain_evaluation  = ff_plugin_explain_evaluation;
//  plugin->plugin_interface.simplify_conflict_literal = ff_plugin_simplify_conflict_literal;
//  plugin->plugin_interface.push                = ff_plugin_push;
//  plugin->plugin_interface.pop                 = ff_plugin_pop;
//  plugin->plugin_interface.gc_mark             = ff_plugin_gc_mark;
//  plugin->plugin_interface.gc_sweep            = ff_plugin_gc_sweep;
//  plugin->plugin_interface.set_exception_handler = ff_plugin_set_exception_handler;

  return (plugin_t*) plugin;
}
