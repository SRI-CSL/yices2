/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2025 SRI International.
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

#include "mcsat/cdclt/cdclt_plugin.h"

#include "mcsat/trail.h"
#include "mcsat/tracing.h"
#include "mcsat/utils/scope_holder.h"

#include "terms/terms.h"
#include "inttypes.h"

#include "yices.h"
#include "api/yices_api_lock_free.h"
#include "context/context.h"

/**
 * CDCLT plugin structure
 */
typedef struct {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

  /** Scope holder for variables */
  scope_holder_t scope;

  /** Yices CDCL(T) context */
  context_t* cdclt_ctx;

  /**  term to assumption map */
  int_hmap_t term2assump_map;

  /** assumption to term map */
  int_hmap_t assump2term_map; 

  /** Conflict vector */
  ivector_t conflict;

  /** assumption vector */
  ivector_t assump;

  /** do the CDCLT check or not */
  uint32_t check_limit;

  /** Next index of the trail to process */
  uint32_t trail_i;

  /** Statistics */
  struct {
    statistic_int_t* conflicts;
    statistic_int_t* checks;
  } stats;

  /** Exception handler */
  jmp_buf* exception;

} cdclt_plugin_t;

/**
 * Initialize statistics
 */
static
void cdclt_plugin_stats_init(cdclt_plugin_t* cdclt) {
  // Add statistics
  cdclt->stats.conflicts = statistics_new_int(cdclt->ctx->stats, "mcsat::cdclt::conflicts");
  cdclt->stats.checks = statistics_new_int(cdclt->ctx->stats, "mcsat::cdclt::checks");
}

/**
 * Construct the plugin
 */
static
void cdclt_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  cdclt_plugin_t* cdclt = (cdclt_plugin_t*) plugin;

  cdclt->ctx = ctx;

  scope_holder_construct(&cdclt->scope);
  
  ctx_config_t* config = yices_new_config();
  yices_set_config(config, "mode", "multi-checks");
  cdclt->cdclt_ctx = _o_yices_new_context(config);

  init_int_hmap(&cdclt->term2assump_map, 0);
  init_int_hmap(&cdclt->assump2term_map, 0);

  init_ivector(&cdclt->conflict, 0);
  init_ivector(&cdclt->assump, 0);

  cdclt->check_limit = 0;
  cdclt->trail_i = 0;

  // Request term notifications for
  ctx->request_term_notification_by_kind(ctx, EQ_TERM, false);
  //ctx->request_term_notification_by_kind(ctx, DISTINCT_TERM, false);
  
  //ctx->request_term_notification_by_kind(ctx, BV_EQ_ATOM, false);
  //ctx->request_term_notification_by_kind(ctx, BV_GE_ATOM, false);
  //ctx->request_term_notification_by_kind(ctx, BV_SGE_ATOM, false);

  //ctx->request_term_notification_by_kind(ctx, ARITH_GE_ATOM, false);
  //ctx->request_term_notification_by_kind(ctx, ARITH_IS_INT_ATOM, false);
  //ctx->request_term_notification_by_kind(ctx, ARITH_BINEQ_ATOM, false);
  
  // Initialize statistics
  cdclt_plugin_stats_init(cdclt);
}

/**
 * Destruct the plugin
 */
static
void cdclt_plugin_destruct(plugin_t* plugin) {
  cdclt_plugin_t* cdclt = (cdclt_plugin_t*) plugin;
  
  // Clean up scope holder
  scope_holder_destruct(&cdclt->scope);
  
  _o_yices_free_context(cdclt->cdclt_ctx);

  delete_int_hmap(&cdclt->term2assump_map);
  delete_int_hmap(&cdclt->assump2term_map);

  delete_ivector(&cdclt->conflict);
  delete_ivector(&cdclt->assump);
}

/**
 * Process a new term
 */
static
void cdclt_plugin_new_term_notify(plugin_t* plugin, term_t t, trail_token_t* prop) {
  cdclt_plugin_t* cdclt = (cdclt_plugin_t*) plugin;
  term_table_t* terms = cdclt->ctx->terms;

  if (cdclt->ctx->options->model_interpolation)
    return;
  
  if (ctx_trace_enabled(cdclt->ctx, "mcsat::new_term")) {
    ctx_trace_printf(cdclt->ctx, "cdclt_new_term_notify: ");
    ctx_trace_term(cdclt->ctx, t);
  }

  // Get the term kind
  term_kind_t t_kind = term_kind(terms, t);
  int_hmap_pair_t *t_assump = int_hmap_find(&cdclt->term2assump_map, t);
  term_t a, b;

  if (t_assump == NULL) {
    // Process based on term kind
    switch (t_kind) {
    case EQ_TERM:
    case DISTINCT_TERM:
    case BV_EQ_ATOM:
    case BV_GE_ATOM:
    case BV_SGE_ATOM:
      a = new_uninterpreted_term(terms, _o_yices_bool_type());
      b = new_uninterpreted_term(terms, _o_yices_bool_type());
      int_hmap_add(&cdclt->term2assump_map, t, a);
      int_hmap_add(&cdclt->assump2term_map, a, t);
      int_hmap_add(&cdclt->term2assump_map, _o_yices_not(t), b);
      int_hmap_add(&cdclt->assump2term_map, b, _o_yices_not(t));
      // assert a -> t in the cdclt solver
      _o_yices_assert_formula(cdclt->cdclt_ctx, _o_yices_implies(a, t));
      _o_yices_assert_formula(cdclt->cdclt_ctx, _o_yices_implies(b, _o_yices_not(t)));
      cdclt->check_limit++;
      break;
    case ARITH_GE_ATOM:
    case ARITH_IS_INT_ATOM:
    case ARITH_BINEQ_ATOM:
      // Do not handle arithmetic terms at the moment
      break;
    default:
      assert(false);
      break;
    }
  }
}

/**
 * Propagate using the current trail
 */
static
void cdclt_plugin_propagate(plugin_t* plugin, trail_token_t* prop) {
  cdclt_plugin_t* cdclt = (cdclt_plugin_t*) plugin;
  
  if (cdclt->ctx->options->model_interpolation)
    return;

  if (ctx_trace_enabled(cdclt->ctx, "cdclt")) {
    ctx_trace_printf(cdclt->ctx, "cdclt_propagate()\n");
  }
  
  ivector_reset(&cdclt->conflict);
  
  const mcsat_trail_t* trail = cdclt->ctx->trail;
  variable_db_t* var_db = cdclt->ctx->var_db;

  bool new_assump = false;
  for (; cdclt->trail_i < trail_size(trail); ++cdclt->trail_i) {
    variable_t x = trail_at(trail, cdclt->trail_i);
    
    if (variable_db_is_boolean(var_db, x)) {
      term_t x_term = x_term = variable_db_get_term(var_db, x);
      const mcsat_value_t* v = trail_get_value(trail, x);
      if (mcsat_value_is_false(v)) x_term = _o_yices_not(x_term);
      int_hmap_pair_t *x_term_assump = int_hmap_find(&cdclt->term2assump_map, x_term);
      if (x_term_assump != NULL) {
        new_assump = true;
        ivector_push(&cdclt->assump, x_term_assump->val);
      }
    }
  }

  if (new_assump && cdclt->assump.size > cdclt->check_limit) {
    if (ctx_trace_enabled(cdclt->ctx, "cdclt")) {
      ctx_trace_printf(cdclt->ctx, "cdclt_propagate::checking\n");
    } 
    
    smt_status_t result = _o_yices_check_context_with_assumptions(cdclt->cdclt_ctx, NULL, cdclt->assump.size, cdclt->assump.data);
    (*cdclt->stats.checks) ++;

    if (result == STATUS_UNSAT) {
      context_build_unsat_core(cdclt->cdclt_ctx, &cdclt->conflict);

      for (uint32_t i = 0; i < cdclt->conflict.size; ++i) {
        term_t a = cdclt->conflict.data[i];
        int_hmap_pair_t *t = int_hmap_get(&cdclt->assump2term_map, a);
        cdclt->conflict.data[i] = t->val;
      }

      // Report conflict
      prop->conflict(prop);
      (*cdclt->stats.conflicts) ++;
    
    } else {
      cdclt->check_limit++;
    }
  }
}

/**
 * Push the current state
 */
static
void cdclt_plugin_push(plugin_t* plugin) {
  cdclt_plugin_t* cdclt = (cdclt_plugin_t*) plugin;
  
  scope_holder_push(&cdclt->scope,
                    &cdclt->trail_i, &cdclt->assump.size,
                    NULL);
}

/**
 * Pop the current state
 */
static
void cdclt_plugin_pop(plugin_t* plugin) {
  cdclt_plugin_t* cdclt = (cdclt_plugin_t*) plugin;
  uint32_t assump_size;

  scope_holder_pop(&cdclt->scope,
                   &cdclt->trail_i, &assump_size,
                   NULL);

  ivector_shrink(&cdclt->assump, assump_size);
}

static
void cdclt_plugin_event_notify(plugin_t* plugin, plugin_notify_kind_t kind) {
  cdclt_plugin_t* cdclt = (cdclt_plugin_t*) plugin;

  switch (kind) {
  case MCSAT_SOLVER_START:
    // Re-initialize the heuristics
    cdclt->check_limit = 0;
    break;
  case MCSAT_SOLVER_RESTART:
    cdclt->check_limit--;
    break;
  case MCSAT_SOLVER_CONFLICT:
    break;
  case MCSAT_SOLVER_POP:
    cdclt->check_limit = 0;
    break;
  default:
    assert(false);
  }
}

/**
 * Get the conflict
 */
static
void cdclt_plugin_get_conflict(plugin_t* plugin, ivector_t* conflict) {
  cdclt_plugin_t* cdclt = (cdclt_plugin_t*) plugin;
  
  // Copy the conflict to the output vector
  ivector_swap(conflict, &cdclt->conflict);
  ivector_reset(&cdclt->conflict);
}

/**
 * Set the exception handler
 */
static
void cdclt_plugin_set_exception_handler(plugin_t* plugin, jmp_buf* handler) {
  cdclt_plugin_t* cdclt = (cdclt_plugin_t*) plugin;
  cdclt->exception = handler;
}

/**
 * Allocate a new CDCLT plugin
 */
plugin_t* cdclt_plugin_allocator(void) {
  cdclt_plugin_t* plugin = safe_malloc(sizeof(cdclt_plugin_t));
  plugin_construct((plugin_t*) plugin);
  plugin->plugin_interface.construct = cdclt_plugin_construct;
  plugin->plugin_interface.destruct = cdclt_plugin_destruct;
  plugin->plugin_interface.new_term_notify = cdclt_plugin_new_term_notify;
  plugin->plugin_interface.event_notify = cdclt_plugin_event_notify;
  plugin->plugin_interface.propagate = cdclt_plugin_propagate;
  plugin->plugin_interface.get_conflict = cdclt_plugin_get_conflict;
  plugin->plugin_interface.push = cdclt_plugin_push;
  plugin->plugin_interface.pop = cdclt_plugin_pop;
  plugin->plugin_interface.set_exception_handler = cdclt_plugin_set_exception_handler;

  return (plugin_t*) plugin;
} 