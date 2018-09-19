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

#include "uf_plugin.h"

#include "mcsat/trail.h"
#include "mcsat/tracing.h"
#include "mcsat/watch_list_manager.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/value.h"

#include "mcsat/eq/equality_graph.h"

#include "utils/int_array_sort2.h"
#include "utils/ptr_array_sort2.h"
#include "model/models.h"

#include "terms/terms.h"

#include "inttypes.h"

typedef struct {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

  /** Scope holder for the int variables */
  scope_holder_t scope;

  /** Conflict  */
  ivector_t conflict;

  /** The term manager (no ITE simplification) */
  term_manager_t* tm;

  /** Equality graph */
  eq_graph_t eq_graph;

  /** Stuff added to eq_graph */
  ivector_t eq_graph_addition_trail;

  struct {
    uint32_t* egraph_terms;
    uint32_t* propagations;
    uint32_t* conflicts;
  } stats;

  /** Exception handler */
  jmp_buf* exception;

} uf_plugin_t;

static
void uf_plugin_stats_init(uf_plugin_t* uf) {
  // Add statistics
  uf->stats.propagations = statistics_new_uint32(uf->ctx->stats, "mcsat::uf::propagations");
  uf->stats.conflicts = statistics_new_uint32(uf->ctx->stats, "mcsat::uf::conflicts");
  uf->stats.egraph_terms = statistics_new_uint32(uf->ctx->stats, "mcsat::uf::egraph_terms");
}

static
void uf_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  uf->ctx = ctx;

  scope_holder_construct(&uf->scope);
  init_ivector(&uf->conflict, 0);

  // Terms
  ctx->request_term_notification_by_kind(ctx, APP_TERM);
  ctx->request_term_notification_by_kind(ctx, ARITH_RDIV);
  ctx->request_term_notification_by_kind(ctx, ARITH_IDIV);
  ctx->request_term_notification_by_kind(ctx, ARITH_MOD);
  ctx->request_term_notification_by_kind(ctx, EQ_TERM);

  // Types
  ctx->request_term_notification_by_type(ctx, UNINTERPRETED_TYPE);

  // Decisions
  ctx->request_decision_calls(ctx, UNINTERPRETED_TYPE);

  // Equality graph
  eq_graph_construct(&uf->eq_graph, ctx, "uf");
  init_ivector(&uf->eq_graph_addition_trail, 0);

  // Term manager
  uf->tm = &ctx->var_db->tm;

  // stats
  uf_plugin_stats_init(uf);
}

static
void uf_plugin_destruct(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;
  scope_holder_destruct(&uf->scope);
  delete_ivector(&uf->conflict);
  eq_graph_destruct(&uf->eq_graph);
  delete_ivector(&uf->eq_graph_addition_trail);
}

static
void uf_plugin_process_eq_graph_propagations(uf_plugin_t* uf, trail_token_t* prop) {
  // Process any propagated terms
  if (eq_graph_has_propagated_terms(&uf->eq_graph)) {
    uint32_t i = 0;
    ivector_t eq_propagations;
    init_ivector(&eq_propagations, 0);
    eq_graph_get_propagated_terms(&uf->eq_graph, &eq_propagations);
    for (; trail_is_consistent(uf->ctx->trail) && i < eq_propagations.size; ++ i) {
      term_t t = eq_propagations.data[i];
      variable_t t_var = variable_db_get_variable_if_exists(uf->ctx->var_db, t);
      if (t_var != variable_null && !trail_has_value(uf->ctx->trail, t_var)) {
        const mcsat_value_t* v = eq_graph_get_propagated_term_value(&uf->eq_graph, t);
        if (ctx_trace_enabled(uf->ctx, "mcsat::eq::propagate")) {
          ctx_trace_term(uf->ctx, t);
          fprintf(ctx_trace_out(uf->ctx), " -> ");
          mcsat_value_print(v, ctx_trace_out(uf->ctx));
          fprintf(ctx_trace_out(uf->ctx), "\n");
        }
        prop->add(prop, t_var, v);
      }
    }
    delete_ivector(&eq_propagations);
  }
}

static
void uf_plugin_add_to_eq_graph(uf_plugin_t* uf, term_t t, bool record) {

  term_table_t* terms = uf->ctx->terms;

  // The kind
  term_kind_t t_kind = term_kind(terms, t);

  // Add to equality graph
  composite_term_t* t_desc = NULL;
  uint32_t children_start = 0;
  switch (t_kind) {
  case APP_TERM:
    t_desc = app_term_desc(terms, t);
    eq_graph_add_ufun_term(&uf->eq_graph, t, t_desc->arg[0], t_desc->arity - 1, t_desc->arg + 1);
    children_start = 1;
    break;
  case ARITH_RDIV:
    t_desc = arith_rdiv_term_desc(terms, t);
    eq_graph_add_ifun_term(&uf->eq_graph, t, ARITH_RDIV, 2, t_desc->arg);
    break;
  case ARITH_IDIV:
    t_desc = arith_idiv_term_desc(terms, t);
    eq_graph_add_ifun_term(&uf->eq_graph, t, ARITH_IDIV, 2, t_desc->arg);
    break;
  case ARITH_MOD:
    t_desc = arith_mod_term_desc(terms, t);
    eq_graph_add_ifun_term(&uf->eq_graph, t, ARITH_MOD, 2, t_desc->arg);
    break;
  case EQ_TERM:
    t_desc = eq_term_desc(terms, t);
    eq_graph_add_ifun_term(&uf->eq_graph, t, EQ_TERM, 2, t_desc->arg);
    break;
  default:
    assert(false);
  }

  // Make sure the subterms are registered
  uint32_t i;
  for (i = children_start; i < t_desc->arity; ++ i) {
    term_t c = t_desc->arg[i];
    variable_db_get_variable(uf->ctx->var_db, c);
  }

  // Record addition so we can re-add on backtracks
  if (record) {
    (*uf->stats.egraph_terms) ++;
    ivector_push(&uf->eq_graph_addition_trail, t);
  }
}


static
void uf_plugin_new_term_notify(plugin_t* plugin, term_t t, trail_token_t* prop) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  if (ctx_trace_enabled(uf->ctx, "mcsat::new_term")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_new_term_notify: ");
    ctx_trace_term(uf->ctx, t);
  }

  term_kind_t t_kind = term_kind(uf->ctx->terms, t);

  switch (t_kind) {
  case ARITH_MOD:
  case ARITH_IDIV:
  case ARITH_RDIV:
  case APP_TERM:
  case EQ_TERM:
    // Application terms (or other terms we treat as uninterpreted)
    uf_plugin_add_to_eq_graph(uf, t, true);
    break;
  default:
    // All other is of uninterpreted sort, and we treat as variables
    break;
  }

}

static
void uf_plugin_propagate(plugin_t* plugin, trail_token_t* prop) {

  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_propagate()\n");
  }

  // If we're not watching anything, we just ignore
  if (eq_graph_term_size(&uf->eq_graph) == 0) {
    return;
  }

  // Propagate known terms
  eq_graph_propagate_trail(&uf->eq_graph);

  // Check for conflicts
  if (uf->eq_graph.in_conflict) {
    // Report conflict
    prop->conflict(prop);
    (*uf->stats.conflicts) ++;
    // Construct the conflict
    eq_graph_get_conflict(&uf->eq_graph, &uf->conflict, NULL);
  } else {
    uf_plugin_process_eq_graph_propagations(uf, prop);
  }
}

static
void uf_plugin_push(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  // Pop the int variable values
  scope_holder_push(&uf->scope,
      &uf->eq_graph_addition_trail.size,
      NULL);

  eq_graph_push(&uf->eq_graph);
}

static
void uf_plugin_pop(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  uint32_t old_eq_graph_addition_trail_size;

  // Pop the int variable values
  scope_holder_pop(&uf->scope,
      &old_eq_graph_addition_trail_size,
      NULL);

  eq_graph_pop(&uf->eq_graph);

  // Re-add all the terms to eq graph
  uint32_t i;
  for (i = old_eq_graph_addition_trail_size; i < uf->eq_graph_addition_trail.size; ++ i) {
    term_t t = uf->eq_graph_addition_trail.data[i];
    uf_plugin_add_to_eq_graph(uf, t, false);
  }
}

bool value_cmp(void* data, void* v1_void, void* v2_void) {

  const mcsat_value_t* v1 = (mcsat_value_t*) v1_void;
  const mcsat_value_t* v2 = (mcsat_value_t*) v2_void;

  assert(v1->type == VALUE_RATIONAL);
  assert(v2->type == VALUE_RATIONAL);

  return q_cmp(&v1->q, &v2->q) < 0;
}

static
void uf_plugin_decide(plugin_t* plugin, variable_t x, trail_token_t* decide, bool must) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_decide: ");
    ctx_trace_term(uf->ctx, variable_db_get_term(uf->ctx->var_db, x));
  }

  assert(eq_graph_is_trail_propagated(&uf->eq_graph));

  // Get the cached value
  const mcsat_value_t* x_cached_value = NULL;
  if (trail_has_cached_value(uf->ctx->trail, x)) {
    x_cached_value = trail_get_cached_value(uf->ctx->trail, x);
  }

  // Pick a value not in the forbidden set
  term_t x_term = variable_db_get_term(uf->ctx->var_db, x);
  pvector_t forbidden;
  init_pvector(&forbidden, 0);
  bool cache_ok = eq_graph_get_forbidden(&uf->eq_graph, x_term, &forbidden, x_cached_value) && x_cached_value != NULL;

  int32_t picked_value = 0;
  if (!cache_ok) {
    // Get the actual value (pick smallest not in list)
    ptr_array_sort2(forbidden.data, forbidden.size, NULL, value_cmp);
    uint32_t i;
    for (i = 0; i < forbidden.size; ++ i) {
      const mcsat_value_t* v = forbidden.data[i];
      assert(v->type == VALUE_RATIONAL);
      int32_t v_int = 0;
      bool ok = q_get32((rational_t*)&v->q, &v_int);
      (void) ok;
      assert(ok);
      if (picked_value < v_int) {
        break; // Can use
      } else {
        ++ picked_value; // Try next value
      }
    }
  } else {
    assert(x_cached_value->type == VALUE_RATIONAL);
    bool ok = q_get32((rational_t*)&x_cached_value->q, &picked_value);
    (void) ok;
    assert(ok);
  }

  // Remove temp
  delete_pvector(&forbidden);

  // Make the yices rational
  rational_t q;
  q_init(&q);
  q_set32(&q, picked_value);

  // Make the mcsat value
  mcsat_value_t value;
  mcsat_value_construct_rational(&value, &q);

  // Set the value
  decide->add(decide, x, &value);

  // Remove temps
  mcsat_value_destruct(&value);
  q_clear(&q);
}

static
void uf_plugin_gc_mark(plugin_t* plugin, gc_info_t* gc_vars) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  // Mark all asserted stuff, and all the children of marked stuff
  eq_graph_gc_mark(&uf->eq_graph, gc_vars);
}

static
void uf_plugin_gc_sweep(plugin_t* plugin, const gc_info_t* gc_vars) {
  // Should be nothing!
}

static
void uf_plugin_get_conflict(plugin_t* plugin, ivector_t* conflict) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;
  ivector_swap(conflict, &uf->conflict);
  ivector_reset(&uf->conflict);
}

static
term_t uf_plugin_explain_propagation(plugin_t* plugin, variable_t var, ivector_t* reasons) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  term_t var_term = variable_db_get_term(uf->ctx->var_db, var);

  if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_explain_propagation():\n");
    ctx_trace_term(uf->ctx, var_term);
    ctx_trace_printf(uf->ctx, "var = %"PRIu32"\n", var);
  }

  return eq_graph_explain_term_propagation(&uf->eq_graph, var_term, reasons, NULL);
}

static
bool uf_plugin_explain_evaluation(plugin_t* plugin, term_t t, int_mset_t* vars, mcsat_value_t* value) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  term_table_t* terms = uf->ctx->terms;
  variable_db_t* var_db = uf->ctx->var_db;
  const mcsat_trail_t* trail = uf->ctx->trail;

  if (value == NULL) {

    // Get all the variables and make sure they are all assigned.
    term_t atom = unsigned_term(t);
    assert(term_kind(terms, atom) == EQ_TERM);
    composite_term_t* eq_desc = eq_term_desc(terms, atom);

    term_t lhs_term = eq_desc->arg[0];
    term_t rhs_term = eq_desc->arg[1];
    variable_t lhs_var = variable_db_get_variable_if_exists(var_db, lhs_term);
    variable_t rhs_var = variable_db_get_variable_if_exists(var_db, rhs_term);
    assert(lhs_var != variable_null);
    assert(rhs_var != variable_null);

    // Check if both are assigned
    if (!trail_has_value(trail, lhs_var)) { return false; }
    if (!trail_has_value(trail, rhs_var)) { return false; }

    int_mset_add(vars, lhs_var);
    int_mset_add(vars, rhs_var);

    // Both variables assigned, we evaluate
    return true;

  } else {
    // We don't propagate values (yet)
    assert(false);
  }

  return true;
}

static
void uf_plugin_set_exception_handler(plugin_t* plugin, jmp_buf* handler) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;
  uf->exception = handler;
}

typedef struct {
  term_table_t* terms;
  variable_db_t* var_db;
} model_sort_data_t;


//static
//bool uf_plugin_build_model_compare(void *data, variable_t t1_var, variable_t t2_var) {
//  model_sort_data_t* ctx = (model_sort_data_t*) data;
//  term_t t1 = variable_db_get_term(ctx->var_db, t1_var);
//  term_t t2 = variable_db_get_term(ctx->var_db, t2_var);
//  int32_t t1_app = app_reps_get_uf(ctx->terms, t1);
//  int32_t t2_app = app_reps_get_uf(ctx->terms, t2);
//  if (t1_app == t2_app) {
//    return t1 < t2;
//  }
//  return t1_app < t2_app;
//}

static
void uf_plugin_build_model(plugin_t* plugin, model_t* model) {
//  uf_plugin_t* uf = (uf_plugin_t*) plugin;
//
//  term_table_t* terms = uf->ctx->terms;
//  type_table_t* types = uf->ctx->types;
//  value_table_t* values = &model->vtbl;
//  variable_db_t* var_db = uf->ctx->var_db;
//  const mcsat_trail_t* trail = uf->ctx->trail;
//
//  // Data for sorting
//  model_sort_data_t sort_ctx;
//  sort_ctx.terms = terms;
//  sort_ctx.var_db = var_db;
//
//  // Sort the representatives by function used: we get a list of function
//  // applications where we can easily collect them by linear scan
//  ivector_t app_reps;
//  init_ivector(&app_reps, uf->app_reps_with_val_rep.size);
//  ivector_copy(&app_reps, uf->app_reps_with_val_rep.data, uf->app_reps_with_val_rep.size);
//  int_array_sort2(app_reps.data, app_reps.size, &sort_ctx, uf_plugin_build_model_compare);
//
//  // Mappings that we collect for a single function
//  ivector_t mappings;
//  init_ivector(&mappings, 0);
//
//  // Temp for arguments of a one concrete mapping
//  ivector_t arguments;
//  init_ivector(&arguments, 0);
//
//  // Got through all the representatives that have a set value and
//  // - while same function, collect the concrete mappings
//  // - if different function, construct the function and add to model
//  uint32_t i;
//  int32_t app_f, prev_app_f = 0;  // Current and previous function symbol
//  term_t app_term, prev_app_term; // Current and previous function application term
//  variable_t app_var;        // Current function application term variable
//  type_t app_type;           // Current function application term type
//  for (i = 0, prev_app_term = NULL_TERM; i < app_reps.size; ++ i) {
//
//    // Current representative application
//    app_var = app_reps.data[i];
//    app_term = variable_db_get_term(var_db, app_var);
//    app_type = term_type(terms, app_term);
//
//    if (ctx_trace_enabled(uf->ctx, "uf_plugin::model")) {
//      ctx_trace_printf(uf->ctx, "processing app rep:");
//      ctx_trace_term(uf->ctx, app_term);
//    }
//
//    // Current function symbol
//    app_f = app_reps_get_uf(terms, app_term);
//    composite_term_t* app_comp = app_reps_get_uf_descriptor(uf->ctx->terms, app_term);
//
//    // For division operators, we only use the ones that divide by 0
//    if (app_f < 0) {
//      assert(app_comp->arity == 2);
//      term_t divisor_term = app_comp->arg[1];
//      variable_t divisor_var = variable_db_get_variable(var_db, divisor_term);
//      const mcsat_value_t* divisor_value = trail_get_value(trail, divisor_var);
//      if (!mcsat_value_is_zero(divisor_value)) {
//        continue;
//      }
//    }
//
//    // If we changed the function, construct the previous one
//    if (prev_app_term != NULL_TERM && app_f != prev_app_f) {
//      type_t tau = app_reps_get_uf_type(&uf->app_reps, prev_app_term);
//      value_t f_value = vtbl_mk_function(values, tau, mappings.size, mappings.data, vtbl_mk_unknown(values));
//      if (prev_app_f < 0) {
//        // Arithmetic stuffs
//        switch (prev_app_f) {
//        case APP_REP_IDIV_ID:
//          vtbl_set_zero_idiv(values, f_value);
//          break;
//        case APP_REP_RDIV_ID:
//          vtbl_set_zero_rdiv(values, f_value);
//          break;
//        case APP_REP_MOD_ID:
//          vtbl_set_zero_mod(values, f_value);
//          break;
//        }
//      } else {
//        // Regular UF function
//        model_map_term(model, prev_app_f, f_value);
//      }
//      ivector_reset(&mappings);
//    }
//
//    // Next concrete mapping f : (x1, x2, ..., xn) -> v
//    // a) Get the v value
//    mcsat_value_t* v_mcsat = (mcsat_value_t*) trail_get_value(trail, app_var);
//    assert(v_mcsat->type != VALUE_NONE);
//    value_t v = mcsat_value_to_value(v_mcsat, types, app_type, values);
//    // b) Get the argument values
//    uint32_t arg_i;
//    uint32_t arg_start = app_reps_get_uf_start(uf->ctx->terms, app_term);
//    uint32_t arg_end = app_f < 0 ? app_comp->arity - 1 : app_comp->arity;
//    ivector_reset(&arguments);
//    for (arg_i = arg_start; arg_i < arg_end; ++ arg_i) {
//      term_t arg_term = app_comp->arg[arg_i];
//      type_t arg_type = term_type(terms, arg_term);
//      variable_t arg_var = variable_db_get_variable(var_db, arg_term);
//      v_mcsat = (mcsat_value_t*) trail_get_value(trail, arg_var);
//      assert(v_mcsat->type != VALUE_NONE);
//      value_t arg_v = mcsat_value_to_value(v_mcsat, types, arg_type, values);
//      ivector_push(&arguments, arg_v);
//    }
//    // c) Construct the concrete mapping, and save in the list for f
//    value_t map_value = vtbl_mk_map(values, arguments.size, arguments.data, v);
//    ivector_push(&mappings, map_value);
//
//    // Remember the previous one
//    prev_app_f = app_f;
//    prev_app_term = app_term;
//  }
//
//  if (app_reps.size > 0 && mappings.size > 0) {
//    // Construct the last function
//    type_t tau = app_reps_get_uf_type(&uf->app_reps, app_term);
//    value_t f_value = vtbl_mk_function(values, tau, mappings.size, mappings.data, vtbl_mk_unknown(values));
//    if (app_f < 0) {
//      // Arithmetic stuffs
//      switch (app_f) {
//      case APP_REP_IDIV_ID:
//        vtbl_set_zero_idiv(values, f_value);
//        break;
//      case APP_REP_RDIV_ID:
//        vtbl_set_zero_rdiv(values, f_value);
//        break;
//      case APP_REP_MOD_ID:
//        vtbl_set_zero_mod(values, f_value);
//        break;
//      }
//    } else {
//      // Regular UF function
//      model_map_term(model, app_f, f_value);
//    }
//  }
//
//  // Remove temps
//  delete_ivector(&arguments);
//  delete_ivector(&mappings);
//  delete_ivector(&app_reps);
}

plugin_t* uf_plugin_allocator(void) {
  uf_plugin_t* plugin = safe_malloc(sizeof(uf_plugin_t));
  plugin_construct((plugin_t*) plugin);
  plugin->plugin_interface.construct             = uf_plugin_construct;
  plugin->plugin_interface.destruct              = uf_plugin_destruct;
  plugin->plugin_interface.new_term_notify       = uf_plugin_new_term_notify;
  plugin->plugin_interface.new_lemma_notify      = 0;
  plugin->plugin_interface.event_notify          = 0;
  plugin->plugin_interface.propagate             = uf_plugin_propagate;
  plugin->plugin_interface.decide                = uf_plugin_decide;
  plugin->plugin_interface.get_conflict          = uf_plugin_get_conflict;
  plugin->plugin_interface.explain_propagation   = uf_plugin_explain_propagation;
  plugin->plugin_interface.explain_evaluation    = uf_plugin_explain_evaluation;
  plugin->plugin_interface.push                  = uf_plugin_push;
  plugin->plugin_interface.pop                   = uf_plugin_pop;
  plugin->plugin_interface.build_model           = uf_plugin_build_model;
  plugin->plugin_interface.gc_mark               = uf_plugin_gc_mark;
  plugin->plugin_interface.gc_sweep              = uf_plugin_gc_sweep;
  plugin->plugin_interface.set_exception_handler = uf_plugin_set_exception_handler;

  return (plugin_t*) plugin;
}
