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
#include "mcsat/weq/weak_eq_graph.h"

#include "utils/int_array_sort2.h"
#include "utils/ptr_array_sort2.h"
#include "utils/int_hash_sets.h"

#include "model/models.h"

#include "terms/terms.h"
#include "inttypes.h"


#define DECIDE_FUNCTION_VALUE_START UINT32_MAX/64


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

  /** Weak Equality graph for array reasoning */
  weq_graph_t weq_graph;

  /** Function Values that have been used */
  int_hset_t fun_used_values;

  /** Tmp vector */
  int_mset_t tmp;

  struct {
    statistic_int_t* egraph_terms;
    statistic_int_t* propagations;
    statistic_int_t* conflicts;
    statistic_avg_t* avg_conflict_size;
    statistic_avg_t* avg_explanation_size;
  } stats;

  /** Exception handler */
  jmp_buf* exception;

} uf_plugin_t;


static
void uf_plugin_stats_init(uf_plugin_t* uf) {
  // Add statistics
  uf->stats.propagations = statistics_new_int(uf->ctx->stats, "mcsat::uf::propagations");
  uf->stats.conflicts = statistics_new_int(uf->ctx->stats, "mcsat::uf::conflicts");
  uf->stats.egraph_terms = statistics_new_int(uf->ctx->stats, "mcsat::uf::egraph_terms");
  uf->stats.avg_conflict_size = statistics_new_avg(uf->ctx->stats, "mcsat::uf::avg_conflict_size");
  uf->stats.avg_explanation_size = statistics_new_avg(uf->ctx->stats, "mcsat::uf::avg_explanation_size");
}

static
void uf_plugin_bump_terms_and_reset(uf_plugin_t* uf, int_mset_t* to_bump) {
  uint32_t i;
  for (i = 0; i < to_bump->element_list.size; ++ i) {
    term_t t = to_bump->element_list.data[i];
    variable_t t_var = variable_db_get_variable_if_exists(uf->ctx->var_db, t);
    if (t != variable_null) {
      int_hmap_pair_t* find = int_hmap_find(&to_bump->count_map, t);
      uf->ctx->bump_variable_n(uf->ctx, t_var, find->val);
    }
  }
  int_mset_clear(to_bump);
}

static
void uf_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  uf->ctx = ctx;

  scope_holder_construct(&uf->scope);
  init_ivector(&uf->conflict, 0);
  init_int_hset(&uf->fun_used_values, 0);
  int_mset_construct(&uf->tmp, NULL_TERM);

  // Terms
  ctx->request_term_notification_by_kind(ctx, APP_TERM, false);
  ctx->request_term_notification_by_kind(ctx, ARITH_RDIV, false);
  ctx->request_term_notification_by_kind(ctx, ARITH_IDIV, false);
  ctx->request_term_notification_by_kind(ctx, ARITH_MOD, false);
  ctx->request_term_notification_by_kind(ctx, EQ_TERM, false);
  ctx->request_term_notification_by_kind(ctx, UPDATE_TERM, false);

  // Types
  ctx->request_term_notification_by_type(ctx, UNINTERPRETED_TYPE);
  ctx->request_term_notification_by_type(ctx, FUNCTION_TYPE);

  // Decisions
  ctx->request_decision_calls(ctx, UNINTERPRETED_TYPE);
  ctx->request_decision_calls(ctx, FUNCTION_TYPE);

  // Equality graph
  eq_graph_construct(&uf->eq_graph, ctx, "uf");
  init_ivector(&uf->eq_graph_addition_trail, 0);

  // Weak Equality graph
  weq_graph_construct(&uf->weq_graph, ctx, &uf->eq_graph);

  // stats
  uf_plugin_stats_init(uf);
}

static
void uf_plugin_destruct(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;
  scope_holder_destruct(&uf->scope);
  delete_ivector(&uf->conflict);
  delete_int_hset(&uf->fun_used_values);
  int_mset_destruct(&uf->tmp);

  eq_graph_destruct(&uf->eq_graph);
  delete_ivector(&uf->eq_graph_addition_trail);

  weq_graph_destruct(&uf->weq_graph);
}

static
bool uf_plugin_process_eq_graph_propagations(uf_plugin_t* uf, trail_token_t* prop) {
  bool propagated = false;
  // Process any propagated terms
  if (eq_graph_has_propagated_terms(&uf->eq_graph)) {
    uint32_t i = 0;
    ivector_t eq_propagations;
    init_ivector(&eq_propagations, 0);
    eq_graph_get_propagated_terms(&uf->eq_graph, &eq_propagations);
    for (; i < eq_propagations.size; ++ i) {
      // Term to propagate
      term_t t = eq_propagations.data[i];
      // Variable to propagate
      variable_t t_var = variable_db_get_variable_if_exists(uf->ctx->var_db, t);
      if (t_var != variable_null) {
        // Only set values of uninterpreted, function and boolean type
        type_kind_t t_type_kind = term_type_kind(uf->ctx->terms, t);
        if (t_type_kind == UNINTERPRETED_TYPE ||
            t_type_kind == FUNCTION_TYPE ||
            t_type_kind == BOOL_TYPE) {
          const mcsat_value_t* v = eq_graph_get_propagated_term_value(&uf->eq_graph, t);
          if (!trail_has_value(uf->ctx->trail, t_var)) {
            if (ctx_trace_enabled(uf->ctx, "mcsat::eq::propagate")) {
              FILE* out = ctx_trace_out(uf->ctx);
              ctx_trace_term(uf->ctx, t);
              fprintf(out, " -> ");
              mcsat_value_print(v, out);
              fprintf(out, "\n");
            }
            
            prop->add(prop, t_var, v);
            (*uf->stats.propagations) ++;

            propagated = true;
          } else {
            // Ignore, we will report conflict
          }
        }
      }
    }
    delete_ivector(&eq_propagations);
  }

  return propagated;
}

static
void uf_plugin_add_to_eq_graph(uf_plugin_t* uf, term_t t, bool record) {

  term_table_t* terms = uf->ctx->terms;

  // The kind
  term_kind_t t_kind = term_kind(terms, t);

  // Add to equality graph
  composite_term_t* t_desc = NULL;
  switch (t_kind) {
  case APP_TERM:
    t_desc = app_term_desc(terms, t);
    eq_graph_add_ufun_term(&uf->eq_graph, t, t_desc->arg[0], t_desc->arity - 1, t_desc->arg + 1);
    weq_graph_add_select_term(&uf->weq_graph, t);
    break;
  case UPDATE_TERM:
    t_desc = update_term_desc(terms, t);
    eq_graph_add_ifun_term(&uf->eq_graph, t, UPDATE_TERM, t_desc->arity, t_desc->arg);
    // remember array term
    weq_graph_add_array_term(&uf->weq_graph, t);
    // remember select terms
    term_t r1 = app_term(terms, t, t_desc->arity - 2, t_desc->arg + 1);
    variable_db_get_variable(uf->ctx->var_db, r1);
    weq_graph_add_select_term(&uf->weq_graph, r1);
    // TODO: can we check if the domain is finite? if so, we can guard this extra select term
    term_t r2 = app_term(terms, t_desc->arg[0], t_desc->arity - 2, t_desc->arg + 1);
    variable_db_get_variable(uf->ctx->var_db, r2);
    weq_graph_add_select_term(&uf->weq_graph, r2);
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
    // remember array terms
    if (is_function_term(terms, t_desc->arg[0])) {
      weq_graph_add_array_eq_term(&uf->weq_graph, t);
    }
    uint32_t i;
    for (i = 0; i < 2; ++ i) {
      if (is_function_term(terms, t_desc->arg[i])) {
        weq_graph_add_array_term(&uf->weq_graph, t_desc->arg[i]);
      }
    }
    break;
  default:
    assert(false);
  }

  // Make sure the subterms are registered
  uint32_t i;
  for (i = 0; i < t_desc->arity; ++ i) {
    term_t c = t_desc->arg[i];
    variable_t c_var = variable_db_get_variable(uf->ctx->var_db, c);
    if (trail_has_value(uf->ctx->trail, c_var)) {
      // we need to process it if we ignored it
      if (eq_graph_term_is_rep(&uf->eq_graph, c)) {
        eq_graph_propagate_trail_assertion(&uf->eq_graph, c);
      }
    }
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
  term_table_t* terms = uf->ctx->terms;

  if (ctx_trace_enabled(uf->ctx, "mcsat::new_term")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_new_term_notify: ");
    ctx_trace_term(uf->ctx, t);
  }

  term_kind_t t_kind = term_kind(terms, t);

  switch (t_kind) {
  case ARITH_MOD:
  case ARITH_IDIV:
  case ARITH_RDIV:
  case APP_TERM:
  case UPDATE_TERM:
  case EQ_TERM:
    // Application terms (or other terms we treat as uninterpreted)
    uf_plugin_add_to_eq_graph(uf, t, true);
    break;
  default:
    // All other is of uninterpreted sort, and we treat as variables
    break;
  }

  // eagerly add array idx lemma
  if (t_kind == UPDATE_TERM) {
    term_t r_lemma = weq_graph_get_array_update_idx_lemma(&uf->weq_graph, t);
    prop->definition_lemma(prop, r_lemma, t);
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
  bool eq_propagated = uf_plugin_process_eq_graph_propagations(uf, prop);

  // Check for conflicts
  if (uf->eq_graph.in_conflict) {
    // Report conflict
    prop->conflict(prop);
    (*uf->stats.conflicts) ++;
    // Construct the conflict
    eq_graph_get_conflict(&uf->eq_graph, &uf->conflict, NULL, &uf->tmp);
    uf_plugin_bump_terms_and_reset(uf, &uf->tmp);
    statistic_avg_add(uf->stats.avg_conflict_size, uf->conflict.size);
    return;
  }

  // optimization: skip array checks if some terms, that are present
  // in the eq_graph, don't have an assigned value.
  variable_db_t* var_db = uf->ctx->var_db;
  term_t t = NULL_TERM;
  bool all_assigned = true;
  int_hmap_pair_t* it;
  for (it = int_hmap_first_record(&var_db->term_to_variable_map);
       it != NULL;
       it = int_hmap_next_record(&var_db->term_to_variable_map, it)) {
    t = it->key;
    if (t >= 0 && eq_graph_has_term(&uf->eq_graph, t) &&
        !eq_graph_term_has_value(&uf->eq_graph, t)) {
      all_assigned = false;
      break;
    }
  }
  
  // skip array propagation if the EQ has done propgation
  // check array propgation only if array terms are present
  if (!eq_propagated && all_assigned) {
    assert(uf->conflict.size == 0);
    weq_graph_check_array_conflict(&uf->weq_graph, &uf->conflict);
    if (uf->conflict.size > 0) {
      // Report conflict
      prop->conflict(prop);
      (*uf->stats.conflicts) ++;
      // extract terms used in the conflict
      /* for (i = 0; i < weq->conflict.size; ++i) { */
      /*   t = weq->conflict.data[i]; */
      /*   if (term_kind(terms, t) == EQ_TERM) { */
      /*     t_desc = eq_term_desc(terms, t); */
      /*     int_mset_add(&weq->tmp, t_desc->arg[0]); */
      /*     int_mset_add(&weq->tmp, t_desc->arg[1]); */
      /*   } else { */
      /*     assert(false); */
      /*   } */
      /* } */
      /* weq_graph_bump_terms_and_reset(weq, &weq->tmp); */
      statistic_avg_add(uf->stats.avg_conflict_size, uf->conflict.size);
    }
  }
}

static
void uf_plugin_push(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  // Push the int variable values
  scope_holder_push(&uf->scope,
                    &uf->eq_graph_addition_trail.size,
                    NULL);

  weq_graph_push(&uf->weq_graph);
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

  weq_graph_pop(&uf->weq_graph);
  eq_graph_pop(&uf->eq_graph);

  // Re-add all the terms to eq graph
  uint32_t i;
  for (i = old_eq_graph_addition_trail_size; i < uf->eq_graph_addition_trail.size; ++ i) {
    term_t t = uf->eq_graph_addition_trail.data[i];
    uf_plugin_add_to_eq_graph(uf, t, false);
  }
  // We've already processed all the propagations, so we just reset it
  eq_graph_get_propagated_terms(&uf->eq_graph, NULL);

  // Clear the conflict
  ivector_reset(&uf->conflict);
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
  bool cache_ok = eq_graph_get_forbidden(&uf->eq_graph, x_term, &forbidden, x_cached_value);
  if (ctx_trace_enabled(uf->ctx, "uf_plugin::decide")) {
    ctx_trace_printf(uf->ctx, "picking !=");
    uint32_t i;
    for (i = 0; i < forbidden.size; ++ i) {
      const mcsat_value_t* v = forbidden.data[i];
      ctx_trace_printf(uf->ctx, " ");
      mcsat_value_print(v, ctx_trace_out(uf->ctx));
    }
    ctx_trace_printf(uf->ctx, "\n");
  }

  term_table_t *terms = uf->ctx->terms;
  type_t x_type = term_type(terms, x_term);
  int32_t picked_value = 0;
  if (!cache_ok) {
    // Pick smallest value not in forbidden list
    ptr_array_sort2(forbidden.data, forbidden.size, NULL, value_cmp);
    uint32_t i;
    // function types have different value picking strategy
    if (term_type_kind(terms, x_term) != FUNCTION_TYPE) {
      for (i = 0; i < forbidden.size; ++ i) {
        const mcsat_value_t* v = forbidden.data[i];
        assert(v->type == VALUE_RATIONAL);
        int32_t v_int = 0;
        bool ok = q_get32((rational_t*)&v->q, &v_int);
        (void) ok;
        assert(ok);
        if (picked_value < v_int) {
          // found a gap
          break;
        } else {
          picked_value = v_int + 1;
        }
      }
      // DECIDE_FUNCTION_VALUE_START is the starting point for function values
      assert(picked_value < DECIDE_FUNCTION_VALUE_START);
    } else {
      /* we pick different values for different functions. Equal
	 functions get equal values via equality propagation. */
      if (forbidden.size > 0) {
        uint32_t max_forbidden_val = 0;
        const mcsat_value_t* v = forbidden.data[forbidden.size - 1];
        assert(v->type == VALUE_RATIONAL);
        bool ok = q_get32((rational_t*)&v->q, &max_forbidden_val);
        (void) ok;
        assert(ok);
        picked_value = max_forbidden_val + 1;
      }
      if (picked_value < DECIDE_FUNCTION_VALUE_START) {
        // starting point for function values
        picked_value = DECIDE_FUNCTION_VALUE_START;
      }

      while (int_hset_member(&uf->fun_used_values, picked_value)) {
        picked_value += 1;
      }
      // save the used value
      int_hset_add(&uf->fun_used_values, picked_value);
    }
  } else {
    assert(x_cached_value->type == VALUE_RATIONAL);
    bool ok = q_get32((rational_t*)&x_cached_value->q, &picked_value);
    (void) ok;
    assert(ok);
  }

  if (ctx_trace_enabled(uf->ctx, "uf_plugin::decide")) {
    ctx_trace_printf(uf->ctx, "picked %"PRIi32"\n", picked_value);
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
  eq_graph_gc_mark(&uf->eq_graph, gc_vars, EQ_GRAPH_MARK_ALL);
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

  term_t subst = eq_graph_explain_term_propagation(&uf->eq_graph, var_term, reasons, NULL, &uf->tmp);
  uf_plugin_bump_terms_and_reset(uf, &uf->tmp);
  statistic_avg_add(uf->stats.avg_explanation_size, reasons->size);
  return subst;
}

static
bool uf_plugin_explain_evaluation(plugin_t* plugin, term_t t, int_mset_t* vars, mcsat_value_t* value) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_explain_evaluation():\n");
    ctx_trace_term(uf->ctx, t);
  }

  term_table_t* terms = uf->ctx->terms;
  variable_db_t* var_db = uf->ctx->var_db;
  const mcsat_trail_t* trail = uf->ctx->trail;

  // Get all the variables and make sure they are all assigned.
  term_kind_t t_kind = term_kind(terms, t);
  if (t_kind == EQ_TERM) {
    composite_term_t* eq_desc = eq_term_desc(terms, t);
    term_t lhs_term = eq_desc->arg[0];
    term_t rhs_term = eq_desc->arg[1];
    variable_t lhs_var = variable_db_get_variable_if_exists(var_db, lhs_term);
    variable_t rhs_var = variable_db_get_variable_if_exists(var_db, rhs_term);

    // Add to variables
    if (lhs_var != variable_null) {
      int_mset_add(vars, lhs_var);
    }
    if (rhs_var != variable_null) {
      int_mset_add(vars, rhs_var);
    }

    // Check if both are assigned
    if (lhs_var == variable_null) {
      return false;
    }
    if (rhs_var == variable_null) {
      return false;
    }
    if (!trail_has_value(trail, lhs_var)) {
      return false;
    }
    if (!trail_has_value(trail, rhs_var)) {
      return false;
    }

    const mcsat_value_t* lhs_value = trail_get_value(trail, lhs_var);
    const mcsat_value_t* rhs_value = trail_get_value(trail, rhs_var);
    bool lhs_eq_rhs = mcsat_value_eq(lhs_value, rhs_value);
    bool negated = is_neg_term(t);
    if ((negated && (value->b != lhs_eq_rhs)) ||
        (!negated && (value->b == lhs_eq_rhs))) {
      return true;
    }

  }

  // Default: return false for cases like f(x) -> false, this is done in the
  // core
  return false;
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


// Compare two terms by function application: group same functions together
static
bool uf_plugin_build_model_compare(void *data, term_t t1, term_t t2) {
  model_sort_data_t* ctx = (model_sort_data_t*) data;

  int32_t t1_app = term_kind(ctx->terms, t1);
  int32_t t2_app = term_kind(ctx->terms, t2);

  if (t1_app != t2_app) {
    return t1_app < t2_app;
  }

  if (t1_app == APP_TERM) {
    t1_app = app_term_desc(ctx->terms, t1)->arg[0];
    t2_app = app_term_desc(ctx->terms, t2)->arg[0];
    if (t1_app != t2_app) {
      return t1_app < t2_app;
    }
  }
  return t1 < t2;
}

static inline
type_t get_function_application_type(term_table_t* terms, term_kind_t app_kind, term_t f) {

  type_table_t* types = terms->types;
  type_t reals = real_type(types);
  type_t ints = int_type(types);

  switch (app_kind) {
  case UPDATE_TERM:
  case APP_TERM:
    return term_type(terms, f);
  case ARITH_RDIV:
    return function_type(types, reals, 1, &reals);
  case ARITH_IDIV:
  case ARITH_MOD:
    return function_type(types, ints, 1, &ints);
  default:
    assert(false);
  }

  return NULL_TYPE;
}

static inline
value_t uf_plugin_get_term_value(uf_plugin_t* uf, value_table_t* vtbl, term_t t) {
  type_t t_type = term_type(uf->ctx->terms, t);
  variable_t t_var = variable_db_get_variable_if_exists(uf->ctx->var_db, t);
  if (t_var != variable_null) {
    const mcsat_value_t* t_value = trail_get_value(uf->ctx->trail, t_var);
    return mcsat_value_to_value(t_value, uf->ctx->types, t_type, vtbl);
  } else {
    assert(false);
    return null_value;
  }
}

static inline
value_t vtbl_mk_default(type_table_t* types, value_table_t *vtbl, type_t tau) {
  type_kind_t tau_kind = type_kind(types, tau);
  switch(tau_kind) {
  case BOOL_TYPE:
    return vtbl_mk_false(vtbl);
    break;
  case REAL_TYPE:
  case INT_TYPE:
    return vtbl_mk_int32(vtbl, 0);
    break;
  case BITVECTOR_TYPE:
    return vtbl_mk_bv_zero(vtbl, bv_type_size(types, tau));
    break;
  case UNINTERPRETED_TYPE:
    return vtbl_mk_const(vtbl, tau, 0, "");
    break;
  default:
    assert(false);
  }

  return null_value;
}

static
void uf_plugin_build_model(plugin_t* plugin, model_t* model) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  term_table_t* terms = uf->ctx->terms;
  value_table_t* vtbl = &model->vtbl;
  variable_db_t* var_db = uf->ctx->var_db;
  const mcsat_trail_t* trail = uf->ctx->trail;

  // Data for sorting
  model_sort_data_t sort_ctx;
  sort_ctx.terms = terms;
  sort_ctx.var_db = var_db;

  // Sort the terms from the equality graph by function used: we get a list of function
  // applications where we can easily collect them by linear scan
  ivector_t app_terms;
  init_ivector(&app_terms, uf->eq_graph_addition_trail.size);
  ivector_copy(&app_terms, uf->eq_graph_addition_trail.data, uf->eq_graph_addition_trail.size);
  int_array_sort2(app_terms.data, app_terms.size, &sort_ctx, uf_plugin_build_model_compare);

  // Mappings that we collect for a single function
  ivector_t mappings;
  init_ivector(&mappings, 0);

  // Temp for arguments of a one concrete mapping
  ivector_t arguments;
  init_ivector(&arguments, 0);

  // Got through all the representatives that have a set value and
  // - while same function, collect the concrete mappings
  // - if different function, construct the function and add to model
  uint32_t i;
  term_t app_f = NULL_TERM, prev_app_f = NULL_TERM;  // Current and previous function symbol
  term_t app_term, prev_app_term = NULL_TERM; // Current and previous function application term
  term_kind_t app_kind = UNUSED_TERM, prev_app_kind = UNUSED_TERM; // Kind of the current and previous function
  bool app_construct = true; // Whether to construct it
  for (i = 0; i < app_terms.size; ++ i) {

    // Current representative application
    app_term = app_terms.data[i];

    // Only need to do functions and uninterpreted
    app_kind = term_kind(terms, app_term);
    switch (app_kind) {
    case APP_TERM:
    case ARITH_RDIV:
    case ARITH_IDIV:
    case ARITH_MOD:
      app_construct = true;
      break;
    default:
      app_construct = false;
      continue;
    }

    composite_term_t* app_comp = composite_term_desc(terms, app_term);

    if (ctx_trace_enabled(uf->ctx, "uf_plugin::model")) {
      ctx_trace_printf(uf->ctx, "processing app rep:");
      ctx_trace_term(uf->ctx, app_term);
    }

    if (app_kind == APP_TERM) {
      app_f = app_comp->arg[0];
    } else {
      app_f = NULL_TERM;
      // Division only if division by 0
      assert(app_comp->arity == 2);
      term_t divisor_term = app_comp->arg[1];
      variable_t divisor_var = variable_db_get_variable(var_db, divisor_term);
      assert(trail_has_value(trail, divisor_var));
      const mcsat_value_t* divisor_value = trail_get_value(trail, divisor_var);
      if (!mcsat_value_is_zero(divisor_value)) {
        continue;
      }
    }

    // If we changed the function, construct the previous one
    if (prev_app_term != NULL_TERM) {
      if (app_f != prev_app_f || app_kind != prev_app_kind) {
        type_t tau = get_function_application_type(terms, prev_app_kind, prev_app_f);
        type_t range_tau = function_type_range(terms->types, tau);
        value_t f_value = vtbl_mk_function(vtbl, tau, mappings.size, mappings.data, vtbl_mk_default(terms->types, vtbl, range_tau));
        switch (prev_app_kind) {
        case ARITH_RDIV:
          vtbl_set_zero_rdiv(vtbl, f_value);
          break;
        case ARITH_IDIV:
          vtbl_set_zero_idiv(vtbl, f_value);
          break;
        case ARITH_MOD:
          vtbl_set_zero_mod(vtbl, f_value);
          break;
        case APP_TERM:
          model_map_term(model, prev_app_f, f_value);
          break;
        default:
          assert(false);
        }
        // Reset the mapping
        ivector_reset(&mappings);
      }
    }

    // Next concrete mapping f : (x1, x2, ..., xn) -> v
    // a) Get the v value
    value_t v = uf_plugin_get_term_value(uf, vtbl, app_term);
    // b) Get the argument values
    uint32_t arg_i;
    uint32_t arg_start = app_kind == APP_TERM ? 1 : 0;
    uint32_t arg_end = app_kind == APP_TERM ? app_comp->arity : app_comp->arity - 1;
    ivector_reset(&arguments);
    for (arg_i = arg_start; arg_i < arg_end; ++ arg_i) {
      term_t arg_term = app_comp->arg[arg_i];
      value_t arg_v = uf_plugin_get_term_value(uf, vtbl, arg_term);
      ivector_push(&arguments, arg_v);
    }
    // c) Construct the concrete mapping, and save in the list for f
    value_t map_value = vtbl_mk_map(vtbl, arguments.size, arguments.data, v);
    ivector_push(&mappings, map_value);

    // Remember the previous one
    prev_app_f = app_f;
    prev_app_term = app_term;
    prev_app_kind = app_kind;
  }

  // Since we make functions when we see a new one, we also construct the last function
  if (app_terms.size > 0 && mappings.size > 0 && app_construct) {
    type_t tau = get_function_application_type(terms, app_kind, app_f);
    type_t range_tau = function_type_range(terms->types, tau);
    value_t f_value = vtbl_mk_function(vtbl, tau, mappings.size, mappings.data, vtbl_mk_default(terms->types, vtbl, range_tau));
    switch (app_kind) {
    case ARITH_RDIV:
      vtbl_set_zero_rdiv(vtbl, f_value);
      break;
    case ARITH_IDIV:
      vtbl_set_zero_idiv(vtbl, f_value);
      break;
    case ARITH_MOD:
      vtbl_set_zero_mod(vtbl, f_value);
      break;
    case APP_TERM:
      model_map_term(model, prev_app_f, f_value);
      break;
    default:
      assert(false);
    }
  }

  // Remove temps
  delete_ivector(&arguments);
  delete_ivector(&mappings);
  delete_ivector(&app_terms);
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
  plugin->plugin_interface.decide_assignment     = NULL;
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
