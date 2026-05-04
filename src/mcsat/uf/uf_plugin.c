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

#include "model/fresh_value_maker.h"
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
    if (t_var != variable_null) {
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
    eq_graph_add_ufun_term(&uf->eq_graph, t, t_desc->arg[0], t_desc->arity - 1, t_desc->arg + 1);
    // remember array term
    weq_graph_add_array_term(&uf->weq_graph, t);
    weq_graph_add_array_term(&uf->weq_graph, t_desc->arg[0]);
    // remember select terms
    term_t r1 = app_term(terms, t, t_desc->arity - 2, t_desc->arg + 1);
    variable_db_get_variable(uf->ctx->var_db, r1);
    weq_graph_add_select_term(&uf->weq_graph, r1);
    // if the element domain is finite then we add this extra read term
    type_t element_type = term_type(terms, t_desc->arg[2]);
    if (is_finite_type(terms->types, element_type) || is_boolean_type(element_type) || is_bv_type(terms->types, element_type)){
      term_t r2 = app_term(terms, t_desc->arg[0], t_desc->arity - 2, t_desc->arg + 1);
      variable_db_get_variable(uf->ctx->var_db, r2);
      weq_graph_add_select_term(&uf->weq_graph, r2);
    }
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
    uint32_t i;
    for (i = 0; i < 2; ++ i) {
      if (is_function_term(terms, t_desc->arg[i]) &&
	  (term_kind(terms, t_desc->arg[i]) == UNINTERPRETED_TERM ||
	   term_kind(terms, t_desc->arg[i]) == UPDATE_TERM)) {
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
void uf_plugin_learn(plugin_t* plugin, trail_token_t* prop) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;
  assert(uf->conflict.size == 0);

  // check array conflicts
  weq_graph_check_array_conflict(&uf->weq_graph, &uf->conflict);

  if (uf->conflict.size > 0) {
    // Report conflict
    prop->conflict(prop);
    (*uf->stats.conflicts) ++;
    statistic_avg_add(uf->stats.avg_conflict_size, uf->conflict.size);
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
  uf_plugin_process_eq_graph_propagations(uf, prop);

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
  if (weq_graph_is_all_assigned(&uf->weq_graph)) {
    assert(uf->conflict.size == 0);
    weq_graph_check_array_conflict(&uf->weq_graph, &uf->conflict);
    if (uf->conflict.size > 0) {
      // Report conflict
      prop->conflict(prop);
      (*uf->stats.conflicts) ++;
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
        int32_t max_forbidden_val = 0;
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
  const mcsat_trail_t* trail;
} model_sort_data_t;


static
bool uf_plugin_get_function_id_from_trail(term_table_t* terms, variable_db_t* var_db, const mcsat_trail_t* trail, term_t t, int32_t* id) {
  variable_t t_var = variable_db_get_variable_if_exists(var_db, t);
  assert(t_var != variable_null);
  assert(trail_has_value(trail, t_var));

  const mcsat_value_t* t_value = trail_get_value(trail, t_var);
  assert(t_value->type == VALUE_RATIONAL);

  bool ok = q_get32((rational_t*) &t_value->q, id);
  if (!ok) {
    // Function ids are allocated as small non-negative integers by
    // uf_plugin_decide; overflow into an unrepresentable rational would
    // indicate a serious internal inconsistency. Assert in debug; in release
    // builds, report failure so callers don't collapse unrelated overflowed
    // ids into one sentinel hashmap key.
    // LCOV_EXCL_START - unreachable on supported inputs
    assert(false);
    return false;
    // LCOV_EXCL_STOP
  }

  return true;
}

static
bool uf_plugin_get_function_id(uf_plugin_t* uf, term_t t, int32_t* id) {
  return uf_plugin_get_function_id_from_trail(uf->ctx->terms, uf->ctx->var_db, uf->ctx->trail, t, id);
}


// Compare applications by the function value of their head term
static
bool uf_plugin_build_app_model_compare(void *data, term_t t1, term_t t2) {
  model_sort_data_t* ctx = (model_sort_data_t*) data;
  term_t t1_fun = app_term_desc(ctx->terms, t1)->arg[0];
  term_t t2_fun = app_term_desc(ctx->terms, t2)->arg[0];
  int32_t t1_fun_id, t2_fun_id;

  if (!uf_plugin_get_function_id_from_trail(ctx->terms, ctx->var_db, ctx->trail, t1_fun, &t1_fun_id) ||
      !uf_plugin_get_function_id_from_trail(ctx->terms, ctx->var_db, ctx->trail, t2_fun, &t2_fun_id)) {
    return t1 < t2;  // LCOV_EXCL_LINE - defensive fallback, unreachable on supported inputs
  }

  if (t1_fun_id != t2_fun_id) {
    return t1_fun_id < t2_fun_id;
  }

  return t1 < t2;
}

static
bool uf_plugin_build_special_model_compare(void *data, term_t t1, term_t t2) {
  term_table_t* terms = (term_table_t*) data;
  term_kind_t t1_kind = term_kind(terms, t1);
  term_kind_t t2_kind = term_kind(terms, t2);

  if (t1_kind != t2_kind) {
    return t1_kind < t2_kind;
  }

  return t1 < t2;
}

// Returns the function type for an application-shaped term whose kind is
// app_kind. For APP_TERM/UPDATE_TERM the type is read from the head term f;
// for div/mod it is the well-known one-argument arithmetic function type and
// f is unused. Callers in the div/mod branches may pass NULL_TERM for f.
static inline
type_t get_function_application_type(term_table_t* terms, term_kind_t app_kind, term_t f) {

  type_table_t* types = terms->types;
  type_t reals = real_type(types);
  type_t ints = int_type(types);

  switch (app_kind) {
  case UPDATE_TERM:
  case APP_TERM:
    assert(f != NULL_TERM);
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

// Default value of type tau for use as the "else" branch of a function.
// Kept as a wrapper for readability at call sites.
static inline
value_t vtbl_mk_default(value_table_t *vtbl, type_t tau) {
  return vtbl_make_object(vtbl, tau);
}

typedef struct {
  uf_plugin_t* uf;
  value_table_t* vtbl;
  fresh_val_maker_t maker;
  ivector_t app_terms;
  ivector_t arguments;
  int_hmap_t app_term_first;
  int_hmap_t function_term;
  int_hmap_t function_value;
} uf_model_builder_t;

static
void uf_model_builder_construct(uf_model_builder_t* builder, uf_plugin_t* uf, value_table_t* vtbl) {
  builder->uf = uf;
  builder->vtbl = vtbl;
  init_fresh_val_maker(&builder->maker, vtbl);
  init_ivector(&builder->app_terms, 0);
  init_ivector(&builder->arguments, 0);
  init_int_hmap(&builder->app_term_first, 0);
  init_int_hmap(&builder->function_term, 0);
  init_int_hmap(&builder->function_value, 0);
}

static
void uf_model_builder_destruct(uf_model_builder_t* builder) {
  delete_int_hmap(&builder->function_value);
  delete_int_hmap(&builder->function_term);
  delete_int_hmap(&builder->app_term_first);
  delete_ivector(&builder->arguments);
  delete_ivector(&builder->app_terms);
  delete_fresh_val_maker(&builder->maker);
}

// Record 't' as a candidate canonical term for its function-id.
// Priority rule: once an UNINTERPRETED_TERM is stored for a given function-id,
// keep it. Otherwise (no term yet, or a non-uninterpreted term stored), overwrite
// with 't'. This ensures the canonical representative is an uninterpreted function
// symbol when one is available, which is preferred for model printing.
static
void uf_model_builder_remember_function_term(uf_model_builder_t* builder, term_t t) {
  int32_t function_id;
  int_hmap_pair_t* find;
  term_table_t* terms = builder->uf->ctx->terms;

  if (term_type_kind(terms, t) != FUNCTION_TYPE) {
    return;
  }

  if (!uf_plugin_get_function_id(builder->uf, t, &function_id)) {
    return;  // LCOV_EXCL_LINE - defensive fallback, unreachable on supported inputs
  }

  find = int_hmap_get(&builder->function_term, function_id);

  if (find->val < 0 || term_kind(terms, find->val) != UNINTERPRETED_TERM) {
    find->val = t;
  }
}

static
value_t uf_model_builder_get_term_value(uf_model_builder_t* builder, term_t t);

static
value_t uf_model_builder_get_function_value(uf_model_builder_t* builder, term_t t) {
  uint32_t i;
  int32_t function_id;
  int_hmap_pair_t* find;
  term_table_t* terms = builder->uf->ctx->terms;
  value_t f_value;
  ivector_t arguments;

  assert(term_type_kind(terms, t) == FUNCTION_TYPE);

  if (!uf_plugin_get_function_id(builder->uf, t, &function_id)) {
    return null_value;  // LCOV_EXCL_LINE - defensive fallback, unreachable on supported inputs
  }

  uf_model_builder_remember_function_term(builder, t);

  find = int_hmap_get(&builder->function_value, function_id);
  if (find->val >= 0) {
    return find->val;
  }

  init_ivector(&arguments, 0);

  term_t fun_term = int_hmap_find(&builder->function_term, function_id)->val;
  type_t fun_type = term_type(terms, fun_term);
  f_value = make_fresh_function(&builder->maker, fun_type);
  if (f_value == null_value) {
    // Unreachable on supported inputs: the MCSAT preprocessor guard
    // (term_needs_function_diseq_guard in mcsat/preprocessor.c) rejects
    // equality atoms whose type contains a finite-domain function sort, so
    // make_fresh_function should always succeed for any function type that
    // reaches model construction. If we ever reach here, the guard has a
    // hole; fail closed rather than silently constructing a collapsing
    // default function value.
    // LCOV_EXCL_START - unreachable, rejected by preprocessor guard
    assert(false && "unreachable: preprocessor guard should have rejected this type");
    delete_ivector(&arguments);
    return null_value;
    // LCOV_EXCL_STOP
  }

  // Cache the fresh base function first to handle recursive calls that come
  // back to the same function_id. Such cycles arise when an application
  // ((t x) ...) has an argument or result whose mcsat-trail function id
  // coincides with t's function id (rare but possible). The cached value at
  // that point is the bare fresh base, without the updates that this call is
  // still in the middle of applying.
  //
  // KNOWN LIMITATION: if such a cycle occurs, the inner call returns a
  // partial function value, and any value_t built from that view (e.g., as
  // an argument or result of vtbl_mk_update below) encodes the partial,
  // pre-update view rather than the final updated function. The model
  // emitted on such inputs is best-effort and may not be extensional on the
  // self-referential pair. Without a visited-set + theory-conflict path,
  // this is the cheapest cycle break we can make. Avoiding the cache write
  // here would loop indefinitely.
  find->val = f_value;
  find = NULL; // invalidated once we recurse (int_hmap_get may resize the table)

  int_hmap_pair_t* first_app = int_hmap_find(&builder->app_term_first, function_id);
  if (first_app != NULL) {
    for (i = first_app->val; i < builder->app_terms.size; ++ i) {
      term_t app_term = builder->app_terms.data[i];
      composite_term_t* app_desc = app_term_desc(terms, app_term);

      int32_t app_function_id;
      if (!uf_plugin_get_function_id(builder->uf, app_desc->arg[0], &app_function_id) ||
          app_function_id != function_id) {
        break;
      }

      ivector_reset(&arguments);
      uint32_t arg_i;
      for (arg_i = 1; arg_i < app_desc->arity; ++ arg_i) {
        ivector_push(&arguments, uf_model_builder_get_term_value(builder, app_desc->arg[arg_i]));
      }

      value_t result_value = uf_model_builder_get_term_value(builder, app_term);
      f_value = vtbl_mk_update(builder->vtbl, f_value, arguments.size, arguments.data, result_value);
    }

    // Re-fetch: the recursive calls above may have inserted new entries into
    // builder->function_value and triggered int_hmap_extend, which invalidates
    // any int_hmap_pair_t* obtained before recursion.
    int_hmap_get(&builder->function_value, function_id)->val = f_value;
  }

  delete_ivector(&arguments);
  return f_value;
}

static
value_t uf_model_builder_get_term_value(uf_model_builder_t* builder, term_t t) {
  if (term_type_kind(builder->uf->ctx->terms, t) == FUNCTION_TYPE) {
    return uf_model_builder_get_function_value(builder, t);
  }

  return uf_plugin_get_term_value(builder->uf, builder->vtbl, t);
}

static
void uf_model_builder_prepare(uf_model_builder_t* builder) {
  uf_plugin_t* uf = builder->uf;
  term_table_t* terms = uf->ctx->terms;
  model_sort_data_t sort_ctx;
  uint32_t i;

  sort_ctx.terms = terms;
  sort_ctx.var_db = uf->ctx->var_db;
  sort_ctx.trail = uf->ctx->trail;

  for (i = 0; i < uf->eq_graph_addition_trail.size; ++ i) {
    term_t t = uf->eq_graph_addition_trail.data[i];
    if (term_kind(terms, t) == APP_TERM) {
      ivector_push(&builder->app_terms, t);
    }
  }

  if (builder->app_terms.size == 0) {
    return;
  }

  int_array_sort2(builder->app_terms.data, builder->app_terms.size, &sort_ctx, uf_plugin_build_app_model_compare);

  for (i = 0; i < builder->app_terms.size; ++ i) {
    term_t app_term = builder->app_terms.data[i];
    composite_term_t* app_desc = app_term_desc(terms, app_term);
    int32_t function_id;
    if (!uf_plugin_get_function_id(builder->uf, app_desc->arg[0], &function_id)) {
      continue;  // LCOV_EXCL_LINE - defensive fallback, unreachable on supported inputs
    }

    int_hmap_pair_t* first = int_hmap_get(&builder->app_term_first, function_id);
    if (first->val < 0) {
      first->val = i;
    }

    uf_model_builder_remember_function_term(builder, app_desc->arg[0]);
    uf_model_builder_remember_function_term(builder, app_term);
  }
}

static
void uf_plugin_build_model(plugin_t* plugin, model_t* model) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  term_table_t* terms = uf->ctx->terms;
  value_table_t* vtbl = &model->vtbl;
  variable_db_t* var_db = uf->ctx->var_db;
  const mcsat_trail_t* trail = uf->ctx->trail;
  uf_model_builder_t builder;
  uf_model_builder_construct(&builder, uf, vtbl);
  uf_model_builder_prepare(&builder);

  // Build values for all top-level uninterpreted functions in the trail.
  uint32_t i;
  const ivector_t* trail_elements = &trail->elements;
  for (i = 0; i < trail_elements->size; ++ i) {
    variable_t x = trail_elements->data[i];
    term_t x_term = variable_db_get_term(var_db, x);
    if (term_kind(terms, x_term) == UNINTERPRETED_TERM &&
        term_type_kind(terms, x_term) == FUNCTION_TYPE) {
      value_t x_value;
      uf_model_builder_remember_function_term(&builder, x_term);
      x_value = uf_model_builder_get_function_value(&builder, x_term);
      if (x_value != null_value) {
        model_map_term(model, x_term, x_value);
      }
    }
  }

  // Now construct special interpreted functions for division-by-zero cases.
  ivector_t special_terms;
  init_ivector(&special_terms, 0);
  for (i = 0; i < uf->eq_graph_addition_trail.size; ++ i) {
    term_t t = uf->eq_graph_addition_trail.data[i];
    term_kind_t kind = term_kind(terms, t);
    if (kind == ARITH_RDIV || kind == ARITH_IDIV || kind == ARITH_MOD) {
      ivector_push(&special_terms, t);
    }
  }

  int_array_sort2(special_terms.data, special_terms.size, terms, uf_plugin_build_special_model_compare);

  ivector_t mappings;
  init_ivector(&mappings, 0);

  // Go through the special (div/mod) applications sorted by kind. While the kind
  // is unchanged, collect concrete mappings; when the kind changes, emit the
  // function value for the previous kind.
  //
  // Note: only div-by-zero cases contribute mappings; other divisors are skipped.
  term_t app_term;
  term_kind_t app_kind = UNUSED_TERM, prev_app_kind = UNUSED_TERM;
  bool has_prev = false;
  for (i = 0; i < special_terms.size; ++ i) {

    app_term = special_terms.data[i];
    app_kind = term_kind(terms, app_term);
    assert(app_kind == ARITH_RDIV || app_kind == ARITH_IDIV || app_kind == ARITH_MOD);

    composite_term_t* app_comp = composite_term_desc(terms, app_term);

    if (ctx_trace_enabled(uf->ctx, "uf_plugin::model")) {
      ctx_trace_printf(uf->ctx, "processing app rep:");
      ctx_trace_term(uf->ctx, app_term);
    }

    // Division only if division by 0
    assert(app_comp->arity == 2);
    term_t divisor_term = app_comp->arg[1];
    variable_t divisor_var = variable_db_get_variable(var_db, divisor_term);
    assert(trail_has_value(trail, divisor_var));
    const mcsat_value_t* divisor_value = trail_get_value(trail, divisor_var);
    if (!mcsat_value_is_zero(divisor_value)) {
      continue;
    }

    // If the kind changed, emit the previous function.
    if (has_prev && app_kind != prev_app_kind) {
      type_t tau = get_function_application_type(terms, prev_app_kind, NULL_TERM);
      type_t range_tau = function_type_range(terms->types, tau);
      value_t f_value = vtbl_mk_function(vtbl, tau, mappings.size, mappings.data, vtbl_mk_default(vtbl, range_tau));
      switch (prev_app_kind) {
      case ARITH_RDIV: vtbl_set_zero_rdiv(vtbl, f_value); break;
      case ARITH_IDIV: vtbl_set_zero_idiv(vtbl, f_value); break;
      case ARITH_MOD:  vtbl_set_zero_mod(vtbl, f_value);  break;
      default: assert(false);
      }
      ivector_reset(&mappings);
    }

    // Next concrete mapping f : (x1, ..., xn) -> v. For div/mod the "function"
    // consumes only the numerator (arity - 1 args); the divisor is always 0 here.
    value_t v = uf_plugin_get_term_value(uf, vtbl, app_term);
    uint32_t arg_i;
    uint32_t arg_end = app_comp->arity - 1;
    ivector_reset(&builder.arguments);
    for (arg_i = 0; arg_i < arg_end; ++ arg_i) {
      term_t arg_term = app_comp->arg[arg_i];
      value_t arg_v = uf_plugin_get_term_value(uf, vtbl, arg_term);
      ivector_push(&builder.arguments, arg_v);
    }
    value_t map_value = vtbl_mk_map(vtbl, builder.arguments.size, builder.arguments.data, v);
    ivector_push(&mappings, map_value);

    prev_app_kind = app_kind;
    has_prev = true;
  }

  // Emit the last pending function, if any.
  if (has_prev && mappings.size > 0) {
    type_t tau = get_function_application_type(terms, prev_app_kind, NULL_TERM);
    type_t range_tau = function_type_range(terms->types, tau);
    value_t f_value = vtbl_mk_function(vtbl, tau, mappings.size, mappings.data, vtbl_mk_default(vtbl, range_tau));
    switch (prev_app_kind) {
    case ARITH_RDIV: vtbl_set_zero_rdiv(vtbl, f_value); break;
    case ARITH_IDIV: vtbl_set_zero_idiv(vtbl, f_value); break;
    case ARITH_MOD:  vtbl_set_zero_mod(vtbl, f_value);  break;
    default: assert(false);
    }
  }

  // Remove temps
  delete_ivector(&mappings);
  delete_ivector(&special_terms);
  uf_model_builder_destruct(&builder);
}

plugin_t* uf_plugin_allocator(void) {
  uf_plugin_t* plugin = safe_malloc(sizeof(uf_plugin_t));
  plugin_construct((plugin_t*) plugin);
  plugin->plugin_interface.construct             = uf_plugin_construct;
  plugin->plugin_interface.destruct              = uf_plugin_destruct;
  plugin->plugin_interface.new_term_notify       = uf_plugin_new_term_notify;
  plugin->plugin_interface.new_lemma_notify      = NULL;
  plugin->plugin_interface.event_notify          = NULL;
  plugin->plugin_interface.propagate             = uf_plugin_propagate;
  plugin->plugin_interface.decide                = uf_plugin_decide;
  plugin->plugin_interface.decide_assignment     = NULL;
  plugin->plugin_interface.learn                 = uf_plugin_learn;
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
