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
#include "utils/int_array_hsets.h"
#include "utils/int_hash_sets.h"

#include "utils/ptr_array_sort2.h"
#include "utils/ptr_hash_map.h"
#include "utils/ptr_sets.h"
#include "utils/refcount_strings.h"

#include "model/models.h"

#include "terms/terms.h"
#include "inttypes.h"

#include "api/yices_api_lock_free.h"

#define DECIDE_FUNCTION_VALUE_START UINT32_MAX/64

#define USE_ARRAY_DIFF 0 //experimental

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

  /** Array terms */
  ivector_t array_terms;

  /** Array eq terms */
  ivector_t array_eq_terms;

  /** Select terms */
  ivector_t select_terms;

  /** Map from types to diff symbols */
  int_hmap_t type_to_diff;

  /** Set of Diff Funs */
  int_hset_t diff_funs;

  /** Map: terms to fun_nodes */
  ptr_hmap_t fun_node_map;

  /** Function Values to types map */
  ptr_hmap_t fun_val_type_map;

  /** Function Values to term (one rep term) */
  int_hmap_t fun_val_term_map;

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


static inline void add_if_not_true_term(ivector_t* vec, term_t t) {
  if (t != true_term) {
    ivector_push(vec, t);
  }
}

/*
 * Weakly Equivalent Arrays: data structure
 */

typedef struct fun_node_s {
  term_t t;
  struct fun_node_s* p;
  term_t pstore;
  term_t pi;
  struct fun_node_s* s;
  term_t sstore;
} fun_node_t;  

static inline fun_node_t *new_node() {
  fun_node_t *n = safe_malloc(sizeof(fun_node_t));
  n->t = NULL_TERM;
  n->p = NULL;
  n->pstore = NULL_TERM;
  n->pi = NULL_TERM;
  n->s  = NULL;
  n->sstore = NULL_TERM;
  return n;
}

static const fun_node_t* get_rep(const eq_graph_t* eq_graph,
                                 const fun_node_t* n) {
  const fun_node_t* res = n;
  while (res->p != NULL) {
    res = res->p;
  }
  return res;
}

static uint32_t count_primary(const eq_graph_t* eq_graph,
                              const fun_node_t* n) {
  uint32_t res = 0;
  const fun_node_t* tmp = n;
  
  while (tmp->p != NULL) {
    tmp = tmp->p;
    res++;
  }
  return res;
}

static const fun_node_t* get_rep_i(const eq_graph_t* eq_graph, const fun_node_t* n,
                                   const term_t idx) {
  const fun_node_t* res = n;
  while (res->p != NULL) {
    if (eq_graph_are_equal(eq_graph, res->pi, idx)) {
      if (res->s == NULL) {
        break;
      }
      res = res->s;
    } else {
      res = res->p;
    }
  }
  return res;
}

static uint32_t count_secondary(const eq_graph_t* eq_graph, const fun_node_t* n,
                                const term_t idx) {
  uint32_t res = 0;
  const fun_node_t* tmp = n;
  while (tmp->p != NULL) {
    if (eq_graph_are_equal(eq_graph, tmp->pi, idx)) {
      if (tmp->s == NULL) {
        break;
      }
      tmp = tmp->s;
      res++;
    } else {
      tmp = tmp->p;
    }
  }
  return res;
}

static const fun_node_t* find_secondary_node(const eq_graph_t* eq_graph,
                                             fun_node_t* n, term_t idx) {
  const fun_node_t* res = n;
  while (res->p != NULL && !eq_graph_are_equal(eq_graph, res->pi, idx)) {
    res = res->p;
  }
  return res;
}

static term_t uf_plugin_get_index_from_store(uf_plugin_t* uf, term_t store) {
  term_table_t* terms = uf->ctx->terms;
  assert(term_kind(terms, store) == UPDATE_TERM);

  composite_term_t* t_desc = update_term_desc(terms, store);
  return t_desc->arg[1];
}

static void make_rep_i(uf_plugin_t* uf, fun_node_t* n) {
  if (n->s == NULL) {
    return;
  }

  if (!eq_graph_are_equal(&uf->eq_graph,
                          n->s->pi, n->pi)) {
    n->s = n->s->p;
    n->sstore = n->s->pstore;
    make_rep_i(uf, n);
  } else {
    make_rep_i(uf, n->s);
    n->s->s = n;
    n->s->sstore = n->sstore;
    n->s = NULL;
    n->sstore = NULL_TERM;
  }
  assert(n->s == NULL);
  assert(n->sstore == NULL_TERM);
}

static void make_rep(uf_plugin_t* uf, fun_node_t* n) {
  if (n->p == NULL) {
    return;
  }

  make_rep(uf, n->p);
  // invert primary edge
  n->p->p = n;
  n->p->pstore = n->pstore;
  n->p->pi = n->pi;
  n->p = NULL;
  make_rep_i(uf, n);
  n->pstore = NULL_TERM;
  n->pi = NULL_TERM;
}

static void add_secondary(uf_plugin_t* uf, int_hset_t* idx_set,
                          fun_node_t* a, fun_node_t* b, term_t store) {
  fun_node_t* n = a;
  while (n != b) {
    assert(n->p);
    if (!int_hset_member(idx_set, n->pi) &&
        get_rep_i(&uf->eq_graph, n, n->pi) != b) {
      make_rep_i(uf, n);
      n->s = b;
      n->sstore = store;
    }
    int_hset_add(idx_set, n->pi);
    n = n->p;
  }
}

static void add_store(uf_plugin_t* uf, fun_node_t* a, fun_node_t* b,
                      term_t idx, term_t store) {
  if (a == b) {
    return;
  }

  make_rep(uf, b);
  if (get_rep(&uf->eq_graph, a) == b) {
    int_hset_t s;
    init_int_hset(&s, 0);
    int_hset_add(&s, idx);
    add_secondary(uf, &s, a, b, store);
    delete_int_hset(&s);
  } else {
    assert(b->p == NULL);
    b->p = a;
    b->pstore = store;
    b->pi = idx;
  }
}

/* * */

static
void uf_plugin_clear_fun_node_map(uf_plugin_t* uf) {
  ptr_hmap_pair_t *p;
  for (p = ptr_hmap_first_record(&uf->fun_node_map);
       p != NULL;
       p = ptr_hmap_next_record(&uf->fun_node_map, p)) {
    safe_free((fun_node_t *) p->val);
  }
  ptr_hmap_reset(&uf->fun_node_map);
  int_hmap_reset(&uf->fun_val_term_map);
}

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
  init_ptr_hmap(&uf->fun_val_type_map, 0);
  init_int_hmap(&uf->fun_val_term_map, 0);
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

  init_ivector(&uf->array_terms, 0);
  init_ivector(&uf->array_eq_terms, 0);
  init_ivector(&uf->select_terms, 0);

  init_int_hmap(&uf->type_to_diff, 0);
  init_int_hset(&uf->diff_funs, 0);
  init_ptr_hmap(&uf->fun_node_map, 0);
  
  // stats
  uf_plugin_stats_init(uf);
}

static
void uf_plugin_destruct(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;
  scope_holder_destruct(&uf->scope);
  delete_ivector(&uf->conflict);
  delete_ptr_hmap(&uf->fun_val_type_map);
  int_mset_destruct(&uf->tmp);
  eq_graph_destruct(&uf->eq_graph);
  delete_ivector(&uf->eq_graph_addition_trail);
  delete_ivector(&uf->array_terms);
  delete_ivector(&uf->array_eq_terms);
  delete_ivector(&uf->select_terms);

  delete_int_hmap(&uf->type_to_diff);
  delete_int_hset(&uf->diff_funs);
  uf_plugin_clear_fun_node_map(uf);
  delete_ptr_hmap(&uf->fun_node_map);
  delete_int_hmap(&uf->fun_val_term_map);
}

static
void uf_plugin_process_eq_graph_propagations(uf_plugin_t* uf, trail_token_t* prop) {
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
          } else {
            // Ignore, we will report conflict
          }
        }
      }
    }
    delete_ivector(&eq_propagations);
  }
}

static term_t uf_plugin_get_fun_rep(uf_plugin_t* uf, term_t t) {
  assert(eq_graph_term_has_value(&uf->eq_graph, t));

  mcsat_value_t* val = eq_graph_get_propagated_term_value(&uf->eq_graph, t);
  int32_t v_int = 0;
  bool ok = q_get32((rational_t*)&val->q, &v_int);
  (void) ok;

  int_hmap_pair_t *v = int_hmap_find(&uf->fun_val_term_map, v_int);
  if (v == NULL) {
    v = int_hmap_get(&uf->fun_val_term_map, v_int);
    v->val = t;
  }

  return v->val;
}

static fun_node_t *uf_plugin_get_fun_node(uf_plugin_t* uf, term_t t) {
  term_t t_rep = uf_plugin_get_fun_rep(uf, t);
  ptr_hmap_pair_t *v = ptr_hmap_find(&uf->fun_node_map, t_rep);
  if (v == NULL) {
    v = ptr_hmap_get(&uf->fun_node_map, t_rep);
    fun_node_t *n = new_node();
    n->t = t_rep;
    v->val = n;
  }

  return v->val;
}

static void uf_plugin_compute_weak_path(uf_plugin_t* uf, fun_node_t* a,
                                        fun_node_t* b, int_hset_t* indices,
                                        int_hset_t* path) {
  //ctx_trace_printf(uf->ctx, "WEAK PATH\n ");

  //arr1 and arr2 must be in the same weak equivalence class
  assert(get_rep(&uf->eq_graph, a) == get_rep(&uf->eq_graph, b));

  if (a == b) {
    return;
  }

  uint32_t prim_cnt1 = count_primary(&uf->eq_graph, a);
  uint32_t prim_cnt2 = count_primary(&uf->eq_graph, b);
  fun_node_t* n1 = a;
  fun_node_t* n2 = b;

  while (prim_cnt1 > prim_cnt2) {
    int_hset_add(path, n1->pstore);
    assert(n1->pi == uf_plugin_get_index_from_store(uf, n1->pstore));
    int_hset_add(indices, n1->pi);
    n1 = n1->p;
    prim_cnt1--;
  }
  while (prim_cnt2 > prim_cnt1) {
    int_hset_add(path, n2->pstore);
    assert(n2->pi == uf_plugin_get_index_from_store(uf, n2->pstore));
    int_hset_add(indices, n2->pi);
    n2 = n2->p;
    prim_cnt2--;
  }
  while (n1 != n2) {
    assert(n1->p);
    assert(n2->p);
    int_hset_add(path, n1->pstore);
    int_hset_add(path, n2->pstore);
    assert(n1->pi == uf_plugin_get_index_from_store(uf, n1->pstore));
    assert(n2->pi == uf_plugin_get_index_from_store(uf, n2->pstore));
    int_hset_add(indices, n1->pi);
    int_hset_add(indices, n2->pi);
    n1 = n1->p;
    n2 = n2->p;
  }

  assert(n1 == n2);
}

static fun_node_t* uf_plugin_compute_path_secondary(uf_plugin_t* uf, fun_node_t* a,
                                                    term_t idx,
                                                    int_hset_t* indices,
                                                    int_hset_t* path) {
  fun_node_t* res = NULL;
  term_table_t* terms = uf->ctx->terms;
  const fun_node_t* tmp = find_secondary_node(&uf->eq_graph, a, idx);
  composite_term_t* t_desc = update_term_desc(terms, tmp->sstore);

  assert(tmp->pi != NULL_TERM);
  assert(tmp->s);
  assert(eq_graph_are_equal(&uf->eq_graph, tmp->pi, idx));
  if (t_desc->arg[1] == idx) {
    //ctx_trace_term(uf->ctx, tmp->sstore);
    //ctx_trace_term(uf->ctx, t_desc->arg[1]);
    //ctx_trace_term(uf->ctx, idx);
    //ctx_trace_term(uf->ctx, tmp->pstore);
    //ctx_trace_term(uf->ctx, tmp->pi);
  }

  int_hset_add(path, a->t);

  if (find_secondary_node(&uf->eq_graph, uf_plugin_get_fun_node(uf, t_desc->arg[0]), idx) != tmp) {
    uf_plugin_compute_weak_path(uf, a, uf_plugin_get_fun_node(uf, tmp->sstore), indices, path);
    res = tmp->s;
    int_hset_add(path, tmp->sstore);
  } else {
    uf_plugin_compute_weak_path(uf, a, uf_plugin_get_fun_node(uf, t_desc->arg[0]), indices, path);
    res = uf_plugin_get_fun_node(uf, tmp->sstore);
    int_hset_add(path, t_desc->arg[0]);
  }

  int_hset_add(indices, t_desc->arg[1]);

  return res;
}

static void uf_plugin_compute_weak_path_i(uf_plugin_t* uf, term_t arr1,
                                          term_t arr2, term_t idx,
                                          int_hset_t* indices,
                                          int_hset_t* path) {
  //ctx_trace_printf(uf->ctx, "WEAK PATH I\n ");
  term_table_t* terms = uf->ctx->terms;

  fun_node_t* a = uf_plugin_get_fun_node(uf, arr1);
  fun_node_t* b = uf_plugin_get_fun_node(uf, arr2);
  uint32_t sec_cnt1 = count_secondary(&uf->eq_graph, a, idx);  
  uint32_t sec_cnt2 = count_secondary(&uf->eq_graph, b, idx);

  assert(get_rep_i(&uf->eq_graph, a, idx) == get_rep_i(&uf->eq_graph, b, idx));

  int_hset_add(path, arr1);
  while (sec_cnt1 > sec_cnt2) {
    a = uf_plugin_compute_path_secondary(uf, a, idx, indices, path);
    sec_cnt1--;
    assert(count_secondary(&uf->eq_graph, a, idx) == sec_cnt1);
    assert(get_rep_i(&uf->eq_graph, a, idx) == get_rep_i(&uf->eq_graph, b, idx));
  }
  while (sec_cnt2 > sec_cnt1) {
    b = uf_plugin_compute_path_secondary(uf, b, idx, indices, path);
    sec_cnt2--;
    assert(count_secondary(&uf->eq_graph, b, idx) == sec_cnt2);
    assert(get_rep_i(&uf->eq_graph, a, idx) == get_rep_i(&uf->eq_graph, b, idx));
  }

  assert(sec_cnt1 == sec_cnt2);
  while (sec_cnt1 > 0 && find_secondary_node(&uf->eq_graph, a, idx) != find_secondary_node(&uf->eq_graph, b, idx)) {
    assert(count_secondary(&uf->eq_graph, a, idx) == count_secondary(&uf->eq_graph, b, idx));
    a = uf_plugin_compute_path_secondary(uf, a, idx, indices, path);
    b = uf_plugin_compute_path_secondary(uf, b, idx, indices, path);
    assert(get_rep_i(&uf->eq_graph, a, idx) == get_rep_i(&uf->eq_graph, b, idx));
  }

  uf_plugin_compute_weak_path(uf, a, b, indices, path);
  
  int_hset_add(path, arr2);
}

static void uf_plugin_add_diff_terms_vars(uf_plugin_t* uf, term_t arr) {
  term_table_t* terms = uf->ctx->terms;
  type_t arr_type = term_type(terms, arr);
  type_t idx_type = function_type_domain(uf->ctx->types, arr_type, 0);

  term_t diff_fun;
  int_hmap_pair_t *diff = int_hmap_find(&uf->type_to_diff, arr_type);
  if (diff != NULL) {
    diff_fun = diff->val;
  } else {
    type_t dom[] = {arr_type, arr_type};
    type_t diff_fun_type = function_type(uf->ctx->types, idx_type, 2, dom);
    diff_fun = new_uninterpreted_term(terms, diff_fun_type);

    char fun_name_str[10];
    sprintf(fun_name_str, "diff_%i", uf->type_to_diff.nelems);
    set_term_name(terms, diff_fun, clone_string(fun_name_str));

    int_hmap_add(&uf->type_to_diff, arr_type, diff_fun);
    int_hset_add(&uf->diff_funs, diff_fun);
  }

  variable_db_get_variable(uf->ctx->var_db, arr);
  uint32_t i;
  for (i = 0; i < uf->array_terms.size; ++ i) {
    term_t arr2 = uf->array_terms.data[i];
    if (arr == arr2) {
      continue;
    }

    type_t arr2_type = term_type(terms, arr2);
    if (arr_type == arr2_type) {
      variable_db_get_variable(uf->ctx->var_db, arr2);

      term_t args[2];
      if (arr < arr2) {
        args[0] = arr;
        args[1] = arr2;
      } else {
        args[0] = arr2;
        args[1] = arr;
      }

      term_t diff_term = app_term(terms, diff_fun, 2, args);
      term_t select_arg[] = {diff_term};
      term_t diff_select1 = app_term(terms, arr, 1, select_arg);
      term_t diff_select2 = app_term(terms, arr2, 1, select_arg);
      variable_db_get_variable(uf->ctx->var_db, diff_term);
      variable_db_get_variable(uf->ctx->var_db, diff_select1);
      variable_db_get_variable(uf->ctx->var_db, diff_select2);

      ivector_push(&uf->select_terms, diff_select1);
      ivector_push(&uf->select_terms, diff_select2);
    }
  }
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
    if (!int_hset_member(&uf->diff_funs, t_desc->arg[0])) {
      ivector_push(&uf->select_terms, t);
    }
    break;
  case UPDATE_TERM:
    if (USE_ARRAY_DIFF) {
      uf_plugin_add_diff_terms_vars(uf, t);
    }
    t_desc = update_term_desc(terms, t);
    eq_graph_add_ufun_term(&uf->eq_graph, t, t, t_desc->arity, t_desc->arg);
    // remember array term
    ivector_push(&uf->array_terms, t);
    // remember select terms
    term_t r1 = app_term(terms, t, t_desc->arity - 2, t_desc->arg + 1);
    variable_db_get_variable(uf->ctx->var_db, r1);
    ivector_push(&uf->select_terms, r1);
    term_t r2 = app_term(terms, t_desc->arg[0], t_desc->arity - 2, t_desc->arg + 1);
    variable_db_get_variable(uf->ctx->var_db, r2);
    ivector_push(&uf->select_terms, r2);
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
      ivector_push(&uf->array_eq_terms, t);
    }
    uint32_t i;
    for (i = 0; i < 2; ++ i) {
      if (is_function_term(terms, t_desc->arg[i])) {
        if (USE_ARRAY_DIFF) {
          uf_plugin_add_diff_terms_vars(uf, t_desc->arg[i]);
        }
        ivector_push(&uf->array_terms, t_desc->arg[i]);
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
    if (is_function_term(terms, c)) {
      if (USE_ARRAY_DIFF) {
        uf_plugin_add_diff_terms_vars(uf, c);
      }
      ivector_push(&uf->array_terms, c);
    }
    if (term_kind(terms, c) == APP_TERM &&
        !int_hset_member(&uf->diff_funs, c)) {
      ivector_push(&uf->select_terms, c);
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
    composite_term_t* t_desc = update_term_desc(terms, t);
    term_t r = app_term(terms, t, t_desc->arity - 2, t_desc->arg + 1);
    variable_db_get_variable(uf->ctx->var_db, r);
    term_t r_lemma = _o_yices_eq(r, t_desc->arg[t_desc->arity - 1]);
    prop->definition_lemma(prop, r_lemma, t);
  }
}

static
bool uf_plugin_array_idx_check(uf_plugin_t* uf, trail_token_t* prop,
                               const ivector_t* array_terms) {
  term_table_t* terms = uf->ctx->terms;
  uint32_t i;

  // array-idx lemma
  for (i = 0; i < array_terms->size; ++i) {
    term_t arr = array_terms->data[i];
    term_kind_t t_kind = term_kind(terms, arr);
    if (t_kind == UPDATE_TERM) {
      composite_term_t* t_desc = update_term_desc(terms, arr);
      term_t r = app_term(terms, arr, t_desc->arity - 2, t_desc->arg + 1);
      term_t v = t_desc->arg[t_desc->arity - 1];
      if (!eq_graph_term_has_value(&uf->eq_graph, r) ||
          !eq_graph_term_has_value(&uf->eq_graph, v))
        continue;
      if (!eq_graph_are_equal(&uf->eq_graph, r, v)) {
        add_if_not_true_term(&uf->conflict, _o_yices_neq(r, v));

        if (ctx_trace_enabled(uf->ctx, "uf_plugin::array")) {
          ctx_trace_printf(uf->ctx, ">1 Array conflict 1 BEGIN\n");
          uint32_t k;
          for (k = 0; k < uf->conflict.size; ++ k) {
            ctx_trace_term(uf->ctx, uf->conflict.data[k]);
          }
          ctx_trace_printf(uf->ctx, ">1 Array conflict 1 END\n");
        }
        return false;
      }
    }
  }
  return true;
}

static
bool uf_plugin_array_weak_eq_i(uf_plugin_t* uf, term_t arr1, term_t arr2,
                               term_t idx,
                               ivector_t* indices, ivector_t* cond) {
  term_table_t* terms = uf->ctx->terms;
  //ctx_trace_printf(uf->ctx, "CHECKING ARRAY WEAK EQ I\n ");

  int_hset_t index_set, path;
  bool res = false;
  uint32_t old_indices_size, old_cond_size;

  const fun_node_t* fn_arr1 = get_rep_i(&uf->eq_graph, uf_plugin_get_fun_node(uf, arr1),
                                        idx);
  const fun_node_t* fn_arr2 = get_rep_i(&uf->eq_graph, uf_plugin_get_fun_node(uf, arr2),
                                        idx);
  assert(fn_arr1 != NULL);
  assert(fn_arr2 != NULL);

  init_int_hset(&index_set, 0);
  init_int_hset(&path, 0);

  if (indices) {
    old_indices_size = indices->size;
  }
  if (cond) {
    old_cond_size = cond->size;
  }

  if (fn_arr1 == fn_arr2) {
    composite_term_t* t_desc = NULL;
    uint32_t k;

    res = true;
    uf_plugin_compute_weak_path_i(uf, arr1, arr2, idx, &index_set, &path);

    // add indices
    int_hset_close(&index_set);
    for (k = 0; k < index_set.nelems; ++k) {
      if (eq_graph_are_equal(&uf->eq_graph, idx, index_set.data[k])) {
        res = false;
        break;
      }
      ivector_push(indices, index_set.data[k]);
    }
    
    int_hset_close(&path);
    // add path eq conditions
    for (k = 0; res && k < path.nelems; ++k) {
      add_if_not_true_term(cond,
                           _o_yices_eq(path.data[k],
                                       uf_plugin_get_fun_rep(uf, path.data[k])));
    }
  }

  if (!res && indices) {
    ivector_shrink(indices, old_indices_size);
  }

  if (!res && cond) {
    ivector_shrink(cond, old_cond_size);
  }

  delete_int_hset(&path);

  return res;
}

static
bool uf_plugin_array_weak_congruence_i(uf_plugin_t* uf, const ivector_t* select_terms,
                                       term_t arr1, term_t arr2,
                                       term_t idx, ivector_t* cond) {
  assert(eq_graph_term_has_value(&uf->eq_graph, idx));

  bool res = false;
  term_table_t* terms = uf->ctx->terms;

  uint32_t i, j, k;
  uint32_t cond_old_size;
  
  ivector_t indices;
  init_ivector(&indices, 0);

  if (cond) {
    cond_old_size = cond->size;
  }

  if (uf_plugin_array_weak_eq_i(uf, arr1, arr2, idx, &indices, cond)) {
    for (k =0; k < indices.size; ++k) {
      assert(idx != indices.data[k]);
      if (eq_graph_are_equal(&uf->eq_graph, idx, indices.data[k])) {
        goto nextcheck;
      }
    }

    res = true;

    for (k =0; k < indices.size; ++k) {
      add_if_not_true_term(cond, _o_yices_neq(idx, indices.data[k]));
    }

    add_if_not_true_term(cond,
                         _o_yices_eq(arr1,
                                     uf_plugin_get_fun_rep(uf, arr1)));
    add_if_not_true_term(cond,
                         _o_yices_eq(arr2,
                                     uf_plugin_get_fun_rep(uf, arr2)));
    goto done;
  }

 nextcheck:
  if (cond) {
    ivector_shrink(cond, cond_old_size);
  }

  for (i = 0; !res && i < select_terms->size; ++ i) {
    term_t t_i = select_terms->data[i];
    type_t t_i_type = term_type(terms, t_i);
    assert(variable_db_get_variable_if_exists(uf->ctx->var_db, t_i) != variable_null);

    ivector_shrink(&indices, 0);
    composite_term_t* e_i_desc = app_term_desc(terms, t_i);
    if (!eq_graph_are_equal(&uf->eq_graph, e_i_desc->arg[1], idx) ||
        !uf_plugin_array_weak_eq_i(uf, arr1, e_i_desc->arg[0], idx, &indices, cond)) {
      assert(indices.size == 0);
      continue;
    }

    uint32_t size1 = cond->size;
    for (j = 0; !res && j < select_terms->size; ++ j) {
      ivector_shrink(cond, size1);
      term_t t_j = select_terms->data[j];
      type_t t_j_type = term_type(terms, t_j);
      if (t_i_type != t_j_type ||
          !eq_graph_are_equal(&uf->eq_graph, t_i, t_j)) {
        continue;
      }
      
      composite_term_t* e_j_desc = app_term_desc(terms, t_j);
      if (!eq_graph_are_equal(&uf->eq_graph, e_j_desc->arg[1], idx) ||
          !uf_plugin_array_weak_eq_i(uf, arr2, e_j_desc->arg[0], idx, &indices, cond)) {
        continue;
      }
      
      res = true;
      if (cond) {
        // Conditions of arr1 weakly-eq-i to a and arr2 weakly-eq-i to b'
        for (k = 0; k < indices.size; ++k) {
          if (eq_graph_are_equal(&uf->eq_graph, indices.data[k], idx)) {
            res = false;
            break;
          }
        }

        if (res) {
          add_if_not_true_term(cond, _o_yices_eq(arr1,
                                                 uf_plugin_get_fun_rep(uf, arr1)));
          add_if_not_true_term(cond, _o_yices_eq(arr2,
                                                 uf_plugin_get_fun_rep(uf, arr2)));
          add_if_not_true_term(cond, _o_yices_eq(e_i_desc->arg[0],
                                                 uf_plugin_get_fun_rep(uf, e_i_desc->arg[0])));
          add_if_not_true_term(cond, _o_yices_eq(e_j_desc->arg[0],
                                                 uf_plugin_get_fun_rep(uf, e_j_desc->arg[0])));
          for (k =0; k < indices.size; ++k) {
            add_if_not_true_term(cond, _o_yices_neq(idx, indices.data[k]));
          }
          add_if_not_true_term(cond, _o_yices_eq(idx, e_i_desc->arg[1]));
          add_if_not_true_term(cond, _o_yices_eq(t_i, t_j));
          add_if_not_true_term(cond, _o_yices_eq(idx, e_j_desc->arg[1]));
        }
      }
    }
  }

 done:
  if (!res && cond) {
    ivector_shrink(cond, cond_old_size);
  }

  delete_ivector(&indices);
  return res;
}

static
bool uf_plugin_array_ext_check(uf_plugin_t* uf, trail_token_t* prop,
                               const ivector_t* array_terms,
                               const ivector_t* select_terms) {
  //ctx_trace_printf(uf->ctx, "ARRAY EXT CHECK \n");

  term_table_t* terms = uf->ctx->terms;
  uint32_t i, j, k;

  ivector_t cond;
  int_hset_t path, indices;

  init_ivector(&cond, 0);
  init_int_hset(&path, 0);
  init_int_hset(&indices, 0);

  for (i = 0; i < array_terms->size; ++i) {
    term_t arr1 = array_terms->data[i];
    type_t arr1_type = term_type(terms, arr1);
    assert(variable_db_get_variable_if_exists(uf->ctx->var_db, arr1) != variable_null);
    
    for (j = i + 1; j < array_terms->size; ++j) {
      term_t arr2 = array_terms->data[j];
      type_t arr2_type = term_type(terms, arr2);
      if (arr1 == arr2 || arr1_type != arr2_type ||
          eq_graph_are_equal(&uf->eq_graph, arr1, arr2)) {
        continue;
      }
      
      const fun_node_t* fn_arr1 = get_rep(&uf->eq_graph, uf_plugin_get_fun_node(uf, arr1));
      const fun_node_t* fn_arr2 = get_rep(&uf->eq_graph, uf_plugin_get_fun_node(uf, arr2));

      if (fn_arr1 == fn_arr2) {
        bool ok = true;
        composite_term_t* t_desc = NULL;

        ivector_shrink(&cond, 0);
        int_hset_reset(&path);
        int_hset_reset(&indices);
        uf_plugin_compute_weak_path(uf, uf_plugin_get_fun_node(uf, arr1),
                                    uf_plugin_get_fun_node(uf, arr2), &indices, &path);
        int_hset_close(&path);
        int_hset_close(&indices);
        for (k = 0; ok && k < indices.nelems; ++ k) {
          //ctx_trace_printf(uf->ctx, ">2 Trying INDEX: ");
          term_t idx = indices.data[k];
          if (!uf_plugin_array_weak_congruence_i(uf, select_terms, arr1, arr2,
                                                 idx, &cond)) {
            ok = false;
            break;
          }
        }

        if (ok) {
          for (k = 0; k < path.nelems; ++k) {
            add_if_not_true_term(&uf->conflict,
                                 _o_yices_eq(path.data[k],
                                             uf_plugin_get_fun_rep(uf, path.data[k])));
          }

          add_if_not_true_term(&uf->conflict,
                               _o_yices_eq(arr1,
                                           uf_plugin_get_fun_rep(uf, arr1)));
          add_if_not_true_term(&uf->conflict,
                               _o_yices_eq(arr2,
                                           uf_plugin_get_fun_rep(uf, arr2)));

          for (k = 0; k < cond.size; ++k) {
            add_if_not_true_term(&uf->conflict, cond.data[k]);
          }

          ivector_push(&uf->conflict, _o_yices_neq(arr1, arr2));

          ivector_remove_duplicates(&uf->conflict);

          if (ctx_trace_enabled(uf->ctx, "uf_plugin::array")) {
            ctx_trace_printf(uf->ctx, ">2 Array conflict BEGIN 2\n");
            for (k = 0; k < uf->conflict.size; ++ k) {
              ctx_trace_term(uf->ctx, uf->conflict.data[k]);
            }
            ctx_trace_printf(uf->ctx, ">2 Array conflict END 2\n");
          }

          assert(uf->conflict.size > 1);

          goto done;
        }
      }
    }
  }

 done:
  delete_ivector(&cond);
  delete_int_hset(&path);

  return (uf->conflict.size == 0);
}

static
bool uf_plugin_array_ext_diff_lemma(uf_plugin_t* uf, trail_token_t* prop,
                                    term_t arr1, term_t arr2) {

  term_table_t* terms = uf->ctx->terms;
  type_t arr1_type = term_type(terms, arr1);
  term_t diff_fun;
  int_hmap_pair_t *diff = int_hmap_find(&uf->type_to_diff, arr1_type);
  if (diff != NULL) {
    diff_fun = diff->val;
  } else {
    assert(false);
  }

  type_t arr2_type = term_type(terms, arr2);
  if (arr1 == arr2 ||
      !eq_graph_term_has_value(&uf->eq_graph, arr1) ||
      !eq_graph_term_has_value(&uf->eq_graph, arr2) ||
      arr1_type != arr2_type) {
    return true;
  }
      
  term_t args[2];
  if (arr1 < arr2) {
    args[0] = arr1;
    args[1] = arr2;
  } else {
    args[0] = arr2;
    args[1] = arr1;
  }
  term_t diff_term = app_term(terms, diff_fun, 2, args);
  term_t select_arg[] = {diff_term};
  term_t diff_select1 = app_term(terms, arr1, 1, select_arg);
  term_t diff_select2 = app_term(terms, arr2, 1, select_arg);
  if (!eq_graph_term_has_value(&uf->eq_graph, diff_term) ||
      !eq_graph_term_has_value(&uf->eq_graph, diff_select1) ||
      !eq_graph_term_has_value(&uf->eq_graph, diff_select2)) {
    return true;
  }
      
  if (!eq_graph_are_equal(&uf->eq_graph, arr1, arr2) &&
      eq_graph_are_equal(&uf->eq_graph, diff_select1, diff_select2)) {
      
    add_if_not_true_term(&uf->conflict, _o_yices_neq(arr1, arr2));
    add_if_not_true_term(&uf->conflict, _o_yices_eq(diff_select1, diff_select2));

    ivector_remove_duplicates(&uf->conflict);

    if (ctx_trace_enabled(uf->ctx, "uf_plugin::array")) {
      ctx_trace_printf(uf->ctx, ">2 Array conflict 2 BEGIN\n");
      uint32_t k;
      for (k = 0; k < uf->conflict.size; ++ k) {
        ctx_trace_term(uf->ctx, uf->conflict.data[k]);
      }
      ctx_trace_printf(uf->ctx, ">2 Array conflict 2 END\n");
    }

    assert(uf->conflict.size > 1);

    return false;
  }

  return true;
}

static
bool uf_plugin_array_ext_diff_check(uf_plugin_t* uf, trail_token_t* prop,
                                    const ivector_t* array_eq_terms,
                                    const ivector_t* array_terms) {

  bool res = true;
  term_table_t* terms = uf->ctx->terms;
  uint32_t i, j, k;

  if (array_eq_terms) {
    composite_term_t* t_desc = NULL;
    for (i = 0; res && i < array_eq_terms->size; ++i) {
      t_desc = eq_term_desc(terms, array_eq_terms->data[i]);
      term_t arr1 = t_desc->arg[0];
      term_t arr2 = t_desc->arg[1];

      res = uf_plugin_array_ext_diff_lemma(uf, prop, arr1, arr2);
    }
  }

  if (array_terms) {
    for (i = 0; res && i < array_terms->size; ++i) {
      term_t arr1 = array_terms->data[i];
      assert(variable_db_get_variable_if_exists(uf->ctx->var_db, arr1) != variable_null);
      if (!eq_graph_term_has_value(&uf->eq_graph, arr1)) {
        continue;
      }

      for (j = i + 1; res && j < array_terms->size; ++j) {
        term_t arr2 = array_terms->data[j];
        res = uf_plugin_array_ext_diff_lemma(uf, prop, arr1, arr2);
      }
    }
  }

  return res;
}

static
bool uf_plugin_array_read_over_write_check(uf_plugin_t* uf, trail_token_t* prop,
                                           const ivector_t* array_terms,
                                           const ivector_t* select_terms) {
  term_table_t* terms = uf->ctx->terms;
  uint32_t i, j, k;

  ivector_t cond, indices;
  init_ivector(&cond, 0);
  init_ivector(&indices, 0);

  //ctx_trace_printf(uf->ctx, "CHECKING READ OVER WRITE\n ");

  // generalized read-over-write lemma
  for (i = 0; i < select_terms->size; ++ i) {
    term_t t_i = select_terms->data[i];
    type_t t_i_type = term_type(terms, t_i);
    assert(variable_db_get_variable_if_exists(uf->ctx->var_db, t_i) != variable_null);
    composite_term_t* e_i_desc = app_term_desc(terms, t_i);

    //ctx_trace_printf(uf->ctx, "SELECT TERM 1 : ");
    //ctx_trace_term(uf->ctx, t_i);
    for (j = 1; j < select_terms->size; ++ j) {
      term_t t_j = select_terms->data[j];
      type_t t_j_type = term_type(terms, t_j);
      composite_term_t* e_j_desc = app_term_desc(terms, t_j);
      if (t_i == t_j ||
          t_i_type != t_j_type ||
          !eq_graph_are_equal(&uf->eq_graph, e_i_desc->arg[1], e_j_desc->arg[1]) ||
          //eq_graph_are_equal(&uf->eq_graph, e_i_desc->arg[0], e_j_desc->arg[0]) ||
          eq_graph_are_equal(&uf->eq_graph, t_i, t_j)) {
        continue;
      }
      
      //ctx_trace_printf(uf->ctx, "SELECT TERM 2 : ");
      //ctx_trace_term(uf->ctx, t_j);

      ivector_shrink(&indices, 0);
      ivector_shrink(&cond, 0);

      if (uf_plugin_array_weak_eq_i(uf, e_i_desc->arg[0], e_j_desc->arg[0],
                                    e_i_desc->arg[1], &indices, &cond)) {
        //ctx_trace_printf(uf->ctx, "FOUND CONFLICT\n ");
        // found conflict
        assert(uf->conflict.size == 0);
        add_if_not_true_term(&uf->conflict,
                             _o_yices_eq(e_i_desc->arg[0],
                                         uf_plugin_get_fun_rep(uf, e_i_desc->arg[0])));
        add_if_not_true_term(&uf->conflict,
                             _o_yices_eq(e_j_desc->arg[0],
                                         uf_plugin_get_fun_rep(uf, e_j_desc->arg[0])));

        add_if_not_true_term(&uf->conflict, _o_yices_eq(e_i_desc->arg[1], e_j_desc->arg[1]));
        add_if_not_true_term(&uf->conflict, _o_yices_neq(t_i, t_j));

        bool ok = true;
        for (k = 0; k < indices.size; ++ k) {
          assert(indices.data[k] != e_i_desc->arg[1]);
          if (eq_graph_are_equal(&uf->eq_graph,
                                 e_i_desc->arg[1], indices.data[k])) {
            ok = false;
            break;
          }

          add_if_not_true_term(&uf->conflict,
                               _o_yices_neq(e_i_desc->arg[1], indices.data[k]));
        }

        if (!ok) {
          ivector_reset(&uf->conflict);
        } else {
          for (k = 0; k < cond.size; ++k) {
            add_if_not_true_term(&uf->conflict, cond.data[k]);
          }

          ivector_remove_duplicates(&uf->conflict);

          if (ctx_trace_enabled(uf->ctx, "uf_plugin::array")) {
            ctx_trace_printf(uf->ctx, ">3 Array conflict BEGIN 3\n");
            for (k = 0; k < uf->conflict.size; ++ k) {
              ctx_trace_term(uf->ctx, uf->conflict.data[k]);
            }
            ctx_trace_printf(uf->ctx, ">3 Array conflict END 3\n");
          }

          assert(uf->conflict.size > 1);

          goto done;
        }
      }
    }
  }

 done:
  delete_ivector(&indices);
  delete_ivector(&cond);

  return uf->conflict.size == 0;
}

static
void uf_plugin_array_build_weak_eq_graph(uf_plugin_t* uf, const ivector_t* array_terms) {
  term_table_t* terms = uf->ctx->terms;
  uint32_t i;

  // clear the fun node map
  // we start from a fresh weak equivalence graph
  uf_plugin_clear_fun_node_map(uf);

  // build the graph
  for (i = 0; i < array_terms->size; ++ i) {
    term_t t = array_terms->data[i];
    term_kind_t t_kind = term_kind(terms, t);
    assert(is_function_term(terms, t));
    assert(t_kind == UNINTERPRETED_TERM || t_kind == UPDATE_TERM);

    if (t_kind == UPDATE_TERM) {
      fun_node_t *b = uf_plugin_get_fun_node(uf, t);
      composite_term_t* t_desc = update_term_desc(terms, t);
      fun_node_t *a = uf_plugin_get_fun_node(uf, t_desc->arg[0]);
      term_t ai = t_desc->arg[1];
      add_store(uf, a, b, ai, t);
    }
  }
}

static
void uf_plugin_array_propagations(uf_plugin_t* uf, trail_token_t* prop) {

  bool ok = true;

  ivector_t array_terms;
  init_ivector(&array_terms, 0);
  ivector_copy(&array_terms, uf->array_terms.data, uf->array_terms.size);
  ivector_remove_duplicates(&array_terms);

  ivector_t select_terms;
  init_ivector(&select_terms, 0);
  ivector_copy(&select_terms, uf->select_terms.data, uf->select_terms.size);
  ivector_remove_duplicates(&select_terms);

  //ok = uf_plugin_array_idx_check(uf, prop, &array_terms);

  bool updates_present = false;

  // check if all the revlevant terms have an assigned value
  uint32_t i;
  term_table_t* terms = uf->ctx->terms;
  composite_term_t* t_desc = NULL;
  for (i = 0; ok && i < array_terms.size; ++i) {
    if (!eq_graph_term_has_value(&uf->eq_graph, array_terms.data[i])) {
      ok = false;
    }
    if (term_kind(terms, array_terms.data[i]) == UPDATE_TERM) {
      updates_present = true;
    }
  }
  for (i = 0; ok && i < select_terms.size; ++i) {
    if (!eq_graph_term_has_value(&uf->eq_graph, select_terms.data[i])) {
      ok = false;
    } else {
      t_desc = app_term_desc(terms, select_terms.data[i]);
      if (!eq_graph_term_has_value(&uf->eq_graph, t_desc->arg[1])) {
        ok = false;
      }
    }
  }
  
  if (USE_ARRAY_DIFF && ok) {
    ok = uf_plugin_array_ext_diff_check(uf, prop, &uf->array_eq_terms, NULL);
  }

  if (ok) {
    if (!USE_ARRAY_DIFF || updates_present) {
      uf_plugin_array_build_weak_eq_graph(uf, &array_terms);
    }
    if (updates_present) {
      ok = uf_plugin_array_read_over_write_check(uf, prop, &array_terms, &select_terms); 
    }
  }

  if (ok) {
    if (USE_ARRAY_DIFF) {
      ok = uf_plugin_array_ext_diff_check(uf, prop, NULL, &array_terms);
    } else {
      ok = uf_plugin_array_ext_check(uf, prop, &array_terms, &select_terms);
    }
  }

  if (uf->conflict.size > 0) {
    // Report conflict
    prop->conflict(prop);
    (*uf->stats.conflicts) ++;
    //ivector_copy(&uf->tmp, &uf->conflict, uf->conflict.size);
    //uf_plugin_bump_terms_and_reset(uf, &uf->tmp);
    statistic_avg_add(uf->stats.avg_conflict_size, uf->conflict.size);
  }

  delete_ivector(&select_terms);
  delete_ivector(&array_terms);
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

  if (uf->array_terms.size > 0) {
    uf_plugin_array_propagations(uf, prop);
  }
}

static
void uf_plugin_push(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  // Push the int variable values
  scope_holder_push(&uf->scope,
                    &uf->eq_graph_addition_trail.size,
                    &uf->array_terms.size,
                    &uf->array_eq_terms.size,
                    &uf->select_terms.size,
                    NULL);

  eq_graph_push(&uf->eq_graph);
}

static
void uf_plugin_pop(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  uint32_t old_eq_graph_addition_trail_size;
  uint32_t t1, t2, t3;

  // Pop the int variable values
  scope_holder_pop(&uf->scope,
                   &old_eq_graph_addition_trail_size,
                   &t1, &t2, &t3,
                   NULL);

  ivector_shrink(&uf->array_terms, t1);
  ivector_shrink(&uf->array_eq_terms, t2);
  ivector_shrink(&uf->select_terms, t3);

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

      while (true) {
        ptr_hmap_pair_t *picked_val_type = ptr_hmap_find(&uf->fun_val_type_map, picked_value);
        // if not in the map, pick it and safe in the map
        if (picked_val_type == NULL) {
          picked_val_type = ptr_hmap_get(&uf->fun_val_type_map, picked_value);
          picked_val_type->val = x_type;
          break;
        }
        // if in the map and the type agrees then pick the value
        if (picked_val_type->val == x_type) {
          break;
        }
        // picked value not good, increment and check in the loop
        picked_value += 1;
      }
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
