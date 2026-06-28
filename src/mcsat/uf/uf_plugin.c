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
#include "utils/ptr_vectors.h"
#include "utils/refcount_strings.h"

#include "model/fresh_value_maker.h"
#include "model/models.h"

#include "terms/terms.h"
#include "inttypes.h"


#define DECIDE_FUNCTION_VALUE_START UINT32_MAX/64
#define UF_FUN_DISEQ_WITNESS_CAP UINT32_MAX
#define UF_FUN_CARDINALITY_CLIQUE_TERM_CAP 64


typedef enum {
  UF_FUN_DISEQ_EXPLICIT,
  UF_FUN_DISEQ_DISTINCT_ID,
} uf_fun_diseq_source_t;

typedef struct {
  term_t lhs;
  term_t rhs;
  type_t type;
  uint32_t arity;
  uf_fun_diseq_source_t source;
  term_t guard;
  term_t* diff_terms;
  term_t lhs_app;
  term_t rhs_app;
  bool lemma_emitted;
} uf_fun_diseq_t;


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

  /** Scoped committed function disequalities */
  pvector_t fun_diseq_entries;

  /** Active function-id view rebuilt from the current trail */
  ivector_t active_fun_terms;
  ivector_t active_fun_types;
  ivector_t active_fun_ids;

  /** Tmp vector */
  int_mset_t tmp;

  struct {
    statistic_int_t* egraph_terms;
    statistic_int_t* fun_diseq_explicit;
    statistic_int_t* fun_diseq_distinct_id;
    statistic_int_t* fun_diseq_incompatible_id_merges;
    statistic_int_t* fun_diseq_witnesses;
    statistic_int_t* propagations;
    statistic_int_t* conflicts;
    statistic_avg_t* avg_conflict_size;
    statistic_avg_t* avg_explanation_size;
  } stats;

  /** Exception handler */
  jmp_buf* exception;

} uf_plugin_t;


static void uf_plugin_free_fun_diseq_entries_from(uf_plugin_t* uf, uint32_t old_size) {
  while (uf->fun_diseq_entries.size > old_size) {
    uf_fun_diseq_t* entry = pvector_pop2(&uf->fun_diseq_entries);
    safe_free(entry->diff_terms);
    safe_free(entry);
  }
}

static bool uf_plugin_is_first_order_function_type(type_table_t* types, type_t tau) {
  uint32_t i, n;

  if (type_kind(types, tau) != FUNCTION_TYPE ||
      type_kind(types, function_type_range(types, tau)) == FUNCTION_TYPE) {
    return false;
  }

  n = function_type_arity(types, tau);
  for (i = 0; i < n; ++ i) {
    if (type_kind(types, function_type_domain(types, tau, i)) == FUNCTION_TYPE) {
      return false;
    }
  }

  return true;
}

static void uf_plugin_order_fun_pair(term_t* lhs, term_t* rhs) {
  term_t tmp;

  if (*rhs < *lhs) {
    tmp = *lhs;
    *lhs = *rhs;
    *rhs = tmp;
  }
}

static uf_fun_diseq_t* uf_plugin_find_fun_diseq_entry(uf_plugin_t* uf, term_t lhs, term_t rhs) {
  uint32_t i;

  uf_plugin_order_fun_pair(&lhs, &rhs);

  for (i = 0; i < uf->fun_diseq_entries.size; ++ i) {
    uf_fun_diseq_t* entry = uf->fun_diseq_entries.data[i];
    if (entry->lhs == lhs && entry->rhs == rhs) {
      return entry;
    }
  }

  return NULL;
}

static void uf_plugin_register_diff_witness_terms(uf_plugin_t* uf, uf_fun_diseq_t* entry) {
  uint32_t i;

  assert(uf->ctx->register_term != NULL);

  uf->ctx->register_term(uf->ctx, entry->lhs);
  uf->ctx->register_term(uf->ctx, entry->rhs);
  for (i = 0; i < entry->arity; ++ i) {
    uf->ctx->register_term(uf->ctx, entry->diff_terms[i]);
  }
  uf->ctx->register_term(uf->ctx, entry->lhs_app);
  uf->ctx->register_term(uf->ctx, entry->rhs_app);
}

uf_fun_diseq_t* uf_plugin_ensure_diff_witnesses(uf_plugin_t* uf, term_t lhs, term_t rhs,
                                                uf_fun_diseq_source_t source, term_t guard) {
  term_table_t* terms = uf->ctx->terms;
  type_table_t* types = uf->ctx->types;
  type_t tau;
  uint32_t i, arity;
  uf_fun_diseq_t* entry;

  if (lhs == rhs) {
    return NULL;
  }

  uf_plugin_order_fun_pair(&lhs, &rhs);
  entry = uf_plugin_find_fun_diseq_entry(uf, lhs, rhs);
  if (entry != NULL) {
    return entry;
  }

  tau = term_type(terms, lhs);
  assert(tau == term_type(terms, rhs));
  assert(uf_plugin_is_first_order_function_type(types, tau));

  arity = function_type_arity(types, tau);
  entry = safe_malloc(sizeof(uf_fun_diseq_t));
  entry->lhs = lhs;
  entry->rhs = rhs;
  entry->type = tau;
  entry->arity = arity;
  entry->source = source;
  entry->guard = guard;
  entry->diff_terms = safe_malloc(arity * sizeof(term_t));
  entry->lemma_emitted = false;

  for (i = 0; i < arity; ++ i) {
    type_t sigma = function_type_domain(types, tau, i);
    char name[64];

    entry->diff_terms[i] = new_uninterpreted_term(terms, sigma);
    snprintf(name, sizeof(name), "mcsat_diff_%"PRIu32"_%"PRIu32, uf->fun_diseq_entries.size, i);
    set_term_name(terms, entry->diff_terms[i], clone_string(name));
  }

  entry->lhs_app = app_term(terms, lhs, arity, entry->diff_terms);
  entry->rhs_app = app_term(terms, rhs, arity, entry->diff_terms);

  uf_plugin_register_diff_witness_terms(uf, entry);
  (*uf->stats.fun_diseq_witnesses) += arity;
  switch (source) {
  case UF_FUN_DISEQ_EXPLICIT:
    (*uf->stats.fun_diseq_explicit) ++;
    break;
  case UF_FUN_DISEQ_DISTINCT_ID:
    (*uf->stats.fun_diseq_distinct_id) ++;
    break;
  default:
    assert(false);
  }

  pvector_push(&uf->fun_diseq_entries, entry);
  return entry;
}

static bool uf_plugin_term_has_function_id(const uf_plugin_t* uf, term_t t, int32_t* id) {
  term_table_t* terms = uf->ctx->terms;
  variable_db_t* var_db = uf->ctx->var_db;
  const mcsat_trail_t* trail = uf->ctx->trail;
  variable_t v;
  const mcsat_value_t* value;

  if (t == NULL_TERM || !uf_plugin_is_first_order_function_type(uf->ctx->types, term_type(terms, t))) {
    return false;
  }

  v = variable_db_get_variable_if_exists(var_db, t);
  if (v == variable_null || !trail_has_value(trail, v)) {
    return false;
  }

  value = trail_get_value(trail, v);
  if (value->type != VALUE_RATIONAL) {
    return false;
  }

  return q_get32((rational_t*) &value->q, id);
}

static bool uf_plugin_add_explicit_fun_diseq_witnesses(uf_plugin_t* uf) {
  term_table_t* terms = uf->ctx->terms;
  variable_db_t* var_db = uf->ctx->var_db;
  const mcsat_trail_t* trail = uf->ctx->trail;
  bool added = false;
  uint32_t i, n;

  n = trail_size(trail);
  for (i = 0; i < n; ++ i) {
    variable_t v = trail_at(trail, i);
    term_t t = variable_db_get_term(var_db, v);
    const mcsat_value_t* value;
    composite_term_t* eq;
    term_t lhs, rhs;
    type_t tau;

    if (term_kind(terms, t) != EQ_TERM) {
      continue;
    }

    value = trail_get_value(trail, v);
    if (value->type != VALUE_BOOLEAN || value->b) {
      continue;
    }

    eq = eq_term_desc(terms, t);
    lhs = eq->arg[0];
    rhs = eq->arg[1];
    tau = term_type(terms, lhs);
    if (tau != term_type(terms, rhs) ||
        !uf_plugin_is_first_order_function_type(uf->ctx->types, tau)) {
      continue;
    }

    if (uf_plugin_find_fun_diseq_entry(uf, lhs, rhs) == NULL &&
        uf_plugin_ensure_diff_witnesses(uf, lhs, rhs, UF_FUN_DISEQ_EXPLICIT, t) != NULL) {
      added = true;
    }
  }

  return added;
}

static bool uf_plugin_add_distinct_id_fun_diseq_witnesses(uf_plugin_t* uf) {
  bool added = false;
  uint32_t i, j, n;

  n = uf->active_fun_terms.size;
  for (i = 0; i < n; ++ i) {
    term_t lhs = uf->active_fun_terms.data[i];
    type_t lhs_type = uf->active_fun_types.data[i];
    int32_t lhs_id = uf->active_fun_ids.data[i];

    for (j = i + 1; j < n; ++ j) {
      term_t rhs = uf->active_fun_terms.data[j];

      if (lhs_type != (type_t) uf->active_fun_types.data[j] ||
          lhs_id == uf->active_fun_ids.data[j]) {
        continue;
      }

      if (uf_plugin_find_fun_diseq_entry(uf, lhs, rhs) == NULL &&
          uf->fun_diseq_entries.size < UF_FUN_DISEQ_WITNESS_CAP &&
          uf_plugin_ensure_diff_witnesses(uf, lhs, rhs, UF_FUN_DISEQ_DISTINCT_ID, NULL_TERM) != NULL) {
        added = true;
      }
    }
  }

  return added;
}

static bool uf_plugin_can_create_distinct_id_witnesses(uf_plugin_t* uf, term_t t) {
  term_table_t* terms = uf->ctx->terms;
  type_t tau = term_type(terms, t);
  uint32_t i, needed;

  needed = 0;
  for (i = 0; i < uf->active_fun_terms.size; ++ i) {
    if (tau == (type_t) uf->active_fun_types.data[i] &&
        uf->active_fun_terms.data[i] != t &&
        uf_plugin_find_fun_diseq_entry(uf, t, uf->active_fun_terms.data[i]) == NULL) {
      ++ needed;
    }
  }

  return needed <= UF_FUN_DISEQ_WITNESS_CAP - uf->fun_diseq_entries.size;
}

static bool uf_plugin_has_incompatible_fun_id_merge(uf_plugin_t* uf) {
  uint32_t i, j, n;

  n = uf->active_fun_terms.size;
  for (i = 0; i < n; ++ i) {
    term_t lhs = uf->active_fun_terms.data[i];
    type_t lhs_type = uf->active_fun_types.data[i];
    int32_t lhs_id = uf->active_fun_ids.data[i];

    if (!eq_graph_has_term(&uf->eq_graph, lhs)) {
      continue;
    }

    for (j = i + 1; j < n; ++ j) {
      term_t rhs = uf->active_fun_terms.data[j];

      if (lhs_type == (type_t) uf->active_fun_types.data[j] &&
          lhs_id != uf->active_fun_ids.data[j] &&
          eq_graph_has_term(&uf->eq_graph, rhs) &&
          eq_graph_are_equal(&uf->eq_graph, lhs, rhs)) {
        (*uf->stats.fun_diseq_incompatible_id_merges) ++;
        if (!uf->eq_graph.in_conflict &&
            eq_graph_has_propagated_term_value(&uf->eq_graph, lhs) &&
            eq_graph_has_propagated_term_value(&uf->eq_graph, rhs)) {
          uf->eq_graph.in_conflict = true;
          uf->eq_graph.conflict_lhs = eq_graph_get_propagated_term_value_id(&uf->eq_graph, lhs);
          uf->eq_graph.conflict_rhs = eq_graph_get_propagated_term_value_id(&uf->eq_graph, rhs);
        }
        return true;
      }
    }
  }

  return false;
}

static bool uf_plugin_bool_term_is_false(uf_plugin_t* uf, term_t t) {
  variable_t v;

  v = variable_db_get_variable_if_exists(uf->ctx->var_db, t);
  return v != variable_null &&
    trail_has_value(uf->ctx->trail, v) &&
    trail_get_value(uf->ctx->trail, v)->type == VALUE_BOOLEAN &&
    !trail_get_value(uf->ctx->trail, v)->b;
}

static bool uf_plugin_bool_term_is_true(uf_plugin_t* uf, term_t t) {
  variable_t v;

  v = variable_db_get_variable_if_exists(uf->ctx->var_db, t);
  return v != variable_null &&
    trail_has_value(uf->ctx->trail, v) &&
    trail_get_value(uf->ctx->trail, v)->type == VALUE_BOOLEAN &&
    trail_get_value(uf->ctx->trail, v)->b;
}

static bool uf_plugin_fun_diseq_entry_is_active(uf_plugin_t* uf, const uf_fun_diseq_t* entry) {
  int32_t lhs_id, rhs_id;

  switch (entry->source) {
  case UF_FUN_DISEQ_EXPLICIT:
    return entry->guard != NULL_TERM && uf_plugin_bool_term_is_false(uf, entry->guard);
  case UF_FUN_DISEQ_DISTINCT_ID:
    return uf_plugin_term_has_function_id(uf, entry->lhs, &lhs_id) &&
      uf_plugin_term_has_function_id(uf, entry->rhs, &rhs_id) &&
      lhs_id != rhs_id;
  default:
    assert(false);
    return false;
  }
}

static term_t uf_plugin_fun_diseq_literal(uf_plugin_t* uf, const uf_fun_diseq_t* entry) {
  term_t diseq;

  if (entry->source == UF_FUN_DISEQ_EXPLICIT && entry->guard != NULL_TERM) {
    return opposite_term(entry->guard);
  }

  diseq = _o_yices_neq(entry->lhs, entry->rhs);
  uf->ctx->register_term(uf->ctx, unsigned_term(diseq));
  return diseq;
}

static bool ivector_contains_term(const ivector_t* v, term_t t) {
  uint32_t i;

  for (i = 0; i < v->size; ++ i) {
    if (v->data[i] == t) {
      return true;
    }
  }

  return false;
}

static void ivector_push_unique_term(ivector_t* v, term_t t) {
  if (!ivector_contains_term(v, t)) {
    ivector_push(v, t);
  }
}

static bool uf_plugin_active_fun_diseq_entry(uf_plugin_t* uf, term_t lhs, term_t rhs,
                                             uf_fun_diseq_t** entry_out) {
  uf_fun_diseq_t* entry;

  entry = uf_plugin_find_fun_diseq_entry(uf, lhs, rhs);
  if (entry != NULL && uf_plugin_fun_diseq_entry_is_active(uf, entry)) {
    *entry_out = entry;
    return true;
  }

  return false;
}

static bool uf_plugin_check_fun_cardinality_conflict(uf_plugin_t* uf) {
  type_table_t* types = uf->ctx->types;
  ivector_t seen_types;
  ivector_t terms;
  uint32_t i, j, k;
  bool conflict_found = false;

  init_ivector(&seen_types, 0);
  init_ivector(&terms, 0);

  for (i = 0; i < uf->fun_diseq_entries.size && !conflict_found; ++ i) {
    uf_fun_diseq_t* entry = uf->fun_diseq_entries.data[i];
    type_t tau = entry->type;
    uint32_t card;
    bool clique;

    if (!uf_plugin_fun_diseq_entry_is_active(uf, entry) ||
        ivector_contains_term(&seen_types, tau)) {
      continue;
    }
    ivector_push(&seen_types, tau);

    if (!is_finite_type(types, tau) || !type_card_is_exact(types, tau)) {
      continue;
    }

    card = type_card(types, tau);
    if (card >= UF_FUN_CARDINALITY_CLIQUE_TERM_CAP) {
      continue;
    }

    ivector_reset(&terms);
    for (j = i; j < uf->fun_diseq_entries.size; ++ j) {
      uf_fun_diseq_t* same_type_entry = uf->fun_diseq_entries.data[j];
      if (same_type_entry->type == tau &&
          uf_plugin_fun_diseq_entry_is_active(uf, same_type_entry)) {
        ivector_push_unique_term(&terms, same_type_entry->lhs);
        ivector_push_unique_term(&terms, same_type_entry->rhs);
        if (terms.size > UF_FUN_CARDINALITY_CLIQUE_TERM_CAP) {
          break;
        }
      }
    }

    if (terms.size <= card || terms.size > UF_FUN_CARDINALITY_CLIQUE_TERM_CAP) {
      continue;
    }

    clique = true;
    ivector_reset(&uf->conflict);
    for (j = 0; j < terms.size && clique; ++ j) {
      for (k = j + 1; k < terms.size; ++ k) {
        uf_fun_diseq_t* pair_entry;
        if (!uf_plugin_active_fun_diseq_entry(uf, terms.data[j], terms.data[k], &pair_entry)) {
          clique = false;
          break;
        }
        ivector_push(&uf->conflict, uf_plugin_fun_diseq_literal(uf, pair_entry));
      }
    }

    if (clique) {
      ivector_remove_duplicates(&uf->conflict);
      conflict_found = uf->conflict.size > 0;
    } else {
      ivector_reset(&uf->conflict);
    }
  }

  if (!conflict_found) {
    ivector_reset(&uf->conflict);
  }
  delete_ivector(&terms);
  delete_ivector(&seen_types);
  return conflict_found;
}

static bool uf_plugin_terms_are_equal_in_branch(uf_plugin_t* uf, term_t lhs, term_t rhs) {
  term_t eq;
  type_t lhs_type;

  if (lhs == rhs) {
    return true;
  }

  lhs_type = term_type(uf->ctx->terms, lhs);
  if (lhs_type == term_type(uf->ctx->terms, rhs) &&
      is_unit_type(uf->ctx->types, lhs_type)) {
    return true;
  }

  if (eq_graph_has_term(&uf->eq_graph, lhs) &&
      eq_graph_has_term(&uf->eq_graph, rhs) &&
      eq_graph_are_equal(&uf->eq_graph, lhs, rhs)) {
    return true;
  }

  eq = _o_yices_eq(lhs, rhs);
  return uf_plugin_bool_term_is_true(uf, eq);
}

static void uf_plugin_emit_fun_diseq_witness_lemmas(uf_plugin_t* uf, trail_token_t* prop) {
  uint32_t i;

  for (i = 0; i < uf->fun_diseq_entries.size; ++ i) {
    uf_fun_diseq_t* entry = uf->fun_diseq_entries.data[i];
    term_t lemma[2];

    if (entry->lemma_emitted || !uf_plugin_fun_diseq_entry_is_active(uf, entry)) {
      continue;
    }

    if (entry->source == UF_FUN_DISEQ_EXPLICIT && entry->guard != NULL_TERM) {
      lemma[0] = entry->guard;
    } else {
      lemma[0] = _o_yices_eq(entry->lhs, entry->rhs);
      uf->ctx->register_term(uf->ctx, lemma[0]);
    }
    lemma[1] = _o_yices_neq(entry->lhs_app, entry->rhs_app);
    if (lemma[1] != true_term) {
      uf->ctx->register_term(uf->ctx, unsigned_term(lemma[1]));
    }

    prop->lemma(prop, _o_yices_or(2, lemma));
    entry->lemma_emitted = true;
  }
}

static bool uf_plugin_check_fun_extensionality_conflict(uf_plugin_t* uf) {
  uint32_t i;

  for (i = 0; i < uf->fun_diseq_entries.size; ++ i) {
    uf_fun_diseq_t* entry = uf->fun_diseq_entries.data[i];
    term_t diseq, witness_eq;

    if (!uf_plugin_fun_diseq_entry_is_active(uf, entry) ||
        !uf_plugin_terms_are_equal_in_branch(uf, entry->lhs_app, entry->rhs_app)) {
      continue;
    }

    diseq = uf_plugin_fun_diseq_literal(uf, entry);
    witness_eq = _o_yices_eq(entry->lhs_app, entry->rhs_app);
    if (witness_eq != true_term) {
      uf->ctx->register_term(uf->ctx, witness_eq);
    }

    ivector_reset(&uf->conflict);
    ivector_push(&uf->conflict, diseq);
    if (witness_eq != true_term) {
      ivector_push(&uf->conflict, witness_eq);
    }
    ivector_remove_duplicates(&uf->conflict);
    return true;
  }

  return false;
}

static void uf_plugin_rebuild_active_fun_ids(uf_plugin_t* uf) {
  variable_db_t* var_db = uf->ctx->var_db;
  uint32_t i, n;

  ivector_reset(&uf->active_fun_terms);
  ivector_reset(&uf->active_fun_types);
  ivector_reset(&uf->active_fun_ids);

  n = variable_db_size(var_db);
  for (i = 1; i < n; ++ i) {
    term_t t = var_db->variable_to_term_map.data[i];
    int32_t id;

    if (uf_plugin_term_has_function_id(uf, t, &id)) {
      ivector_push(&uf->active_fun_terms, t);
      ivector_push(&uf->active_fun_types, term_type(uf->ctx->terms, t));
      ivector_push(&uf->active_fun_ids, id);
    }
  }
}


static
void uf_plugin_stats_init(uf_plugin_t* uf) {
  // Add statistics
  uf->stats.propagations = statistics_new_int(uf->ctx->stats, "mcsat::uf::propagations");
  uf->stats.conflicts = statistics_new_int(uf->ctx->stats, "mcsat::uf::conflicts");
  uf->stats.egraph_terms = statistics_new_int(uf->ctx->stats, "mcsat::uf::egraph_terms");
  uf->stats.fun_diseq_explicit = statistics_new_int(uf->ctx->stats, "mcsat::uf::fun_diseq_explicit");
  uf->stats.fun_diseq_distinct_id = statistics_new_int(uf->ctx->stats, "mcsat::uf::fun_diseq_distinct_id");
  uf->stats.fun_diseq_incompatible_id_merges = statistics_new_int(uf->ctx->stats, "mcsat::uf::fun_diseq_incompatible_id_merges");
  uf->stats.fun_diseq_witnesses = statistics_new_int(uf->ctx->stats, "mcsat::uf::fun_diseq_witnesses");
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
  init_pvector(&uf->fun_diseq_entries, 0);
  init_ivector(&uf->active_fun_terms, 0);
  init_ivector(&uf->active_fun_types, 0);
  init_ivector(&uf->active_fun_ids, 0);
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
  uf_plugin_free_fun_diseq_entries_from(uf, 0);
  delete_pvector(&uf->fun_diseq_entries);
  delete_ivector(&uf->active_fun_terms);
  delete_ivector(&uf->active_fun_types);
  delete_ivector(&uf->active_fun_ids);
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
    uf->ctx->register_term(uf->ctx, r1);
    weq_graph_add_select_term(&uf->weq_graph, r1);
    // if the element domain is finite then we add this extra read term
    type_t element_type = term_type(terms, t_desc->arg[2]);
    if (is_finite_type(terms->types, element_type) || is_boolean_type(element_type) || is_bv_type(terms->types, element_type)){
      term_t r2 = app_term(terms, t_desc->arg[0], t_desc->arity - 2, t_desc->arg + 1);
      uf->ctx->register_term(uf->ctx, r2);
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

  bool added_fun_diseq_witnesses = uf_plugin_add_explicit_fun_diseq_witnesses(uf);

  // If we're not watching anything and no witness was added, we just ignore.
  if (eq_graph_term_size(&uf->eq_graph) == 0 && !added_fun_diseq_witnesses) {
    return;
  }

  // Propagate known terms
  eq_graph_propagate_trail(&uf->eq_graph);
  uf_plugin_rebuild_active_fun_ids(uf);
  uf_plugin_process_eq_graph_propagations(uf, prop);
  uf_plugin_rebuild_active_fun_ids(uf);
  added_fun_diseq_witnesses = uf_plugin_add_distinct_id_fun_diseq_witnesses(uf) || added_fun_diseq_witnesses;
  if (added_fun_diseq_witnesses) {
    eq_graph_propagate_trail(&uf->eq_graph);
    uf_plugin_process_eq_graph_propagations(uf, prop);
    uf_plugin_rebuild_active_fun_ids(uf);
  }
  uf_plugin_emit_fun_diseq_witness_lemmas(uf, prop);
  if (uf_plugin_has_incompatible_fun_id_merge(uf)) {
    assert(uf->eq_graph.in_conflict);
  }

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

  if (uf_plugin_check_fun_cardinality_conflict(uf)) {
    prop->conflict(prop);
    (*uf->stats.conflicts) ++;
    statistic_avg_add(uf->stats.avg_conflict_size, uf->conflict.size);
    return;
  }

  if (uf_plugin_check_fun_extensionality_conflict(uf)) {
    prop->conflict(prop);
    (*uf->stats.conflicts) ++;
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
                    &uf->fun_diseq_entries.size,
                    NULL);

  weq_graph_push(&uf->weq_graph);
  eq_graph_push(&uf->eq_graph);
}

static
void uf_plugin_pop(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  uint32_t old_eq_graph_addition_trail_size, old_fun_diseq_entries_size;

  // Pop the int variable values
  scope_holder_pop(&uf->scope,
                   &old_eq_graph_addition_trail_size,
                   &old_fun_diseq_entries_size,
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
  uf_plugin_free_fun_diseq_entries_from(uf, old_fun_diseq_entries_size);
  uf_plugin_rebuild_active_fun_ids(uf);
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

  // Cached values to try, in priority order (only hints; each is checked against
  // the forbidden set via eq_graph_get_forbidden).
  const mcsat_value_t* x_candidates[2] = { NULL, NULL };
  uint32_t x_num_candidates = trail_get_cached_candidates(uf->ctx->trail, x, x_candidates);

  // Pick a value not in the forbidden set
  term_t x_term = variable_db_get_term(uf->ctx->var_db, x);
  pvector_t forbidden;
  init_pvector(&forbidden, 0);
  // Build the forbidden list while testing the first candidate (the list does not
  // depend on the candidate, so pass NULL when there is none); then test any
  // remaining candidates against the already-built list (values == NULL).
  const mcsat_value_t* x_cached_value = NULL;
  bool cache_ok = eq_graph_get_forbidden(&uf->eq_graph, x_term, &forbidden,
                                         x_num_candidates > 0 ? x_candidates[0] : NULL);
  if (cache_ok) {
    x_cached_value = x_candidates[0];
  } else {
    for (uint32_t i = 1; i < x_num_candidates; ++i) {
      if (eq_graph_get_forbidden(&uf->eq_graph, x_term, NULL, x_candidates[i])) {
        x_cached_value = x_candidates[i];
        cache_ok = true;
        break;
      }
    }
  }
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
      bool use_fresh_function_value = uf_plugin_can_create_distinct_id_witnesses(uf, x_term);
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

      while (use_fresh_function_value && int_hset_member(&uf->fun_used_values, picked_value)) {
        picked_value += 1;
      }
      // save the used value
      if (use_fresh_function_value) {
        int_hset_add(&uf->fun_used_values, picked_value);
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
    delete_ivector(&arguments);
    return null_value;
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
bool uf_plugin_term_has_trail_value(uf_plugin_t* uf, term_t t) {
  variable_t var;

  var = variable_db_get_variable_if_exists(uf->ctx->var_db, t);
  return var != variable_null && trail_has_value(uf->ctx->trail, var);
}

static
void uf_model_builder_map_term_if_missing(uf_model_builder_t* builder, model_t* model, term_t t) {
  value_t value;

  if (model_find_term_value(model, t) != null_value) {
    return;
  }

  if (term_type_kind(builder->uf->ctx->terms, t) != FUNCTION_TYPE &&
      !uf_plugin_term_has_trail_value(builder->uf, t)) {
    return;
  }

  value = uf_model_builder_get_term_value(builder, t);
  if (value != null_value) {
    model_map_term(model, t, value);
  }
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
void uf_model_builder_map_diff_witnesses(uf_model_builder_t* builder, model_t* model) {
  uf_plugin_t* uf = builder->uf;
  uint32_t i, j;

  for (i = 0; i < uf->fun_diseq_entries.size; ++ i) {
    uf_fun_diseq_t* entry = uf->fun_diseq_entries.data[i];

    if (!uf_plugin_fun_diseq_entry_is_active(uf, entry)) {
      continue;
    }

    for (j = 0; j < entry->arity; ++ j) {
      uf_model_builder_map_term_if_missing(builder, model, entry->diff_terms[j]);
    }
    uf_model_builder_map_term_if_missing(builder, model, entry->lhs_app);
    uf_model_builder_map_term_if_missing(builder, model, entry->rhs_app);
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

  uf_model_builder_map_diff_witnesses(&builder, model);

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
