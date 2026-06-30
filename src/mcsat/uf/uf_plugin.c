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
#include "mcsat/utils/branch_utils.h"
#include "mcsat/watch_list_manager.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/value.h"

#include "mcsat/eq/equality_graph.h"
#include "mcsat/weq/weak_eq_graph.h"

#include "utils/int_array_sort2.h"
#include "utils/int_hash_map.h"
#include "utils/int_hash_map2.h"
#include "utils/pair_hash_map.h"
#include "utils/ptr_array_sort2.h"
#include "utils/int_hash_sets.h"
#include "utils/ptr_vectors.h"
#include "utils/refcount_strings.h"

#include "model/fresh_value_maker.h"
#include "model/models.h"
#include "model/term_to_val.h"

#include "terms/terms.h"
#include "terms/term_utils.h"
#include "inttypes.h"
#include <string.h>


#define DECIDE_FUNCTION_VALUE_START UINT32_MAX/64
#define UF_FUN_DISEQ_WITNESS_CAP 16
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
  term_t* diff_terms;
  term_t lhs_app;
  term_t rhs_app;
  term_t app_eq;
} uf_diff_witness_t;

typedef struct {
  term_t lhs;
  term_t rhs;
  type_t type;
  uint32_t arity;
  uf_fun_diseq_source_t source;
  term_t guard;
  uf_diff_witness_t* witness;
  term_t* diff_terms;
  term_t lhs_app;
  term_t rhs_app;
} uf_fun_diseq_t;

typedef struct {
  term_t lhs;
  term_t rhs;
  type_t type;
  uf_fun_diseq_source_t source;
  term_t guard;
} uf_fun_model_diseq_t;

typedef enum {
  UF_FUN_DISEQ_NO_CHANGE,
  UF_FUN_DISEQ_ADDED_WITNESS,
  UF_FUN_DISEQ_CONFLICT,
  UF_FUN_DISEQ_CAP_REACHED,
} uf_fun_diseq_result_t;


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

  /** Permanent normalized function-type key for each allocated function id */
  int_hmap_t fun_value_type_keys;

  /** Scoped committed function disequalities */
  pvector_t fun_diseq_entries;

  /** Scoped non-risky function disequalities for model completion */
  pvector_t fun_model_diseq_entries;

  /** Internal diff witness terms */
  int_hset_t diff_witness_terms;

  /** Persistent diff witness terms, keyed by ordered function-term pair */
  pmap_t diff_witness_cache;
  pvector_t diff_witness_cache_entries;

  /** Equality atoms whose disequality literal was generated as a witness lemma. */
  int_hset_t generated_witness_eqs;

  /** Trail prefix already scanned for explicit function disequalities */
  uint32_t fun_diseq_trail_scan_index;

  /** Active function-id view rebuilt from the current trail */
  ivector_t active_fun_terms;
  ivector_t active_fun_types;
  ivector_t active_fun_type_keys;
  ivector_t active_fun_ids;
  uint32_t active_fun_trail_size;
  uint32_t active_fun_generation;
  bool active_fun_ids_valid;

  /** Cached risky-function-type check, keyed by type id */
  int_hmap_t risky_function_type_cache;

  /** Sensitivity generation used for scan cursors and active id views */
  uint32_t equality_sensitivity_generation;

  /** Tmp vector */
  int_mset_t tmp;

  struct {
    statistic_int_t* egraph_terms;
    statistic_int_t* fun_diseq_explicit;
    statistic_int_t* fun_diseq_distinct_id;
    statistic_int_t* fun_diseq_model;
    statistic_int_t* fun_diseq_incompatible_id_merges;
    statistic_int_t* fun_diseq_witnesses;
    statistic_int_t* fun_diseq_cardinality_conflicts;
    statistic_int_t* propagations;
    statistic_int_t* conflicts;
    statistic_avg_t* avg_conflict_size;
    statistic_avg_t* avg_explanation_size;
  } stats;

  /** Exception handler */
  jmp_buf* exception;

} uf_plugin_t;

static void uf_plugin_bump_terms_and_reset(uf_plugin_t* uf, int_mset_t* to_bump);
static void uf_plugin_rebuild_active_fun_ids(uf_plugin_t* uf);
static term_t uf_plugin_distinct_id_diseq_literal(uf_plugin_t* uf, term_t lhs, term_t rhs);
static bool ivector_contains_term(const ivector_t* v, term_t t);
static void ivector_push_unique_term(ivector_t* v, term_t t);
static bool uf_plugin_term_has_direct_trail_assignment(uf_plugin_t* uf, term_t t, variable_t v);
static bool uf_plugin_pick_active_function_id(uf_plugin_t* uf, term_t t, type_t tau, const pvector_t* forbidden,
                                              int32_t* picked_id);
static bool uf_plugin_fun_pair_super_type(uf_plugin_t* uf, term_t lhs, term_t rhs, type_t* tau);

static void uf_plugin_free_fun_diseq_entries_from(uf_plugin_t* uf, uint32_t old_size) {
  while (uf->fun_diseq_entries.size > old_size) {
    uf_fun_diseq_t* entry = pvector_pop2(&uf->fun_diseq_entries);
    safe_free(entry);
  }
}

static void uf_plugin_free_diff_witness_cache(uf_plugin_t* uf) {
  while (uf->diff_witness_cache_entries.size > 0) {
    uf_diff_witness_t* witness = pvector_pop2(&uf->diff_witness_cache_entries);
    safe_free(witness->diff_terms);
    safe_free(witness);
  }
}

static void uf_plugin_free_fun_model_diseq_entries_from(uf_plugin_t* uf, uint32_t old_size) {
  while (uf->fun_model_diseq_entries.size > old_size) {
    safe_free(pvector_pop2(&uf->fun_model_diseq_entries));
  }
}

static void uf_plugin_invalidate_active_fun_ids(uf_plugin_t* uf) {
  uf->active_fun_ids_valid = false;
}

static type_t uf_function_type_key(uf_plugin_t* uf, type_t tau) {
  assert(type_kind(uf->ctx->types, tau) == FUNCTION_TYPE);
  return max_super_type(uf->ctx->types, tau);
}

static bool uf_function_types_have_supertype(uf_plugin_t* uf, type_t lhs_type, type_t rhs_type,
                                             type_t* super) {
  type_t tau;

  if (type_kind(uf->ctx->types, lhs_type) != FUNCTION_TYPE ||
      type_kind(uf->ctx->types, rhs_type) != FUNCTION_TYPE) {
    return false;
  }

  tau = super_type(uf->ctx->types, lhs_type, rhs_type);
  if (tau == NULL_TYPE || type_kind(uf->ctx->types, tau) != FUNCTION_TYPE) {
    return false;
  }

  *super = tau;
  return true;
}

static void uf_plugin_assert_equality_sensitivity_frozen(uf_plugin_t* uf) {
  assert(mcsat_branch_equality_sensitivity_is_frozen(uf->ctx));
}

static void uf_plugin_refresh_equality_sensitivity_generation(uf_plugin_t* uf) {
  uint32_t generation;

  if (uf->ctx->equality_sensitivity_generation == NULL) {
    return;
  }

  generation = uf->ctx->equality_sensitivity_generation(uf->ctx);
  if (uf->equality_sensitivity_generation != generation) {
    uf->equality_sensitivity_generation = generation;
    uf->fun_diseq_trail_scan_index = 0;
    ivector_reset(&uf->active_fun_terms);
    ivector_reset(&uf->active_fun_types);
    ivector_reset(&uf->active_fun_type_keys);
    ivector_reset(&uf->active_fun_ids);
    uf->active_fun_ids_valid = false;
  }
}

#ifndef NDEBUG
static void uf_plugin_assert_generated_equality_sensitive(uf_plugin_t* uf, const char* origin,
                                                          term_t lhs, term_t rhs) {
  type_t tau, lhs_type, rhs_type;

  (void) origin;
  if (!mcsat_branch_equality_sensitivity_is_frozen(uf->ctx)) {
    return;
  }
  lhs_type = term_type(uf->ctx->terms, lhs);
  rhs_type = term_type(uf->ctx->terms, rhs);
  tau = super_type(uf->ctx->types, lhs_type, rhs_type);
  assert(tau != NULL_TYPE &&
         "UF generated equality on incompatible types");
  assert(mcsat_branch_type_is_equality_sensitive(uf->ctx, tau) &&
         "UF generated equality on non-sensitive type");
}
#endif

static bool uf_type_has_unit_cardinality(type_table_t* types, type_t tau) {
  return is_unit_type(types, tau) ||
    (type_card_is_exact(types, tau) && type_card(types, tau) == 1);
}

static bool uf_type_is_risky_uncached(type_table_t* types, type_t tau) {
  return type_kind(types, tau) == FUNCTION_TYPE &&
    (type_has_finite_domain(types, tau) ||
     uf_type_has_unit_cardinality(types, function_type_range(types, tau)));
}

static bool uf_type_is_risky(uf_plugin_t* uf, type_t tau) {
  int_hmap_pair_t* cached;
  bool risky;

  cached = int_hmap_find(&uf->risky_function_type_cache, tau);
  if (cached != NULL) {
    return cached->val != 0;
  }

  risky = uf_type_is_risky_uncached(uf->ctx->types, tau);
  cached = int_hmap_get(&uf->risky_function_type_cache, tau);
  cached->val = risky;
  return risky;
}

static bool uf_function_type_exact_cardinality(type_table_t* types, type_t tau, uint32_t* card) {
  assert(type_kind(types, tau) == FUNCTION_TYPE);

  if (!type_has_finite_domain(types, tau) ||
      !type_has_finite_range(types, tau) ||
      !type_card_is_exact(types, tau)) {
    return false;
  }

  *card = type_card(types, tau);
  return true;
}

static bool uf_type_needs_search_diff(uf_plugin_t* uf, type_t tau) {
  uf_plugin_assert_equality_sensitivity_frozen(uf);

  return type_kind(uf->ctx->types, tau) == FUNCTION_TYPE &&
    mcsat_branch_type_is_equality_sensitive(uf->ctx, tau) &&
    uf_type_is_risky(uf, tau);
}

static bool uf_type_needs_model_diseq_record(uf_plugin_t* uf, type_t tau) {
  uf_plugin_assert_equality_sensitivity_frozen(uf);

  return type_kind(uf->ctx->types, tau) == FUNCTION_TYPE &&
    mcsat_branch_type_is_equality_sensitive(uf->ctx, tau) &&
    !uf_type_is_risky(uf, tau);
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

static uf_fun_model_diseq_t* uf_plugin_find_fun_model_diseq_entry(uf_plugin_t* uf, term_t lhs, term_t rhs) {
  uint32_t i;

  uf_plugin_order_fun_pair(&lhs, &rhs);

  for (i = 0; i < uf->fun_model_diseq_entries.size; ++ i) {
    uf_fun_model_diseq_t* entry = uf->fun_model_diseq_entries.data[i];
    if (entry->lhs == lhs && entry->rhs == rhs) {
      return entry;
    }
  }

  return NULL;
}

static bool uf_plugin_fun_pair_super_type(uf_plugin_t* uf, term_t lhs, term_t rhs, type_t* tau) {
  return uf_function_types_have_supertype(uf, term_type(uf->ctx->terms, lhs),
                                          term_type(uf->ctx->terms, rhs), tau);
}

static uf_fun_model_diseq_t* uf_plugin_ensure_model_diseq_record(uf_plugin_t* uf, term_t lhs, term_t rhs,
                                                                  uf_fun_diseq_source_t source, term_t guard) {
  type_t tau;
  uf_fun_model_diseq_t* entry;

  if (lhs == rhs) {
    return NULL;
  }

  uf_plugin_order_fun_pair(&lhs, &rhs);
  entry = uf_plugin_find_fun_model_diseq_entry(uf, lhs, rhs);
  if (entry != NULL) {
    return entry;
  }

  if (!uf_plugin_fun_pair_super_type(uf, lhs, rhs, &tau) ||
      !uf_type_needs_model_diseq_record(uf, tau)) {
    return NULL;
  }

  entry = safe_malloc(sizeof(uf_fun_model_diseq_t));
  entry->lhs = lhs;
  entry->rhs = rhs;
  entry->type = tau;
  entry->source = source;
  entry->guard = guard;
  pvector_push(&uf->fun_model_diseq_entries, entry);
  (*uf->stats.fun_diseq_model) ++;

  return entry;
}

static bool uf_plugin_fun_pair_needs_search_diff(uf_plugin_t* uf, term_t lhs, term_t rhs) {
  type_t tau;

  return uf_plugin_fun_pair_super_type(uf, lhs, rhs, &tau) &&
    uf_type_needs_search_diff(uf, tau);
}

static void uf_plugin_register_diff_witness_terms(uf_plugin_t* uf, const uf_diff_witness_t* witness) {
  uint32_t i;

  assert(uf->ctx->register_term != NULL);

  uf->ctx->register_term(uf->ctx, witness->lhs);
  uf->ctx->register_term(uf->ctx, witness->rhs);
  for (i = 0; i < witness->arity; ++ i) {
    uf->ctx->register_term(uf->ctx, witness->diff_terms[i]);
  }
  uf->ctx->register_term(uf->ctx, witness->lhs_app);
  uf->ctx->register_term(uf->ctx, witness->rhs_app);
  if (witness->app_eq != true_term && witness->app_eq != false_term) {
    uf->ctx->register_term(uf->ctx, witness->app_eq);
  }
}

static uf_diff_witness_t* uf_plugin_ensure_diff_witness_cache(uf_plugin_t* uf, term_t lhs, term_t rhs) {
  term_table_t* terms = uf->ctx->terms;
  type_table_t* types = uf->ctx->types;
  type_t tau;
  uint32_t i, arity, index;
  pmap_rec_t* rec;
  uf_diff_witness_t* witness;

  assert(lhs != rhs);

  uf_plugin_order_fun_pair(&lhs, &rhs);
  rec = pmap_find(&uf->diff_witness_cache, lhs, rhs);
  if (rec != NULL) {
    return rec->val;
  }

  if (!uf_plugin_fun_pair_super_type(uf, lhs, rhs, &tau)) {
    return NULL;
  }
  assert(mcsat_branch_equality_sensitivity_is_frozen(uf->ctx));
  assert(mcsat_branch_type_is_equality_sensitive(uf->ctx, tau));
  assert(uf_plugin_fun_pair_needs_search_diff(uf, lhs, rhs));

  arity = function_type_arity(types, tau);
  index = uf->diff_witness_cache_entries.size;

  witness = safe_malloc(sizeof(uf_diff_witness_t));
  witness->lhs = lhs;
  witness->rhs = rhs;
  witness->type = tau;
  witness->arity = arity;
  witness->diff_terms = safe_malloc(arity * sizeof(term_t));

  for (i = 0; i < arity; ++ i) {
    type_t sigma = function_type_domain(types, tau, i);
    char name[64];

    assert(mcsat_branch_type_is_equality_sensitive(uf->ctx, sigma));
    witness->diff_terms[i] = new_uninterpreted_term(terms, sigma);
    snprintf(name, sizeof(name), "mcsat_diff_%"PRIu32"_%"PRIu32, index, i);
    set_term_name(terms, witness->diff_terms[i], clone_string(name));
    int_hset_add(&uf->diff_witness_terms, witness->diff_terms[i]);
  }

  witness->lhs_app = app_term(terms, lhs, arity, witness->diff_terms);
  witness->rhs_app = app_term(terms, rhs, arity, witness->diff_terms);
  witness->app_eq = _o_yices_eq(witness->lhs_app, witness->rhs_app);
  if (witness->app_eq != true_term && witness->app_eq != false_term) {
    int_hset_add(&uf->generated_witness_eqs, witness->app_eq);
  }
  uf_plugin_invalidate_active_fun_ids(uf);

  rec = pmap_get(&uf->diff_witness_cache, lhs, rhs);
  assert(rec->val == DEFAULT_PTR);
  rec->val = witness;
  pvector_push(&uf->diff_witness_cache_entries, witness);
  (*uf->stats.fun_diseq_witnesses) += arity;

  return witness;
}

uf_fun_diseq_t* uf_plugin_ensure_diff_witnesses(uf_plugin_t* uf, term_t lhs, term_t rhs,
                                                uf_fun_diseq_source_t source, term_t guard) {
  type_table_t* types = uf->ctx->types;
  type_t tau;
  uint32_t arity;
  uf_fun_diseq_t* entry;
  uf_diff_witness_t* witness;

  if (lhs == rhs) {
    return NULL;
  }

  uf_plugin_order_fun_pair(&lhs, &rhs);
  entry = uf_plugin_find_fun_diseq_entry(uf, lhs, rhs);
  if (entry != NULL) {
    return entry;
  }

  if (!uf_plugin_fun_pair_super_type(uf, lhs, rhs, &tau)) {
    return NULL;
  }
  assert(mcsat_branch_equality_sensitivity_is_frozen(uf->ctx));
  assert(mcsat_branch_type_is_equality_sensitive(uf->ctx, tau));
  assert(uf_plugin_fun_pair_needs_search_diff(uf, lhs, rhs));

  arity = function_type_arity(types, tau);
  witness = uf_plugin_ensure_diff_witness_cache(uf, lhs, rhs);

  entry = safe_malloc(sizeof(uf_fun_diseq_t));
  entry->lhs = lhs;
  entry->rhs = rhs;
  entry->type = tau;
  entry->arity = arity;
  entry->source = source;
  entry->guard = guard;
  entry->witness = witness;
  entry->diff_terms = witness->diff_terms;
  entry->lhs_app = witness->lhs_app;
  entry->rhs_app = witness->rhs_app;

  uf_plugin_register_diff_witness_terms(uf, witness);
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

  type_t range = function_type_range(types, tau);
  if (uf_type_needs_search_diff(uf, range) &&
      uf_plugin_find_fun_diseq_entry(uf, entry->lhs_app, entry->rhs_app) == NULL) {
    assert(mcsat_branch_type_is_equality_sensitive(uf->ctx, range));
#ifndef NDEBUG
    uf_plugin_assert_generated_equality_sensitive(uf, "recursive diff witness guard",
                                                  entry->lhs_app, entry->rhs_app);
#endif
    uf_plugin_ensure_diff_witnesses(uf, entry->lhs_app, entry->rhs_app,
                                    UF_FUN_DISEQ_EXPLICIT, witness->app_eq);
  }

  return entry;
}

static bool uf_plugin_term_has_function_id(const uf_plugin_t* uf, term_t t, int32_t* id) {
  term_table_t* terms = uf->ctx->terms;
  variable_db_t* var_db = uf->ctx->var_db;
  const mcsat_trail_t* trail = uf->ctx->trail;
  variable_t v;
  const mcsat_value_t* value;

  if (t == NULL_TERM || term_type_kind(terms, t) != FUNCTION_TYPE) {
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

static term_t uf_plugin_fun_diseq_literal_for_source(uf_plugin_t* uf, term_t lhs, term_t rhs,
                                                     uf_fun_diseq_source_t source, term_t guard) {
  switch (source) {
  case UF_FUN_DISEQ_EXPLICIT:
    assert(guard != NULL_TERM);
    return opposite_term(guard);
  case UF_FUN_DISEQ_DISTINCT_ID:
    return uf_plugin_distinct_id_diseq_literal(uf, lhs, rhs);
  default:
    assert(false);
    return NULL_TERM;
  }
}

static uf_fun_diseq_result_t uf_plugin_add_fun_diseq_pair(uf_plugin_t* uf, term_t lhs, term_t rhs,
                                                          uf_fun_diseq_source_t source, term_t guard) {
  type_table_t* types = uf->ctx->types;
  type_t tau;

  if (lhs == rhs) {
    return UF_FUN_DISEQ_NO_CHANGE;
  }

  if (!uf_plugin_fun_pair_super_type(uf, lhs, rhs, &tau) ||
      type_kind(types, tau) != FUNCTION_TYPE ||
      int_hset_member(&uf->diff_witness_terms, lhs) ||
      int_hset_member(&uf->diff_witness_terms, rhs)) {
    return UF_FUN_DISEQ_NO_CHANGE;
  }

  if (!mcsat_branch_type_is_equality_sensitive(uf->ctx, tau)) {
    return UF_FUN_DISEQ_NO_CHANGE;
  }
  assert(mcsat_branch_type_is_equality_sensitive(uf->ctx, tau));

  if (uf_type_has_unit_cardinality(types, function_type_range(types, tau))) {
    ivector_reset(&uf->conflict);
    ivector_push(&uf->conflict, uf_plugin_fun_diseq_literal_for_source(uf, lhs, rhs, source, guard));
    return UF_FUN_DISEQ_CONFLICT;
  }

  if (uf_plugin_fun_pair_needs_search_diff(uf, lhs, rhs)) {
    if (source == UF_FUN_DISEQ_EXPLICIT &&
        uf->fun_diseq_entries.size >= UF_FUN_DISEQ_WITNESS_CAP) {
      return UF_FUN_DISEQ_CAP_REACHED;
    }

    if (uf_plugin_find_fun_diseq_entry(uf, lhs, rhs) == NULL &&
        uf_plugin_ensure_diff_witnesses(uf, lhs, rhs, source, guard) != NULL) {
      return UF_FUN_DISEQ_ADDED_WITNESS;
    }
    return UF_FUN_DISEQ_NO_CHANGE;
  }

  /*
   * Explicit non-risky disequalities may relate terms whose assigned function
   * ids do not by themselves force extensional separation. Distinct-id
   * non-risky commitments are handled by assigning fresh function values for
   * distinct ids, so we do not enumerate all such pairs here.
   */
  if (source == UF_FUN_DISEQ_EXPLICIT &&
      uf_type_needs_model_diseq_record(uf, tau) &&
      uf_plugin_find_fun_model_diseq_entry(uf, lhs, rhs) == NULL) {
    uf_plugin_ensure_model_diseq_record(uf, lhs, rhs, source, guard);
  }

  return UF_FUN_DISEQ_NO_CHANGE;
}

static bool uf_plugin_add_explicit_fun_diseq_witnesses(uf_plugin_t* uf) {
  term_table_t* terms = uf->ctx->terms;
  variable_db_t* var_db = uf->ctx->var_db;
  const mcsat_trail_t* trail = uf->ctx->trail;
  bool added = false;
  uint32_t i, n, retry_index;

  if (!mcsat_branch_equality_sensitivity_is_frozen(uf->ctx)) {
    return false;
  }
  uf_plugin_refresh_equality_sensitivity_generation(uf);

  n = trail_size(trail);
  retry_index = n;
  if (uf->fun_diseq_trail_scan_index > n) {
    uf->fun_diseq_trail_scan_index = n;
  }

  for (i = uf->fun_diseq_trail_scan_index; i < n; ++ i) {
    variable_t v = trail_at(trail, i);
    term_t t = variable_db_get_term(var_db, v);
    const mcsat_value_t* value;
    term_kind_t kind;
    uf_fun_diseq_result_t result;

    if (t == NULL_TERM || int_hset_member(&uf->diff_witness_terms, t)) {
      continue;
    }

    kind = term_kind(terms, t);
    value = trail_get_value(trail, v);
    if (value->type != VALUE_BOOLEAN) {
      continue;
    }

    switch (kind) {
    case EQ_TERM:
      if (value->b || int_hset_member(&uf->generated_witness_eqs, t)) {
        continue;
      }
      {
        composite_term_t* eq = eq_term_desc(terms, t);
        result = uf_plugin_add_fun_diseq_pair(uf, eq->arg[0], eq->arg[1], UF_FUN_DISEQ_EXPLICIT, t);
      }
      if (result == UF_FUN_DISEQ_ADDED_WITNESS) {
        added = true;
      } else if (result == UF_FUN_DISEQ_CONFLICT) {
        uf->fun_diseq_trail_scan_index = retry_index;
        return added;
      } else if (result == UF_FUN_DISEQ_CAP_REACHED) {
        retry_index = retry_index < i ? retry_index : i;
      }
      break;

    case DISTINCT_TERM:
      if (!value->b) {
        continue;
      }
      {
        composite_term_t* distinct = distinct_term_desc(terms, t);
        term_t guard = opposite_term(t);
        uint32_t j, k;

        for (j = 0; j < distinct->arity; ++ j) {
          for (k = j + 1; k < distinct->arity; ++ k) {
            result = uf_plugin_add_fun_diseq_pair(uf, distinct->arg[j], distinct->arg[k],
                                                  UF_FUN_DISEQ_EXPLICIT, guard);
            if (result == UF_FUN_DISEQ_ADDED_WITNESS) {
              added = true;
            } else if (result == UF_FUN_DISEQ_CONFLICT) {
              uf->fun_diseq_trail_scan_index = retry_index;
              return added;
            } else if (result == UF_FUN_DISEQ_CAP_REACHED) {
              retry_index = retry_index < i ? retry_index : i;
            }
          }
        }
      }
      break;

    default:
      break;
    }
  }

  uf->fun_diseq_trail_scan_index = retry_index;
  return added;
}

static bool uf_plugin_add_distinct_id_fun_diseq_witnesses(uf_plugin_t* uf) {
  uint32_t i, j, n;
  bool added = false;

  if (!mcsat_branch_equality_sensitivity_is_frozen(uf->ctx)) {
    return false;
  }
  uf_plugin_refresh_equality_sensitivity_generation(uf);

  n = uf->active_fun_terms.size;
  for (i = 0; i < n; ++ i) {
    term_t lhs = uf->active_fun_terms.data[i];
    type_t lhs_type = uf->active_fun_types.data[i];
    type_t lhs_key = uf->active_fun_type_keys.data[i];
    int32_t lhs_id = uf->active_fun_ids.data[i];

    if (!uf_type_needs_search_diff(uf, lhs_key)) {
      continue;
    }

    if (int_hset_member(&uf->diff_witness_terms, lhs)) {
      continue;
    }

#ifndef NDEBUG
    variable_t lhs_var = variable_db_get_variable_if_exists(uf->ctx->var_db, lhs);
    assert(lhs_var != variable_null &&
           uf_plugin_term_has_direct_trail_assignment(uf, lhs, lhs_var));
#endif

    for (j = i + 1; j < n; ++ j) {
      term_t rhs = uf->active_fun_terms.data[j];
      type_t pair_type;
      uf_fun_diseq_result_t result;

      if (lhs_key != (type_t) uf->active_fun_type_keys.data[j] ||
          lhs_id == uf->active_fun_ids.data[j] ||
          int_hset_member(&uf->diff_witness_terms, rhs) ||
          !uf_function_types_have_supertype(uf, lhs_type, uf->active_fun_types.data[j], &pair_type) ||
          !uf_type_needs_search_diff(uf, pair_type)) {
        continue;
      }

#ifndef NDEBUG
      variable_t rhs_var = variable_db_get_variable_if_exists(uf->ctx->var_db, rhs);
      assert(rhs_var != variable_null &&
             uf_plugin_term_has_direct_trail_assignment(uf, rhs, rhs_var));
#endif

      result = uf_plugin_add_fun_diseq_pair(uf, lhs, rhs, UF_FUN_DISEQ_DISTINCT_ID, NULL_TERM);
      if (result == UF_FUN_DISEQ_ADDED_WITNESS) {
        added = true;
      } else if (result == UF_FUN_DISEQ_CONFLICT) {
        return added;
      }
    }
  }

  return added;
}

static bool uf_plugin_forbidden_contains_id(const pvector_t* forbidden, int32_t id) {
  uint32_t i;

  for (i = 0; i < forbidden->size; ++ i) {
    const mcsat_value_t* v = forbidden->data[i];
    int32_t v_id;

    if (v->type == VALUE_RATIONAL &&
        q_get32((rational_t*) &v->q, &v_id) &&
        v_id == id) {
      return true;
    }
  }

  return false;
}

static bool uf_plugin_function_id_key_is_allowed(uf_plugin_t* uf, int32_t id, type_t key) {
  int_hmap_pair_t* cached;

  cached = int_hmap_find(&uf->fun_value_type_keys, id);
  return cached == NULL || cached->val == key;
}

static void uf_plugin_record_function_id_key(uf_plugin_t* uf, int32_t id, type_t key) {
  int_hmap_pair_t* cached;

  cached = int_hmap_get(&uf->fun_value_type_keys, id);
  assert(cached->val < 0 || cached->val == key);
  cached->val = key;
}

static bool uf_plugin_fun_diseq_entry_is_active(uf_plugin_t* uf, const uf_fun_diseq_t* entry);
static bool uf_plugin_fun_model_diseq_entry_is_active(uf_plugin_t* uf, const uf_fun_model_diseq_t* entry);

static bool uf_plugin_active_diseq_blocks_function_id(uf_plugin_t* uf, term_t t, int32_t id) {
  uint32_t i;

  for (i = 0; i < uf->fun_diseq_entries.size; ++ i) {
    uf_fun_diseq_t* entry = uf->fun_diseq_entries.data[i];
    int32_t other_id;

    if (!uf_plugin_fun_diseq_entry_is_active(uf, entry)) {
      continue;
    }
    if (entry->lhs == t &&
        uf_plugin_term_has_function_id(uf, entry->rhs, &other_id) &&
        other_id == id) {
      return true;
    }
    if (entry->rhs == t &&
        uf_plugin_term_has_function_id(uf, entry->lhs, &other_id) &&
        other_id == id) {
      return true;
    }
  }

  for (i = 0; i < uf->fun_model_diseq_entries.size; ++ i) {
    uf_fun_model_diseq_t* entry = uf->fun_model_diseq_entries.data[i];
    int32_t other_id;

    if (!uf_plugin_fun_model_diseq_entry_is_active(uf, entry)) {
      continue;
    }
    if (entry->lhs == t &&
        uf_plugin_term_has_function_id(uf, entry->rhs, &other_id) &&
        other_id == id) {
      return true;
    }
    if (entry->rhs == t &&
        uf_plugin_term_has_function_id(uf, entry->lhs, &other_id) &&
        other_id == id) {
      return true;
    }
  }

  return false;
}

static bool uf_plugin_pick_active_function_id(uf_plugin_t* uf, term_t t, type_t tau, const pvector_t* forbidden,
                                              int32_t* picked_id) {
  uint32_t i;
  type_t key;

  key = uf_function_type_key(uf, tau);
  uf_plugin_rebuild_active_fun_ids(uf);
  for (i = 0; i < uf->active_fun_terms.size; ++ i) {
    int32_t id;

    if (key != (type_t) uf->active_fun_type_keys.data[i]) {
      continue;
    }

    id = uf->active_fun_ids.data[i];
    if (!uf_plugin_forbidden_contains_id(forbidden, id) &&
        uf_plugin_function_id_key_is_allowed(uf, id, key) &&
        !uf_plugin_active_diseq_blocks_function_id(uf, t, id)) {
      uf_plugin_record_function_id_key(uf, id, key);
      *picked_id = id;
      return true;
    }
  }

  return false;
}

static bool uf_plugin_cached_function_id_is_allowed(uf_plugin_t* uf, term_t t, const pvector_t* forbidden,
                                                    const mcsat_value_t* candidate) {
  type_t tau;
  type_t key;
  int32_t id, active_id;

  if (candidate == NULL ||
      candidate->type != VALUE_RATIONAL ||
      !q_get32((rational_t*) &candidate->q, &id) ||
      uf_plugin_forbidden_contains_id(forbidden, id) ||
      uf_plugin_active_diseq_blocks_function_id(uf, t, id)) {
    return false;
  }

  tau = term_type(uf->ctx->terms, t);
  key = uf_function_type_key(uf, tau);
  if (!uf_plugin_function_id_key_is_allowed(uf, id, key)) {
    return false;
  }

  if (!uf_plugin_pick_active_function_id(uf, t, tau, forbidden, &active_id)) {
    uf_plugin_record_function_id_key(uf, id, key);
    return true;
  }

  if (id == active_id) {
    uf_plugin_record_function_id_key(uf, id, key);
    return true;
  }

  return false;
}

static bool uf_plugin_literal_is_true_in_branch(uf_plugin_t* uf, term_t t) {
  term_table_t* terms = uf->ctx->terms;
  variable_db_t* var_db = uf->ctx->var_db;
  const mcsat_trail_t* trail = uf->ctx->trail;
  term_t atom;
  bool negated;

  if (t == true_term) {
    return true;
  }
  if (t == false_term) {
    return false;
  }
  if (mcsat_branch_bool_term_is_true(uf->ctx, t)) {
    return true;
  }
  if (mcsat_branch_bool_term_is_false(uf->ctx, t)) {
    return false;
  }

  atom = unsigned_term(t);
  negated = atom != t;
  if (term_kind(terms, atom) == EQ_TERM) {
    composite_term_t* eq = eq_term_desc(terms, atom);
    term_t lhs = eq->arg[0];
    term_t rhs = eq->arg[1];
    variable_t lhs_var;
    variable_t rhs_var;
    bool lhs_eq_rhs;

    if (term_type(terms, lhs) == term_type(terms, rhs) &&
        is_unit_type(uf->ctx->types, term_type(terms, lhs))) {
      return !negated;
    }

    lhs_var = variable_db_get_variable_if_exists(var_db, lhs);
    rhs_var = variable_db_get_variable_if_exists(var_db, rhs);
    if (lhs_var != variable_null &&
        rhs_var != variable_null &&
        trail_has_value(trail, lhs_var) &&
        trail_has_value(trail, rhs_var)) {
      lhs_eq_rhs = mcsat_value_eq(trail_get_value(trail, lhs_var),
                                  trail_get_value(trail, rhs_var));
      return negated ? !lhs_eq_rhs : lhs_eq_rhs;
    }

    if (eq_graph_has_term(&uf->eq_graph, lhs) &&
        eq_graph_has_term(&uf->eq_graph, rhs) &&
        eq_graph_term_has_value(&uf->eq_graph, lhs) &&
        eq_graph_term_has_value(&uf->eq_graph, rhs)) {
      lhs_eq_rhs = mcsat_value_eq(eq_graph_get_propagated_term_value(&uf->eq_graph, lhs),
                                  eq_graph_get_propagated_term_value(&uf->eq_graph, rhs));
      return negated ? !lhs_eq_rhs : lhs_eq_rhs;
    }
  }

  return false;
}

static bool uf_plugin_fun_diseq_entry_is_active(uf_plugin_t* uf, const uf_fun_diseq_t* entry) {
  int32_t lhs_id, rhs_id;
  bool active;

  switch (entry->source) {
  case UF_FUN_DISEQ_EXPLICIT:
    active = entry->guard != NULL_TERM && mcsat_branch_bool_term_is_false(uf->ctx, entry->guard);
    break;
  case UF_FUN_DISEQ_DISTINCT_ID:
    active = uf_plugin_term_has_function_id(uf, entry->lhs, &lhs_id) &&
      uf_plugin_term_has_function_id(uf, entry->rhs, &rhs_id) &&
      lhs_id != rhs_id;
    break;
  default:
    assert(false);
    return false;
  }

  assert(!active || !mcsat_branch_equality_sensitivity_is_frozen(uf->ctx) ||
         mcsat_branch_type_is_equality_sensitive(uf->ctx, entry->type) ||
         !"active UF diff entry on non-sensitive type");
  return active;
}

static bool uf_plugin_fun_model_diseq_entry_is_active(uf_plugin_t* uf, const uf_fun_model_diseq_t* entry) {
  int32_t lhs_id, rhs_id;
  bool active;

  switch (entry->source) {
  case UF_FUN_DISEQ_EXPLICIT:
    active = entry->guard != NULL_TERM && mcsat_branch_bool_term_is_false(uf->ctx, entry->guard);
    break;
  case UF_FUN_DISEQ_DISTINCT_ID:
    active = uf_plugin_term_has_function_id(uf, entry->lhs, &lhs_id) &&
      uf_plugin_term_has_function_id(uf, entry->rhs, &rhs_id) &&
      lhs_id != rhs_id;
    break;
  default:
    assert(false);
    return false;
  }

  assert(!active || !mcsat_branch_equality_sensitivity_is_frozen(uf->ctx) ||
         mcsat_branch_type_is_equality_sensitive(uf->ctx, entry->type) ||
         !"active UF model-diseq entry on non-sensitive type");
  return active;
}

static term_t uf_plugin_distinct_id_eq_atom(uf_plugin_t* uf, term_t lhs, term_t rhs) {
  type_t tau;
  term_t eq;

  if (!uf_plugin_fun_pair_super_type(uf, lhs, rhs, &tau)) {
    return NULL_TERM;
  }
  assert(type_kind(uf->ctx->types, tau) == FUNCTION_TYPE);
  assert(uf->ctx->equality_sensitivity_is_frozen == NULL ||
         uf->ctx->equality_sensitivity_is_frozen(uf->ctx));
  assert(uf->ctx->type_is_equality_sensitive == NULL ||
         uf->ctx->type_is_equality_sensitive(uf->ctx, tau));
#ifndef NDEBUG
  uf_plugin_assert_generated_equality_sensitive(uf, "distinct id equality atom", lhs, rhs);
#endif
  (void) tau;

  eq = _o_yices_eq(lhs, rhs);
  if (eq != true_term && eq != false_term) {
    uf->ctx->register_term(uf->ctx, eq);
  }
  return eq;
}

static term_t uf_plugin_distinct_id_diseq_literal(uf_plugin_t* uf, term_t lhs, term_t rhs) {
  term_t eq = uf_plugin_distinct_id_eq_atom(uf, lhs, rhs);
  assert(eq != NULL_TERM);
  return eq == NULL_TERM ? NULL_TERM : opposite_term(eq);
}

static term_t uf_plugin_fun_diseq_literal(uf_plugin_t* uf, const uf_fun_diseq_t* entry) {
  if (entry->source == UF_FUN_DISEQ_EXPLICIT && entry->guard != NULL_TERM) {
    return opposite_term(entry->guard);
  }

  assert(entry->source == UF_FUN_DISEQ_DISTINCT_ID);
  return uf_plugin_distinct_id_diseq_literal(uf, entry->lhs, entry->rhs);
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

static variable_t uf_plugin_get_subterm_variable(uf_plugin_t* uf, term_t t) {
  if (t == true_term || t == false_term) {
    return variable_null;
  }

  return variable_db_get_variable(uf->ctx->var_db, unsigned_term(t));
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

static bool uf_plugin_check_explicit_distinct_cardinality_conflict(uf_plugin_t* uf) {
  term_table_t* terms = uf->ctx->terms;
  type_table_t* types = uf->ctx->types;
  variable_db_t* var_db = uf->ctx->var_db;
  const mcsat_trail_t* trail = uf->ctx->trail;
  uint32_t i, j, n;

  if (!mcsat_branch_equality_sensitivity_is_frozen(uf->ctx)) {
    return false;
  }

  n = trail_size(trail);
  for (i = 0; i < n; ++ i) {
    variable_t v = trail_at(trail, i);
    term_t t = variable_db_get_term(var_db, v);
    const mcsat_value_t* value;
    composite_term_t* distinct;
    type_t tau;
    uint32_t card;

    if (t == NULL_TERM || term_kind(terms, t) != DISTINCT_TERM) {
      continue;
    }

    value = trail_get_value(trail, v);
    if (value->type != VALUE_BOOLEAN || !value->b) {
      continue;
    }

    distinct = distinct_term_desc(terms, t);
    if (distinct->arity == 0) {
      continue;
    }

    tau = term_type(terms, distinct->arg[0]);
    if (type_kind(types, tau) != FUNCTION_TYPE ||
        !mcsat_branch_type_is_equality_sensitive(uf->ctx, tau) ||
        !uf_function_type_exact_cardinality(types, tau, &card) ||
        distinct->arity <= card) {
      continue;
    }

    for (j = 0; j < distinct->arity; ++ j) {
      if (term_type(terms, distinct->arg[j]) != tau ||
          int_hset_member(&uf->diff_witness_terms, distinct->arg[j])) {
        break;
      }
    }
    if (j < distinct->arity) {
      continue;
    }

    ivector_reset(&uf->conflict);
    ivector_push(&uf->conflict, t);
    (*uf->stats.fun_diseq_cardinality_conflicts) ++;
    return true;
  }

  return false;
}

static bool uf_plugin_check_distinct_id_cardinality_conflict(uf_plugin_t* uf) {
  type_table_t* types = uf->ctx->types;
  ivector_t seen_types;
  ivector_t reps;
  ivector_t rep_ids;
  uint32_t i, j, k, n;
  bool conflict_found = false;

  if (!mcsat_branch_equality_sensitivity_is_frozen(uf->ctx)) {
    return false;
  }

  init_ivector(&seen_types, 0);
  init_ivector(&reps, 0);
  init_ivector(&rep_ids, 0);

  n = uf->active_fun_terms.size;
  for (i = 0; i < n && !conflict_found; ++ i) {
    type_t key = uf->active_fun_type_keys.data[i];
    uint32_t card;

    if (ivector_contains_term(&seen_types, key)) {
      continue;
    }
    ivector_push(&seen_types, key);

    if (!uf_type_needs_search_diff(uf, key)) {
      continue;
    }

    if (!uf_function_type_exact_cardinality(types, key, &card) ||
        card >= UF_FUN_CARDINALITY_CLIQUE_TERM_CAP) {
      continue;
    }

    ivector_reset(&reps);
    ivector_reset(&rep_ids);
    for (j = i; j < n && reps.size <= card; ++ j) {
      int32_t id;
      term_t t;

      if (key != (type_t) uf->active_fun_type_keys.data[j]) {
        continue;
      }

      id = uf->active_fun_ids.data[j];
      if (ivector_contains_term(&rep_ids, id)) {
        continue;
      }

      t = uf->active_fun_terms.data[j];
      if (int_hset_member(&uf->diff_witness_terms, t)) {
        continue;
      }

      ivector_push(&reps, t);
      ivector_push(&rep_ids, id);
    }

    if (reps.size <= card) {
      continue;
    }

    ivector_reset(&uf->conflict);
    for (j = 0; j < reps.size; ++ j) {
      for (k = j + 1; k < reps.size; ++ k) {
        ivector_push(&uf->conflict,
                     uf_plugin_distinct_id_diseq_literal(uf, reps.data[j], reps.data[k]));
      }
    }
    ivector_remove_duplicates(&uf->conflict);
    conflict_found = uf->conflict.size > 0;
    if (conflict_found) {
      (*uf->stats.fun_diseq_cardinality_conflicts) ++;
    }
  }

  if (!conflict_found) {
    ivector_reset(&uf->conflict);
  }
  delete_ivector(&rep_ids);
  delete_ivector(&reps);
  delete_ivector(&seen_types);
  return conflict_found;
}

static bool uf_plugin_check_fun_cardinality_conflict(uf_plugin_t* uf) {
  type_table_t* types = uf->ctx->types;
  ivector_t seen_types;
  ivector_t terms;
  uint32_t i, j, k;
  bool conflict_found = false;

  init_ivector(&seen_types, 0);
  init_ivector(&terms, 0);

  if (uf_plugin_check_explicit_distinct_cardinality_conflict(uf) ||
      uf_plugin_check_distinct_id_cardinality_conflict(uf)) {
    delete_ivector(&terms);
    delete_ivector(&seen_types);
    return true;
  }

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

    if (!uf_function_type_exact_cardinality(types, tau, &card)) {
      continue;
    }
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
      if (conflict_found) {
        (*uf->stats.fun_diseq_cardinality_conflicts) ++;
      }
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

#ifndef NDEBUG
  uf_plugin_assert_generated_equality_sensitive(uf, "branch equality check", lhs, rhs);
#endif
  eq = _o_yices_eq(lhs, rhs);
  if (eq == NULL_TERM ||
      eq == false_term ||
      mcsat_branch_bool_term_is_false(uf->ctx, eq)) {
    return false;
  }
  if (eq == true_term || mcsat_branch_bool_term_is_true(uf->ctx, eq)) {
    return true;
  }

  if (eq_graph_has_term(&uf->eq_graph, lhs) &&
      eq_graph_has_term(&uf->eq_graph, rhs) &&
      eq_graph_term_has_value(&uf->eq_graph, lhs) &&
      eq_graph_term_has_value(&uf->eq_graph, rhs) &&
      mcsat_value_eq(eq_graph_get_propagated_term_value(&uf->eq_graph, lhs),
                     eq_graph_get_propagated_term_value(&uf->eq_graph, rhs))) {
    return true;
  }

  return false;
}

static bool uf_plugin_add_terms_equal_reason(uf_plugin_t* uf, term_t lhs, term_t rhs,
                                             ivector_t* reason) {
  term_t eq;
  type_t lhs_type;
  ivector_t reasons;
  uint32_t i;

  if (lhs == rhs) {
    return true;
  }

  lhs_type = term_type(uf->ctx->terms, lhs);
  if (lhs_type == term_type(uf->ctx->terms, rhs) &&
      is_unit_type(uf->ctx->types, lhs_type)) {
    return true;
  }

#ifndef NDEBUG
  uf_plugin_assert_generated_equality_sensitive(uf, "equality reason", lhs, rhs);
#endif
  eq = _o_yices_eq(lhs, rhs);
  if (eq == NULL_TERM ||
      eq == false_term ||
      mcsat_branch_bool_term_is_false(uf->ctx, eq)) {
    return false;
  }

  if (eq == true_term) {
    return true;
  }

  if (mcsat_branch_bool_term_is_true(uf->ctx, eq)) {
    ivector_push(reason, eq);
    return true;
  }

  if (eq_graph_has_term(&uf->eq_graph, lhs) &&
      eq_graph_has_term(&uf->eq_graph, rhs) &&
      eq_graph_term_has_value(&uf->eq_graph, lhs) &&
      eq_graph_term_has_value(&uf->eq_graph, rhs) &&
      mcsat_value_eq(eq_graph_get_propagated_term_value(&uf->eq_graph, lhs),
                     eq_graph_get_propagated_term_value(&uf->eq_graph, rhs))) {
    assert(eq_graph_are_equal(&uf->eq_graph, lhs, rhs));
    init_ivector(&reasons, 0);
    eq_graph_explain_eq(&uf->eq_graph, lhs, rhs, &reasons, NULL, &uf->tmp);
    for (i = 0; i < reasons.size; ++ i) {
      if (!uf_plugin_literal_is_true_in_branch(uf, reasons.data[i])) {
        delete_ivector(&reasons);
        uf_plugin_bump_terms_and_reset(uf, &uf->tmp);
        return false;
      }
    }
    for (i = 0; i < reasons.size; ++ i) {
      if (reasons.data[i] != true_term) {
        ivector_push(reason, reasons.data[i]);
      }
    }
    delete_ivector(&reasons);
    uf_plugin_bump_terms_and_reset(uf, &uf->tmp);
    return true;
  }

  return false;
}

static bool uf_plugin_check_fun_extensionality_conflict(uf_plugin_t* uf) {
  uint32_t i;

  for (i = 0; i < uf->fun_diseq_entries.size; ++ i) {
    uf_fun_diseq_t* entry = uf->fun_diseq_entries.data[i];
    term_t diseq;

    if (!uf_plugin_fun_diseq_entry_is_active(uf, entry) ||
        !uf_plugin_terms_are_equal_in_branch(uf, entry->lhs_app, entry->rhs_app)) {
      continue;
    }

    diseq = uf_plugin_fun_diseq_literal(uf, entry);

    ivector_reset(&uf->conflict);
    ivector_push(&uf->conflict, diseq);
    if (!uf_plugin_add_terms_equal_reason(uf, entry->lhs_app, entry->rhs_app, &uf->conflict)) {
      ivector_reset(&uf->conflict);
      continue;
    }
    ivector_remove_duplicates(&uf->conflict);
    return true;
  }

  return false;
}

static void uf_plugin_rebuild_active_fun_ids(uf_plugin_t* uf) {
  variable_db_t* var_db = uf->ctx->var_db;
  const mcsat_trail_t* trail = uf->ctx->trail;
  uint32_t i, n;

  if (!mcsat_branch_equality_sensitivity_is_frozen(uf->ctx)) {
    ivector_reset(&uf->active_fun_terms);
    ivector_reset(&uf->active_fun_types);
    ivector_reset(&uf->active_fun_type_keys);
    ivector_reset(&uf->active_fun_ids);
    uf->active_fun_ids_valid = false;
    return;
  }
  uf_plugin_refresh_equality_sensitivity_generation(uf);

  n = trail_size(trail);
  if (uf->active_fun_ids_valid &&
      uf->active_fun_trail_size == n &&
      uf->active_fun_generation == uf->equality_sensitivity_generation) {
    return;
  }

  ivector_reset(&uf->active_fun_terms);
  ivector_reset(&uf->active_fun_types);
  ivector_reset(&uf->active_fun_type_keys);
  ivector_reset(&uf->active_fun_ids);

  for (i = 0; i < n; ++ i) {
    variable_t v = trail_at(trail, i);
    term_t t = variable_db_get_term(var_db, v);
    const mcsat_value_t* value;
    type_t tau;
    type_t key;
    int32_t id;

    if (t == NULL_TERM || int_hset_member(&uf->diff_witness_terms, t)) {
      continue;
    }

    tau = term_type(uf->ctx->terms, t);
    if (type_kind(uf->ctx->types, tau) == FUNCTION_TYPE) {
      key = uf_function_type_key(uf, tau);
      if (!uf_type_needs_search_diff(uf, key)) {
        continue;
      }

      value = trail_get_value(trail, v);
      if (value->type != VALUE_RATIONAL ||
          !q_get32((rational_t*) &value->q, &id)) {
        continue;
      }
      if (!uf_plugin_term_has_direct_trail_assignment(uf, t, v)) {
        continue;
      }
      if (!uf_plugin_function_id_key_is_allowed(uf, id, key)) {
        assert(false && "function id used with incompatible normalized type key");
        continue;
      }
      uf_plugin_record_function_id_key(uf, id, key);

      bool found = false;
      uint32_t j;
      for (j = 0; j < uf->active_fun_terms.size; ++ j) {
        if (key == (type_t) uf->active_fun_type_keys.data[j] &&
            id == uf->active_fun_ids.data[j]) {
          found = true;
          break;
        }
      }
      if (!found) {
        ivector_push(&uf->active_fun_terms, t);
        ivector_push(&uf->active_fun_types, tau);
        ivector_push(&uf->active_fun_type_keys, key);
        ivector_push(&uf->active_fun_ids, id);
      }
    }
  }

  uf->active_fun_trail_size = n;
  uf->active_fun_generation = uf->equality_sensitivity_generation;
  uf->active_fun_ids_valid = true;
}


static
void uf_plugin_stats_init(uf_plugin_t* uf) {
  // Add statistics
  uf->stats.propagations = statistics_new_int(uf->ctx->stats, "mcsat::uf::propagations");
  uf->stats.conflicts = statistics_new_int(uf->ctx->stats, "mcsat::uf::conflicts");
  uf->stats.egraph_terms = statistics_new_int(uf->ctx->stats, "mcsat::uf::egraph_terms");
  uf->stats.fun_diseq_explicit = statistics_new_int(uf->ctx->stats, "mcsat::uf::fun_diseq_explicit");
  uf->stats.fun_diseq_distinct_id = statistics_new_int(uf->ctx->stats, "mcsat::uf::fun_diseq_distinct_id");
  uf->stats.fun_diseq_model = statistics_new_int(uf->ctx->stats, "mcsat::uf::fun_diseq_model");
  uf->stats.fun_diseq_incompatible_id_merges = statistics_new_int(uf->ctx->stats, "mcsat::uf::fun_diseq_incompatible_id_merges");
  uf->stats.fun_diseq_witnesses = statistics_new_int(uf->ctx->stats, "mcsat::uf::fun_diseq_witnesses");
  uf->stats.fun_diseq_cardinality_conflicts = statistics_new_int(uf->ctx->stats, "mcsat::uf::fun_diseq_cardinality_conflicts");
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
  init_int_hmap(&uf->fun_value_type_keys, 0);
  init_pvector(&uf->fun_diseq_entries, 0);
  init_pvector(&uf->fun_model_diseq_entries, 0);
  init_int_hset(&uf->diff_witness_terms, 0);
  init_pmap(&uf->diff_witness_cache, 0);
  init_pvector(&uf->diff_witness_cache_entries, 0);
  init_int_hset(&uf->generated_witness_eqs, 0);
  uf->fun_diseq_trail_scan_index = 0;
  init_ivector(&uf->active_fun_terms, 0);
  init_ivector(&uf->active_fun_types, 0);
  init_ivector(&uf->active_fun_type_keys, 0);
  init_ivector(&uf->active_fun_ids, 0);
  uf->active_fun_trail_size = 0;
  uf->active_fun_generation = 0;
  uf->active_fun_ids_valid = false;
  init_int_hmap(&uf->risky_function_type_cache, 0);
  uf->equality_sensitivity_generation = 0;
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
  delete_int_hmap(&uf->fun_value_type_keys);
  uf_plugin_free_fun_diseq_entries_from(uf, 0);
  delete_pvector(&uf->fun_diseq_entries);
  uf_plugin_free_fun_model_diseq_entries_from(uf, 0);
  delete_pvector(&uf->fun_model_diseq_entries);
  uf_plugin_free_diff_witness_cache(uf);
  delete_pvector(&uf->diff_witness_cache_entries);
  delete_pmap(&uf->diff_witness_cache);
  delete_int_hset(&uf->diff_witness_terms);
  delete_int_hset(&uf->generated_witness_eqs);
  delete_ivector(&uf->active_fun_terms);
  delete_ivector(&uf->active_fun_types);
  delete_ivector(&uf->active_fun_type_keys);
  delete_ivector(&uf->active_fun_ids);
  delete_int_hmap(&uf->risky_function_type_cache);
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
      term_t t_atom;
      // Variable to propagate
      variable_t t_var;

      if (t == true_term || t == false_term) {
        continue;
      }

      t_atom = unsigned_term(t);
      t_var = variable_db_get_variable_if_exists(uf->ctx->var_db, t_atom);
      if (t_var != variable_null) {
        // Only set values of uninterpreted, function and boolean type
        type_kind_t t_type_kind = term_type_kind(uf->ctx->terms, t_atom);
        if (t_type_kind == UNINTERPRETED_TYPE ||
            t_type_kind == FUNCTION_TYPE ||
            t_type_kind == BOOL_TYPE) {
          const mcsat_value_t* v = eq_graph_get_propagated_term_value(&uf->eq_graph, t);
          mcsat_value_t atom_value;
          if (t_atom != t) {
            assert(v->type == VALUE_BOOLEAN);
            mcsat_value_construct_bool(&atom_value, !v->b);
            v = &atom_value;
          }
          if (!trail_has_value(uf->ctx->trail, t_var)) {
            if (ctx_trace_enabled(uf->ctx, "mcsat::eq::propagate")) {
              FILE* out = ctx_trace_out(uf->ctx);
              ctx_trace_term(uf->ctx, t_atom);
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
    if (term_kind(terms, t_desc->arg[0]) == UPDATE_TERM) {
      composite_term_t* update_desc = update_term_desc(terms, t_desc->arg[0]);
      if (t_desc->arity > 2 && t_desc->arity == update_desc->arity - 1) {
        uint32_t i;
        term_t r = app_term(terms, update_desc->arg[0], t_desc->arity - 1, t_desc->arg + 1);
        uf->ctx->register_term(uf->ctx, r);
        weq_graph_add_select_term(&uf->weq_graph, r);
        for (i = 1; i < t_desc->arity; ++ i) {
          term_t eq = _o_yices_eq(t_desc->arg[i], update_desc->arg[i]);
          if (eq != true_term && eq != false_term) {
            uf->ctx->register_term(uf->ctx, unsigned_term(eq));
          }
        }
      }
    }
    break;
  case UPDATE_TERM:
    t_desc = update_term_desc(terms, t);
    eq_graph_add_ufun_term(&uf->eq_graph, t, t_desc->arg[0], t_desc->arity - 1, t_desc->arg + 1);
    // remember array term
    weq_graph_add_array_term(&uf->weq_graph, t);
    weq_graph_add_array_term(&uf->weq_graph, t_desc->arg[0]);
    // remember select terms
    term_t r1 = app_term(terms, t, t_desc->arity - 2, t_desc->arg + 1);
    if (t_desc->arity > 3) {
      uf->ctx->register_term(uf->ctx, r1);
    } else {
      variable_db_get_variable(uf->ctx->var_db, r1);
    }
    weq_graph_add_select_term(&uf->weq_graph, r1);
    // if the element domain is finite then we add this extra read term
    type_t element_type = term_type(terms, t_desc->arg[t_desc->arity - 1]);
    if (is_finite_type(terms->types, element_type) || is_boolean_type(element_type) || is_bv_type(terms->types, element_type)){
      term_t r2 = app_term(terms, t_desc->arg[0], t_desc->arity - 2, t_desc->arg + 1);
      if (t_desc->arity > 3) {
        uf->ctx->register_term(uf->ctx, r2);
      } else {
        variable_db_get_variable(uf->ctx->var_db, r2);
      }
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
    variable_t c_var = uf_plugin_get_subterm_variable(uf, c);
    if (c_var == variable_null) {
      continue;
    }
    if (trail_has_value(uf->ctx->trail, c_var)) {
      // we need to process it if we ignored it
      if (eq_graph_term_is_rep(&uf->eq_graph, unsigned_term(c))) {
        eq_graph_propagate_trail_assertion(&uf->eq_graph, unsigned_term(c));
        uf_plugin_invalidate_active_fun_ids(uf);
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
  bool added_distinct_id_witnesses;
  bool cardinality_checked_after_witnesses;

  if (ctx_trace_enabled(uf->ctx, "uf_plugin")) {
    ctx_trace_printf(uf->ctx, "uf_plugin_propagate()\n");
  }

  uf_plugin_refresh_equality_sensitivity_generation(uf);

  // If we're not watching anything, we just ignore.
  if (eq_graph_term_size(&uf->eq_graph) == 0) {
    return;
  }

  bool added_fun_diseq_witnesses = uf_plugin_add_explicit_fun_diseq_witnesses(uf);
  if (uf->conflict.size > 0) {
    prop->conflict(prop);
    (*uf->stats.conflicts) ++;
    statistic_avg_add(uf->stats.avg_conflict_size, uf->conflict.size);
    return;
  }

  // Propagate known terms
  eq_graph_propagate_trail(&uf->eq_graph);
  uf_plugin_invalidate_active_fun_ids(uf);
  uf_plugin_rebuild_active_fun_ids(uf);
  uf_plugin_process_eq_graph_propagations(uf, prop);
  uf_plugin_rebuild_active_fun_ids(uf);
  if (added_fun_diseq_witnesses && uf_plugin_check_fun_cardinality_conflict(uf)) {
    prop->conflict(prop);
    (*uf->stats.conflicts) ++;
    statistic_avg_add(uf->stats.avg_conflict_size, uf->conflict.size);
    return;
  }
  cardinality_checked_after_witnesses = added_fun_diseq_witnesses;
  added_distinct_id_witnesses = uf_plugin_add_distinct_id_fun_diseq_witnesses(uf);
  added_fun_diseq_witnesses = added_distinct_id_witnesses || added_fun_diseq_witnesses;
  if (added_distinct_id_witnesses) {
    cardinality_checked_after_witnesses = false;
  }
  if (uf->conflict.size > 0) {
    prop->conflict(prop);
    (*uf->stats.conflicts) ++;
    statistic_avg_add(uf->stats.avg_conflict_size, uf->conflict.size);
    return;
  }
  if (added_fun_diseq_witnesses) {
    eq_graph_propagate_trail(&uf->eq_graph);
    uf_plugin_invalidate_active_fun_ids(uf);
    uf_plugin_process_eq_graph_propagations(uf, prop);
    uf_plugin_rebuild_active_fun_ids(uf);
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

  if (!cardinality_checked_after_witnesses && uf_plugin_check_fun_cardinality_conflict(uf)) {
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

  // Some checks above can register generated terms synchronously. Registration
  // may add terms to the equality graph and produce term/value notifications
  // after the main propagation drain, so consume them before the solver can
  // create a new decision scope.
  if (uf->conflict.size == 0 && uf_plugin_process_eq_graph_propagations(uf, prop)) {
    uf_plugin_invalidate_active_fun_ids(uf);
  }
}

static
void uf_plugin_push(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  // Push the int variable values
  scope_holder_push(&uf->scope,
                    &uf->eq_graph_addition_trail.size,
                    &uf->fun_diseq_entries.size,
                    &uf->fun_model_diseq_entries.size,
                    &uf->fun_diseq_trail_scan_index,
                    NULL);

  weq_graph_push(&uf->weq_graph);
  eq_graph_push(&uf->eq_graph);
}

static
void uf_plugin_pop(plugin_t* plugin) {
  uf_plugin_t* uf = (uf_plugin_t*) plugin;

  uint32_t old_eq_graph_addition_trail_size, old_fun_diseq_entries_size;
  uint32_t old_fun_model_diseq_entries_size;
  uint32_t old_fun_diseq_trail_scan_index;

  // Pop the int variable values
  scope_holder_pop(&uf->scope,
                   &old_eq_graph_addition_trail_size,
                   &old_fun_diseq_entries_size,
                   &old_fun_model_diseq_entries_size,
                   &old_fun_diseq_trail_scan_index,
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
  uf_plugin_free_fun_model_diseq_entries_from(uf, old_fun_model_diseq_entries_size);
  uf->fun_diseq_trail_scan_index = old_fun_diseq_trail_scan_index;
  ivector_reset(&uf->active_fun_terms);
  ivector_reset(&uf->active_fun_types);
  ivector_reset(&uf->active_fun_type_keys);
  ivector_reset(&uf->active_fun_ids);
  uf->active_fun_ids_valid = false;
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

  term_t x_term = variable_db_get_term(uf->ctx->var_db, x);
  term_table_t *terms = uf->ctx->terms;
  bool x_is_function = term_type_kind(terms, x_term) == FUNCTION_TYPE;

  // Pick a value not in the forbidden set
  pvector_t forbidden;
  init_pvector(&forbidden, 0);
  const mcsat_value_t* x_cached_value = NULL;
  bool cache_ok;

  if (x_is_function) {
    uint32_t i;

    cache_ok = false;
    (void) eq_graph_get_forbidden(&uf->eq_graph, x_term, &forbidden, NULL);
    for (i = 0; i < x_num_candidates; ++ i) {
      if (eq_graph_get_forbidden(&uf->eq_graph, x_term, NULL, x_candidates[i]) &&
          uf_plugin_cached_function_id_is_allowed(uf, x_term, &forbidden, x_candidates[i])) {
        x_cached_value = x_candidates[i];
        cache_ok = true;
        break;
      }
    }
  } else {
    // Build the forbidden list while testing the first candidate (the list does not
    // depend on the candidate, so pass NULL when there is none); then test any
    // remaining candidates against the already-built list (values == NULL).
    cache_ok = eq_graph_get_forbidden(&uf->eq_graph, x_term, &forbidden,
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
      type_t tau = term_type(terms, x_term);
      type_t key = uf_function_type_key(uf, tau);
      bool picked_existing_function_value = false;
      if (uf_plugin_pick_active_function_id(uf, x_term, tau, &forbidden, &picked_value)) {
        assert(!uf_plugin_forbidden_contains_id(&forbidden, picked_value));
        picked_existing_function_value = true;
      } else if (forbidden.size > 0) {
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

      while (!picked_existing_function_value && int_hset_member(&uf->fun_used_values, picked_value)) {
        picked_value += 1;
      }
      /*
       * Function ids are untyped rational values in the equality graph, so a
       * value reused across different function types can create ill-typed
       * equality explanations. Reuse is only deliberate when we selected an
       * active same-type id above; otherwise reserve a globally fresh id even
       * if the same-type search policy asked us not to create a new split.
       */
      if (!picked_existing_function_value) {
        int_hset_add(&uf->fun_used_values, picked_value);
      }
      uf_plugin_record_function_id_key(uf, picked_value, key);
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
  if (t_var != variable_null && trail_has_value(uf->ctx->trail, t_var)) {
    const mcsat_value_t* t_value = trail_get_value(uf->ctx->trail, t_var);
    return mcsat_value_to_value(t_value, uf->ctx->types, t_type, vtbl);
  }

  term_converter_t convert;
  value_t value;

  init_term_converter(&convert, uf->ctx->terms, vtbl);
  value = convert_term_to_val(&convert, t);
  delete_term_converter(&convert);

  return value >= 0 ? value : null_value;
}

// Default value of type tau for use as the "else" branch of a function.
// Kept as a wrapper for readability at call sites.
static inline
value_t vtbl_mk_default(value_table_t *vtbl, type_t tau) {
  return vtbl_make_object(vtbl, tau);
}

typedef struct {
  int32_t function_id;
  type_t type;
  uint32_t arity;
  value_t value;
  value_t arguments[0];
} uf_model_app_value_t;

typedef struct {
  uf_plugin_t* uf;
  value_table_t* vtbl;
  fresh_val_maker_t maker;
  ivector_t app_terms;
  ivector_t arguments;
  int_hmap_t app_term_first;
  int_hmap_t function_term;
  int_hmap2_t function_value;
  pvector_t app_value_reservations;
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
  init_int_hmap2(&builder->function_value, 0);
  init_pvector(&builder->app_value_reservations, 0);
}

static
void uf_model_builder_destruct(uf_model_builder_t* builder) {
  while (builder->app_value_reservations.size > 0) {
    safe_free(pvector_pop2(&builder->app_value_reservations));
  }
  delete_pvector(&builder->app_value_reservations);
  delete_int_hmap2(&builder->function_value);
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
  int_hmap2_rec_t* find;
  term_table_t* terms = builder->uf->ctx->terms;
  type_table_t* types = builder->uf->ctx->types;
  type_t fun_type;
  value_t f_value;
  ivector_t arguments;
  bool new_record;

  assert(term_type_kind(terms, t) == FUNCTION_TYPE);

  if (!uf_plugin_get_function_id(builder->uf, t, &function_id)) {
    return null_value;  // LCOV_EXCL_LINE - defensive fallback, unreachable on supported inputs
  }

  uf_model_builder_remember_function_term(builder, t);

  fun_type = term_type(terms, t);
  find = int_hmap2_get(&builder->function_value, function_id, fun_type, &new_record);
  if (new_record) {
    find->val = -1;
  }
  if (find->val >= 0) {
    return find->val;
  }

  init_ivector(&arguments, 0);

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
      if (!is_subtype(types, term_type(terms, app_term), function_type_range(types, fun_type))) {
        continue;
      }

      ivector_reset(&arguments);
      uint32_t arg_i;
      for (arg_i = 1; arg_i < app_desc->arity; ++ arg_i) {
        value_t arg_value = uf_model_builder_get_term_value(builder, app_desc->arg[arg_i]);
        if (arg_value == null_value) {
          break;
        }
        ivector_push(&arguments, arg_value);
      }
      if (arg_i < app_desc->arity) {
        continue;
      }

      value_t result_value = uf_model_builder_get_term_value(builder, app_term);
      if (result_value == null_value) {
        continue;
      }
      f_value = vtbl_mk_update(builder->vtbl, f_value, arguments.size, arguments.data, result_value);
    }

    // Re-fetch: the recursive calls above may have inserted new entries into
    // builder->function_value and triggered int_hmap_extend, which invalidates
    // any int_hmap_pair_t* obtained before recursion.
    int_hmap2_get(&builder->function_value, function_id, fun_type, &new_record)->val = f_value;
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
bool uf_model_builder_make_fresh_domain_values(uf_model_builder_t* builder, type_t tau, ivector_t* arguments) {
  type_table_t* types = builder->uf->ctx->types;
  uint32_t i, arity;
  bool has_fresh_component = false;

  assert(type_kind(types, tau) == FUNCTION_TYPE);

  ivector_reset(arguments);
  arity = function_type_arity(types, tau);
  for (i = 0; i < arity; ++ i) {
    type_t sigma = function_type_domain(types, tau, i);
    value_t v;

    if (is_finite_type(types, sigma)) {
      v = vtbl_make_object(builder->vtbl, sigma);
    } else {
      v = make_fresh_value(&builder->maker, sigma);
      has_fresh_component = true;
    }

    if (v == null_value) {
      ivector_reset(arguments);
      return false;
    }
    ivector_push(arguments, v);
  }

  return has_fresh_component;
}

static bool uf_model_builder_pick_distinct_range_values(uf_model_builder_t* builder,
                                                        type_t lhs_range, type_t rhs_range,
                                                        value_t* lhs_value, value_t* rhs_value);

static
void uf_model_builder_apply_model_diseqs(uf_model_builder_t* builder) {
  uf_plugin_t* uf = builder->uf;
  type_table_t* types = uf->ctx->types;
  ivector_t arguments;
  uint32_t i;

  init_ivector(&arguments, 0);

  for (i = 0; i < uf->fun_model_diseq_entries.size; ++ i) {
    uf_fun_model_diseq_t* entry = uf->fun_model_diseq_entries.data[i];
    type_t tau, lhs_type, rhs_type, lhs_range, rhs_range;
    int32_t lhs_id, rhs_id;
    value_t lhs_value, rhs_value;
    value_t lhs_range_value, rhs_range_value;

    if (!uf_plugin_fun_model_diseq_entry_is_active(uf, entry) ||
        !uf_plugin_get_function_id(uf, entry->lhs, &lhs_id) ||
        !uf_plugin_get_function_id(uf, entry->rhs, &rhs_id) ||
        lhs_id == rhs_id) {
      continue;
    }

    tau = entry->type;
    assert(type_kind(types, tau) == FUNCTION_TYPE);
    assert(!uf_type_is_risky(uf, tau));

    if (!uf_model_builder_make_fresh_domain_values(builder, tau, &arguments)) {
      continue;
    }

    lhs_type = term_type(uf->ctx->terms, entry->lhs);
    rhs_type = term_type(uf->ctx->terms, entry->rhs);
    lhs_range = function_type_range(types, lhs_type);
    rhs_range = function_type_range(types, rhs_type);
    lhs_range_value = null_value;
    rhs_range_value = null_value;
    if (!uf_model_builder_pick_distinct_range_values(builder, lhs_range, rhs_range,
                                                     &lhs_range_value, &rhs_range_value)) {
      continue;
    }

    lhs_value = uf_model_builder_get_function_value(builder, entry->lhs);
    rhs_value = uf_model_builder_get_function_value(builder, entry->rhs);
    if (lhs_value == null_value || rhs_value == null_value) {
      continue;
    }

    lhs_value = vtbl_mk_update(builder->vtbl, lhs_value, arguments.size, arguments.data, lhs_range_value);
    rhs_value = vtbl_mk_update(builder->vtbl, rhs_value, arguments.size, arguments.data, rhs_range_value);
    {
      bool new_record;

      int_hmap2_get(&builder->function_value, lhs_id, lhs_type, &new_record)->val = lhs_value;
      int_hmap2_get(&builder->function_value, rhs_id, rhs_type, &new_record)->val = rhs_value;
    }
  }

  delete_ivector(&arguments);
}

static bool uf_model_values_are_equal(value_table_t* vtbl, value_t lhs, value_t rhs) {
  value_t eq;

  if (lhs == rhs) {
    return true;
  }

  eq = vtbl_eval_eq(vtbl, lhs, rhs);
  return is_true(vtbl, eq);
}

static bool uf_model_builder_pick_value_distinct_from(uf_model_builder_t* builder,
                                                      type_t tau, value_t fixed,
                                                      value_t* result) {
  value_t candidates[2];

  if (!vtbl_make_two_objects(builder->vtbl, tau, candidates)) {
    return false;
  }

  if (!uf_model_values_are_equal(builder->vtbl, fixed, candidates[0])) {
    *result = candidates[0];
    return true;
  }

  assert(!uf_model_values_are_equal(builder->vtbl, fixed, candidates[1]));
  *result = candidates[1];
  return true;
}

static bool uf_model_builder_pick_distinct_range_values(uf_model_builder_t* builder,
                                                        type_t lhs_range, type_t rhs_range,
                                                        value_t* lhs_value,
                                                        value_t* rhs_value) {
  if (*lhs_value != null_value && *rhs_value != null_value) {
    return !uf_model_values_are_equal(builder->vtbl, *lhs_value, *rhs_value);
  }

  if (*lhs_value != null_value) {
    return uf_model_builder_pick_value_distinct_from(builder, rhs_range, *lhs_value, rhs_value);
  }

  if (*rhs_value != null_value) {
    return uf_model_builder_pick_value_distinct_from(builder, lhs_range, *rhs_value, lhs_value);
  }

  *lhs_value = vtbl_make_object(builder->vtbl, lhs_range);
  if (*lhs_value == null_value) {
    return false;
  }
  return uf_model_builder_pick_value_distinct_from(builder, rhs_range, *lhs_value, rhs_value);
}

static bool uf_plugin_term_has_trail_value(uf_plugin_t* uf, term_t t);

static uf_model_app_value_t* uf_model_builder_find_app_value(uf_model_builder_t* builder,
                                                             int32_t function_id, type_t type,
                                                             uint32_t arity, value_t* arguments) {
  uint32_t i, j;

  for (i = 0; i < builder->app_value_reservations.size; ++ i) {
    uf_model_app_value_t* entry = builder->app_value_reservations.data[i];
    if (entry->function_id != function_id || entry->type != type || entry->arity != arity) {
      continue;
    }

    for (j = 0; j < arity; ++ j) {
      if (entry->arguments[j] != arguments[j]) {
        break;
      }
    }
    if (j == arity) {
      return entry;
    }
  }

  return NULL;
}

static value_t uf_model_builder_get_reserved_app_value(uf_model_builder_t* builder,
                                                       int32_t function_id, type_t type, term_t app_term,
                                                       uint32_t arity, value_t* arguments) {
  uf_model_app_value_t* entry;

  if (uf_plugin_term_has_trail_value(builder->uf, app_term)) {
    return uf_model_builder_get_term_value(builder, app_term);
  }

  entry = uf_model_builder_find_app_value(builder, function_id, type, arity, arguments);
  if (entry != NULL) {
    return entry->value;
  }

  return null_value;
}

static void uf_model_builder_reserve_app_value(uf_model_builder_t* builder,
                                               int32_t function_id, type_t type,
                                               uint32_t arity, value_t* arguments, value_t value) {
  uf_model_app_value_t* entry;

  entry = uf_model_builder_find_app_value(builder, function_id, type, arity, arguments);
  if (entry != NULL) {
    return;
  }

  entry = safe_malloc(sizeof(uf_model_app_value_t) + arity * sizeof(value_t));
  entry->function_id = function_id;
  entry->type = type;
  entry->arity = arity;
  entry->value = value;
  memcpy(entry->arguments, arguments, arity * sizeof(value_t));
  pvector_push(&builder->app_value_reservations, entry);
}

static bool uf_plugin_term_has_direct_trail_assignment(uf_plugin_t* uf, term_t t, variable_t v) {
  const eq_graph_t* eq = &uf->eq_graph;
  eq_node_id_t t_id;
  eq_edge_id_t e_id;

  if (!eq_graph_has_term(eq, t)) {
    return false;
  }

  t_id = eq_graph_term_id(eq, t);
  for (e_id = eq->graph.data[t_id]; e_id != eq_edge_null; e_id = eq->edges[e_id].next) {
    const eq_edge_t* edge = &eq->edges[e_id];
    if (edge->reason.type == REASON_IS_IN_TRAIL &&
        edge->reason.data == (uint32_t) v &&
        eq->nodes[edge->v].type == EQ_NODE_VALUE) {
      return true;
    }
  }

  return false;
}

static
void uf_model_builder_apply_search_diff_witnesses(uf_model_builder_t* builder) {
  uf_plugin_t* uf = builder->uf;
  type_table_t* types = uf->ctx->types;
  ivector_t arguments;
  uint32_t i, j;

  init_ivector(&arguments, 0);

  for (i = 0; i < uf->fun_diseq_entries.size; ++ i) {
    uf_fun_diseq_t* entry = uf->fun_diseq_entries.data[i];
    type_t lhs_type, rhs_type, lhs_range, rhs_range;
    int32_t lhs_id, rhs_id;
    value_t lhs_fun_value, rhs_fun_value;
    value_t lhs_app_value, rhs_app_value;

    if (!uf_plugin_fun_diseq_entry_is_active(uf, entry) ||
        !uf_plugin_get_function_id(uf, entry->lhs, &lhs_id) ||
        !uf_plugin_get_function_id(uf, entry->rhs, &rhs_id) ||
        lhs_id == rhs_id) {
      continue;
    }

    assert(type_kind(types, entry->type) == FUNCTION_TYPE);
    assert(uf_type_is_risky(uf, entry->type));
    lhs_type = term_type(uf->ctx->terms, entry->lhs);
    rhs_type = term_type(uf->ctx->terms, entry->rhs);
    lhs_range = function_type_range(types, lhs_type);
    rhs_range = function_type_range(types, rhs_type);

    ivector_reset(&arguments);
    for (j = 0; j < entry->arity; ++ j) {
      value_t arg = uf_model_builder_get_term_value(builder, entry->diff_terms[j]);
      if (arg == null_value) {
        break;
      }
      ivector_push(&arguments, arg);
    }
    if (j < entry->arity) {
      continue;
    }

    lhs_fun_value = uf_model_builder_get_function_value(builder, entry->lhs);
    rhs_fun_value = uf_model_builder_get_function_value(builder, entry->rhs);
    if (lhs_fun_value == null_value || rhs_fun_value == null_value) {
      continue;
    }

    lhs_app_value = uf_model_builder_get_reserved_app_value(builder, lhs_id, lhs_type, entry->lhs_app,
                                                           arguments.size, arguments.data);
    rhs_app_value = uf_model_builder_get_reserved_app_value(builder, rhs_id, rhs_type, entry->rhs_app,
                                                           arguments.size, arguments.data);
    if (!uf_model_builder_pick_distinct_range_values(builder, lhs_range, rhs_range,
                                                     &lhs_app_value, &rhs_app_value)) {
      continue;
    }

    lhs_fun_value = vtbl_mk_update(builder->vtbl, lhs_fun_value, arguments.size, arguments.data, lhs_app_value);
    rhs_fun_value = vtbl_mk_update(builder->vtbl, rhs_fun_value, arguments.size, arguments.data, rhs_app_value);
    uf_model_builder_reserve_app_value(builder, lhs_id, lhs_type, arguments.size, arguments.data, lhs_app_value);
    uf_model_builder_reserve_app_value(builder, rhs_id, rhs_type, arguments.size, arguments.data, rhs_app_value);
    {
      bool new_record;

      int_hmap2_get(&builder->function_value, lhs_id, lhs_type, &new_record)->val = lhs_fun_value;
      int_hmap2_get(&builder->function_value, rhs_id, rhs_type, &new_record)->val = rhs_fun_value;
    }
  }

  delete_ivector(&arguments);
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

  if (!uf_plugin_term_has_trail_value(builder->uf, t)) {
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
void uf_model_builder_reserve_trail_app_values(uf_model_builder_t* builder) {
  uf_plugin_t* uf = builder->uf;
  term_table_t* terms = uf->ctx->terms;
  uint32_t i;

  for (i = 0; i < builder->app_terms.size; ++ i) {
    term_t app_term = builder->app_terms.data[i];
    composite_term_t* app_desc;
    int32_t function_id;
    type_t function_type;
    value_t app_value;
    uint32_t j;

    if (!uf_plugin_term_has_trail_value(uf, app_term)) {
      continue;
    }

    app_desc = app_term_desc(terms, app_term);
    if (!uf_plugin_get_function_id(uf, app_desc->arg[0], &function_id)) {
      continue;  // LCOV_EXCL_LINE - defensive fallback, unreachable on supported inputs
    }

    ivector_reset(&builder->arguments);
    for (j = 1; j < app_desc->arity; ++ j) {
      value_t arg = uf_model_builder_get_term_value(builder, app_desc->arg[j]);
      if (arg == null_value) {
        break;
      }
      ivector_push(&builder->arguments, arg);
    }
    if (j < app_desc->arity) {
      continue;
    }

    app_value = uf_model_builder_get_term_value(builder, app_term);
    if (app_value == null_value) {
      continue;
    }

    function_type = term_type(terms, app_desc->arg[0]);
    uf_model_builder_reserve_app_value(builder, function_id, function_type,
                                       builder->arguments.size, builder->arguments.data, app_value);
  }

  ivector_reset(&builder->arguments);
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
    if (x_term != NULL_TERM &&
        term_kind(terms, x_term) == UNINTERPRETED_TERM &&
        term_type_kind(terms, x_term) == FUNCTION_TYPE) {
      uf_model_builder_remember_function_term(&builder, x_term);
      uf_model_builder_get_function_value(&builder, x_term);
    }
  }

  uf_model_builder_reserve_trail_app_values(&builder);
  uf_model_builder_apply_model_diseqs(&builder);
  uf_model_builder_apply_search_diff_witnesses(&builder);

  for (i = 0; i < trail_elements->size; ++ i) {
    variable_t x = trail_elements->data[i];
    term_t x_term = variable_db_get_term(var_db, x);
    if (x_term != NULL_TERM &&
        term_kind(terms, x_term) == UNINTERPRETED_TERM &&
        term_type_kind(terms, x_term) == FUNCTION_TYPE) {
      value_t x_value = uf_model_builder_get_function_value(&builder, x_term);
      if (x_value != null_value) {
        model_map_term(model, x_term, x_value);
      }
    }
  }

  for (i = 0; i < builder.app_terms.size; ++ i) {
    uf_model_builder_map_term_if_missing(&builder, model, builder.app_terms.data[i]);
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
