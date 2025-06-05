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

#include "mcsat/bool/bool_plugin.h"

#include "mcsat/bool/clause_db.h"
#include "mcsat/bool/cnf.h"
#include "mcsat/bool/bcp_watch_manager.h"

#include "mcsat/tracing.h"

#include "utils/int_array_sort2.h"
#include "mcsat/utils/scope_holder.h"

typedef struct {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

  /** The clause database */
  clause_db_t clause_db;

  /** The CNF converter */
  cnf_t cnf;

  /** Clauses that have been added and need to be processed */
  ivector_t clauses_to_add;

  /** Clauses, these we keep forever */
  ivector_t clauses;

  /** Lemmas, so that we can potentially remove them */
  ivector_t lemmas;

  /** Limit on lemma count before we do compaction */
  uint32_t lemmas_limit;

  /** Clauses to re-check for propagations. */
  ivector_t clauses_to_repropagate;

  /** The watch manager for BCP */
  bcp_watch_manager_t wlm;

  /** Map from variables to clauses that we used to propagate the value */
  ivector_t reason;

  /** List of propagated variables */
  ivector_t propagated;

  /** Size of the propagated vector */
  uint32_t propagated_size;

  /** Next index of the trail to process */
  uint32_t trail_i;

  /** The clause of the latest conflict */
  clause_ref_t conflict;

  /** Scope holder for the int variables */
  scope_holder_t scope;

  /** GC info for clause removal */
  gc_info_t gc_clauses;

  struct {

    /** Score increase per bump (multiplicative) */
    float clause_score_bump_factor;
    /** Decay all scores */
    float clause_score_decay_factor;
    /** Limit for when to scale down */
    float clause_score_limit;

    /** Limit on lemma clauses before we ask for gc */
    uint32_t lemma_limit_init;
    /** Increase of the lemma limit after gc */
    float lemma_limit_factor;

    /** bump factor for bool vars -- geq 1. Higher number means more weightage **/
    uint32_t bool_var_bump_factor;

  } heuristic_params;

  struct {
    statistic_int_t* propagations;
    statistic_int_t* conflicts;
    statistic_int_t* clauses_attached;
    statistic_int_t* clauses_attached_binary;
  } stats;

  /** Exception handler */
  jmp_buf* exception;

} bool_plugin_t;

static
void bool_plugin_stats_init(bool_plugin_t* bp) {
  bp->stats.propagations = statistics_new_int(bp->ctx->stats, "mcsat::bool::propagations");
  bp->stats.conflicts = statistics_new_int(bp->ctx->stats, "mcsat::bool::conflicts");
  bp->stats.clauses_attached = statistics_new_int(bp->ctx->stats, "mcsat::bool::clauses_attached");
  bp->stats.clauses_attached_binary = statistics_new_int(bp->ctx->stats, "mcsat::bool::clauses_attached_binary");
}

static
void bool_plugin_heuristics_init(bool_plugin_t* bp) {
  // Clause scoring
  bp->heuristic_params.clause_score_bump_factor = 1;
  bp->heuristic_params.clause_score_decay_factor = 0.999;
  bp->heuristic_params.clause_score_limit = 1e20;

  // Clause database compact
  bp->heuristic_params.lemma_limit_init = 1000;
  bp->heuristic_params.lemma_limit_factor = 1.05;

  // Bool var scoring
  bp->heuristic_params.bool_var_bump_factor = 20;
}

static
void bool_plugin_construct(plugin_t* plugin, plugin_context_t* ctx) {
  bool_plugin_t* bp = (bool_plugin_t*) plugin;

  bp->ctx = ctx;
  clause_db_construct(&bp->clause_db, ctx->var_db);
  cnf_construct(&bp->cnf, ctx, &bp->clause_db);
  init_ivector(&bp->clauses_to_add, 0);
  init_ivector(&bp->clauses, 0);
  init_ivector(&bp->lemmas, 0);
  init_ivector(&bp->clauses_to_repropagate, 0);
  bcp_watch_manager_construct(&bp->wlm);
  init_ivector(&bp->reason, 0);
  init_ivector(&bp->propagated, 0);

  bp->trail_i = 0;
  bp->propagated_size = 0;

  ctx->request_term_notification_by_kind(ctx, OR_TERM, false);
  ctx->request_term_notification_by_kind(ctx, XOR_TERM, false);
  ctx->request_term_notification_by_kind(ctx, EQ_TERM, false);
  ctx->request_term_notification_by_kind(ctx, ITE_TERM, false);
  ctx->request_term_notification_by_kind(ctx, ITE_SPECIAL, false);

  ctx->request_term_notification_by_type(ctx, BOOL_TYPE);

  ctx->request_decision_calls(ctx, BOOL_TYPE);

  scope_holder_construct(&bp->scope);
  // CONSTRUCTED ON DEMAND: gc_info_construct(&bp->gc_clauses, clause_ref_null);

  bool_plugin_stats_init(bp);
  bool_plugin_heuristics_init(bp);
}

static
void bool_plugin_destruct(plugin_t* plugin) {
  bool_plugin_t* bp = (bool_plugin_t*) plugin;
  clause_db_destruct(&bp->clause_db);
  cnf_destruct(&bp->cnf);
  delete_ivector(&bp->clauses_to_add);
  delete_ivector(&bp->clauses);
  delete_ivector(&bp->lemmas);
  bcp_watch_manager_destruct(&bp->wlm);
  delete_ivector(&bp->clauses_to_repropagate); // BD: fixed memory leak
  delete_ivector(&bp->reason);
  delete_ivector(&bp->propagated);
  scope_holder_destruct(&bp->scope);
  // DESTRUCTED ON DEMAND: gc_info_destruct(&bp->gc_clauses);
}

static
void bool_plugin_new_term_notify(plugin_t* plugin, term_t term, trail_token_t* prop) {
  bool_plugin_t* bp = (bool_plugin_t*) plugin;

  if (ctx_trace_enabled(bp->ctx, "mcsat::new_term")) {
    ctx_trace_printf(bp->ctx, "bool_plugin_new_term_notify: ");
    ctx_trace_term(bp->ctx, term);
  }

  // Ignore non-Boolean terms
  if (term_type_kind(bp->ctx->terms, term) != BOOL_TYPE) {
    assert(is_ite_term(bp->ctx->terms, term));
    return;
  }

  // Convert to CNF
  cnf_convert(&bp->cnf, term, &bp->clauses_to_add);

  // Variable to the watch list manager
  assert(variable_db_has_variable(bp->ctx->var_db, term));
  variable_t term_var = variable_db_get_variable(bp->ctx->var_db, term);
  bcp_watch_manager_new_variable_notify(&bp->wlm, term_var);

  // If constant true, then propagate it's true
  if (term == true_term) {
    prop->add_at_level(prop, term_var, &mcsat_value_true, bp->ctx->trail->decision_level_base);
  }

}

static
void bool_plugin_new_lemma_notify(plugin_t* plugin, ivector_t* lemma, trail_token_t* prop) {
  bool_plugin_t* bp = (bool_plugin_t*) plugin;

  uint32_t i;
  clause_ref_t clause_ref;

  // Convert to CNF
  i = bp->clauses_to_add.size;
  cnf_convert_lemma(&bp->cnf, lemma, &bp->clauses_to_add);

  // Remember the lemma clauses
  for (; i < bp->clauses_to_add.size; ++ i) {
    clause_ref = bp->clauses_to_add.data[i];
    assert(clause_db_is_clause(&bp->clause_db, clause_ref, true));
    ivector_push(&bp->lemmas, clause_ref);
  }
}

/** Comparison based on trail */
static
bool bool_plugin_trail_literal_compare(void *data, mcsat_literal_t l1, mcsat_literal_t l2) {
  const mcsat_trail_t* trail;
  bool l1_has_value, l2_has_value;
  uint32_t l1_level, l2_level;
  bool l1_value, l2_value;

  trail = data;

  //
  // We compare based literals so that true < undef < false, while sorting
  // literals with the same value based on the trail level

  // Literals with no value
  l1_has_value = literal_has_value(l1, trail);
  l2_has_value = literal_has_value(l2, trail);
  if (!l1_has_value && !l2_has_value) {
    // Both have no value, just order by variable
    return literal_get_variable(l1) < literal_get_variable(l2);
  }

  // At least one has a value
  if (!l1_has_value) {
    l2_value = literal_get_value(l2, trail);
    if (l2_value) {
      return false;
    } else {
      return true;
    }
  }
  if (!l2_has_value) {
    l1_value = literal_get_value(l1, trail);
    if (l1_value) {
      return true;
    } else {
      return false;
    }
  }

  // Both literals have a value

  // True literals go up front
  l1_value = literal_get_value(l1, trail);
  l2_value = literal_get_value(l2, trail);
  if (l1_value && !l2_value) {
    return true;
  }
  if (l2_value && !l1_value) {
    return false;
  }

  // Same value, sort by decreasing level for false literals and by
  // increasing level for true literals
  l1_level = literal_get_level(l1, trail);
  l2_level = literal_get_level(l2, trail);
  if (l1_level != l2_level) {
    if (l1_value) {
      return l1_level < l2_level;
    } else {
      return l1_level > l2_level;
    }
  } else {
    return literal_get_variable(l1) < literal_get_variable(l2);
  }
}

/**
 * Add a new clause, normalize and attach to any internal structures. Returns
 * -1 if the clause does not propagate, otherwise returns the level at which
 * the clause propagates.
 */
static
int bool_plugin_attach_clause(bool_plugin_t* bp, clause_ref_t c_ref, trail_token_t* prop) {
  int i, propagation_level;
  mcsat_clause_t* c;

  // Get the clause
  c = clause_db_get_clause(&bp->clause_db, c_ref);

  if (ctx_trace_enabled(bp->ctx, "mcsat::bool::attach")) {
    ctx_trace_printf(bp->ctx, "bool_plugin_attach_clause: ");
    clause_db_print_clause(&bp->clause_db, c_ref, ctx_trace_out(bp->ctx));
    ctx_trace_printf(bp->ctx, "\n");
  }

  // Sort the clause based on trail
  int_array_sort2(c->literals, c->size, (void*) bp->ctx->trail, bool_plugin_trail_literal_compare);

  if (ctx_trace_enabled(bp->ctx, "mcsat::bool::attach")) {
    ctx_trace_printf(bp->ctx, "sorted: ");
    clause_db_print_clause(&bp->clause_db, c_ref, ctx_trace_out(bp->ctx));
    ctx_trace_printf(bp->ctx, "\n");
  }

  // Reduce the size of the clause by removing base level false literals.
  // These literals are at the end (see trail_compare in the sort)
  i = c->size - 1;
  while (i >= 0) {
    if (literal_has_value_at_base(c->literals[i], bp->ctx->trail) && literal_is_false(c->literals[i], bp->ctx->trail)) {
      c->size --;
      i --;
    } else {
      break;
    }
  }

  if (c->size == 0) {
    // Empty clause derived, we have a conflict at base level
    prop->conflict(prop);
    return -1;
  }

  // If the first literal at base, it must be true at base making the clause
  // irellevant
  if (literal_has_value_at_base(c->literals[0], bp->ctx->trail)) {
    assert(literal_is_true(c->literals[0], bp->ctx->trail));
    return -1;
  }

  // If it propagates, add it to the delayed propagation list (even empty clauses)
  if (c->size == 1) {
    propagation_level = bp->ctx->trail->decision_level_base;
  } else if (literal_is_false(c->literals[1], bp->ctx->trail)) {
    propagation_level = trail_get_level(bp->ctx->trail, literal_get_variable(c->literals[1]));
  } else {
    propagation_level = -1;
  }

  // Attach the two first literals
  // ~c[0], ~c[1], i.e. when c[0] or c[1] become false we do something
  if (c->size == 2) {
    bcp_watch_manager_add_to_watch(&bp->wlm, literal_negate(c->literals[0]), c_ref, true, c->literals[1]);
    bcp_watch_manager_add_to_watch(&bp->wlm, literal_negate(c->literals[1]), c_ref, true, c->literals[0]);
    (*bp->stats.clauses_attached_binary) ++;
  } else if (c->size > 2) {
    bcp_watch_manager_add_to_watch(&bp->wlm, literal_negate(c->literals[0]), c_ref, false, c->literals[1]);
    bcp_watch_manager_add_to_watch(&bp->wlm, literal_negate(c->literals[1]), c_ref, false, c->literals[0]);
    (*bp->stats.clauses_attached) ++;
  }

  if (ctx_trace_enabled(bp->ctx, "mcsat::bool::attach")) {
    ctx_trace_printf(bp->ctx, "propagates at level %d\n", propagation_level);
  }

  // Return the level at which the clause propagates
  return propagation_level;
}

static
void bool_plugin_decay_clause_scores(bool_plugin_t* bp) {
  bp->heuristic_params.clause_score_bump_factor *= (1 / bp->heuristic_params.clause_score_decay_factor);
}

static
void bool_plugin_rescale_clause_scores(bool_plugin_t* bp) {
  uint32_t i;
  clause_ref_t clause;
  mcsat_clause_tag_t* tag;

  for (i = 0; i < bp->lemmas.size; ++ i) {
    clause = bp->lemmas.data[i];
    tag = clause_db_get_tag(&bp->clause_db, clause);
    assert(tag->type == CLAUSE_LEMMA);
    tag->score /= bp->heuristic_params.clause_score_limit;
  }

  bp->heuristic_params.clause_score_bump_factor /= bp->heuristic_params.clause_score_limit;
}

static
void bool_plugin_bump_clause(bool_plugin_t* bp, const mcsat_clause_t* clause) {
  mcsat_clause_tag_t* tag;

  tag = clause_get_tag(clause);
  if (tag->type == CLAUSE_LEMMA) {
    // Bump
    tag->score += bp->heuristic_params.clause_score_bump_factor;
    // If over the limit, normalize
    if (tag->score > bp->heuristic_params.clause_score_limit) {
      bool_plugin_rescale_clause_scores(bp);
    }
  }
}

static inline
void bool_plugin_report_conflict(bool_plugin_t* bp, trail_token_t* prop, clause_ref_t c) {
  mcsat_tagged_clause_t* clause;

  // Bump the conflict clause
  clause = clause_db_get_tagged_clause(&bp->clause_db, c);
  if (clause->tag.type == CLAUSE_LEMMA) {
    bool_plugin_bump_clause(bp, &clause->clause);
  }

  prop->conflict(prop);
  bp->conflict = c;

  (*bp->stats.conflicts) ++;
}

static inline
void bool_plugin_set_reason_ref(bool_plugin_t* bp, variable_t x, clause_ref_t reason_ref) {
  assert(x < bp->reason.size);
  assert(variable_db_is_variable(bp->ctx->var_db, x, true));
  assert(reason_ref == clause_ref_null || clause_db_is_clause(&bp->clause_db, reason_ref, true));

  bp->reason.data[x] = reason_ref;
}

/**
 * Propagate the literal and remember any needed information.
 */
static inline
void bool_plugin_propagate_literal(bool_plugin_t* bp, mcsat_literal_t l, trail_token_t* prop, clause_ref_t cref) {
  variable_t x;

  assert(cref != clause_ref_null);
  assert(!literal_has_value(l, bp->ctx->trail));

  (*bp->stats.propagations) ++;

  literal_set_value(l, prop);
  ivector_push(&bp->propagated, literal_get_variable(l));

  x = literal_get_variable(l);
  while (x >= bp->reason.size) {
    ivector_push(&bp->reason, clause_ref_null);
  }
  assert(bp->reason.data[x] == clause_ref_null);
  bool_plugin_set_reason_ref(bp, x, cref);
}

/**
 * Get the reason of why x is set to this value.
 */
static inline
clause_ref_t bool_plugin_get_reason_ref(bool_plugin_t* bp, variable_t x) {
  clause_ref_t reason_ref;

  assert(x < bp->reason.size);
  assert(variable_db_is_variable(bp->ctx->var_db, x, true));

  reason_ref = bp->reason.data[x];
  assert(clause_db_is_clause(&bp->clause_db, reason_ref, true));

  return reason_ref;
}

/**
 * Get the reason of why x is set to this value.
 */
static inline
const mcsat_clause_t* bool_plugin_get_reason(bool_plugin_t* bp, variable_t x) {
  return clause_db_get_clause(&bp->clause_db, bool_plugin_get_reason_ref(bp, x));
}

/**
 * Add any new clauses that were added in the meantime.
 */
static
void bool_plugin_add_new_clauses(bool_plugin_t* bp, trail_token_t* prop) {
  uint32_t i;
  int propagation_level;
  clause_ref_t c_ref;
  mcsat_clause_t* c;

  // Attach all the clauses
  for (i = 0; i < bp->clauses_to_add.size; ++ i) {
    // Get the clause and attach it
    c_ref = bp->clauses_to_add.data[i];
    propagation_level = bool_plugin_attach_clause(bp, c_ref, prop);

    if (propagation_level >= 0) {
      c = clause_db_get_clause(&bp->clause_db, c_ref);
      // If the clause propagates at current level, just propagate it
      assert(propagation_level <= bp->ctx->trail->decision_level);
      if (propagation_level == bp->ctx->trail->decision_level) {
        bool_plugin_propagate_literal(bp, c->literals[0], prop, c_ref);
      } else {
        // Propagates at lower level (this happens with assumptions)
        // we don't currently repropagate since we don't need to
        ivector_push(&bp->clauses_to_repropagate, c_ref);
        bool_plugin_propagate_literal(bp, c->literals[0], prop, c_ref);
      }
    }
  }

  // Done with the clause, reset
  ivector_reset(&bp->clauses_to_add);
}

/**
 * Propagates the trail with BCP. When done, either the trail is fully
 * propagated, or the trail is in an inconsistent state.
 */
static
void bool_plugin_propagate(plugin_t* plugin, trail_token_t* prop) {
  uint32_t k;
  bool_plugin_t* bp;
  const mcsat_trail_t* trail;
  variable_t var;
  bool var_value;
  mcsat_literal_t var_lit, var_lit_neg, lit, lit_neg;
  bcp_remove_iterator_t it;
  bcp_watcher_t* it_w;
  mcsat_clause_t* clause;
  bool watch_found;

  bp = (bool_plugin_t*) plugin;
  trail = bp->ctx->trail;

  // Add any new clauses
  bool_plugin_add_new_clauses(bp, prop);

  if (ctx_trace_enabled(bp->ctx, "bool::propagate")) {
    ctx_trace_printf(bp->ctx, "trail:\n");
    trail_print(bp->ctx->trail, bp->ctx->tracer->file);
  }

  // Propagate
  for(; trail_is_consistent(trail) && bp->trail_i < trail_size(trail); ++ bp->trail_i) {

    // Current trail element
    var = trail_at(bp->ctx->trail, bp->trail_i);;

    // Only for Boolean variables
    if (variable_db_is_boolean(bp->ctx->var_db, var)) {
      assert(trail_has_value(trail, var));
      var_value = trail_get_value(trail, var)->b;

      if (ctx_trace_enabled(bp->ctx, "bool::propagate")) {
        ctx_trace_printf(bp->ctx, "checking propagation due to ");
        variable_db_print_variable(bp->ctx->var_db, var, bp->ctx->tracer->file);
        ctx_trace_printf(bp->ctx, "\n");
      }

      // The literal we're propagating
      var_lit = literal_construct(var, !var_value);
      var_lit_neg = literal_negate(var_lit);

      // Get the watch-list
      bcp_remove_iterator_construct(&it, &bp->wlm, var_lit);

      while (trail_is_consistent(trail) && !bcp_remove_iterator_done(&it)) {
        it_w = bcp_remove_iterator_get_watcher(&it);

        // Check the blocker
        if(literal_is_true(it_w->blocker, trail)) {
          bcp_remove_iterator_next_and_keep(&it);
          continue;
        }

        // The binary clause case
        if (it_w->is_binary) {
          // Check the blocker
          if (literal_is_false(it_w->blocker, trail)) {
            bool_plugin_report_conflict(bp, prop, it_w->cref);
          } else {
            bool_plugin_propagate_literal(bp, it_w->blocker, prop, it_w->cref);
          }
          bcp_remove_iterator_next_and_keep(&it);
          continue;
        }

        // Get the clause
        clause = clause_db_get_clause(&bp->clause_db, it_w->cref);

        if (ctx_trace_enabled(bp->ctx, "bool::propagate")) {
          ctx_trace_printf(bp->ctx, "bool propagate on: %d ", it_w->cref);
          clause_print(clause, bp->ctx->var_db, bp->ctx->tracer->file);
          ctx_trace_printf(bp->ctx, "\n");
        }

        // Put the literal to [1] so that [0] is the propagation one
        if (clause->literals[0] == var_lit_neg) {
          clause_swap_literals(clause, 0, 1);
        }
        assert(literal_get_variable(clause->literals[1]) == var);

        // If [0] is true, the clause is already satisfied
        if (literal_is_true(clause->literals[0], trail)) {
          it_w->blocker = clause->literals[0];
          bcp_remove_iterator_next_and_keep(&it);

          if (ctx_trace_enabled(bp->ctx, "bool::propagate")) {
            ctx_trace_printf(bp->ctx, "clause true due to blocker\n");
          }
          continue;
        }

        // Find a new watch
        watch_found = false;
        for (k = 2; k < clause->size; ++ k) {
          if (!literal_is_false(clause->literals[k], trail)) {
            // Put it in place and add to watch list if not true at base level
            clause_swap_literals(clause, 1, k);
            lit = clause->literals[1];
            lit_neg = literal_negate(lit);
            bcp_watch_manager_add_to_watch(&bp->wlm, lit_neg, it_w->cref, false, clause->literals[0]);
            // Found the watch, done
            watch_found = true;
            break;
          } else {
            // Literal is false, see if at level 0, to push to back
            // TODO: We can check == clause level, but it's not clear
            // this optimization has any merit
            if (literal_get_level(clause->literals[k], trail) == 0) {
              clause->size --;
              clause_swap_literals(clause, k, clause->size);
              -- k;
            }
          }
        }

        if (!watch_found) {
          if (ctx_trace_enabled(bp->ctx, "bool::propagate")) {
            ctx_trace_printf(bp->ctx, "no watch found\n");
          }
          // No watch, we're ready to propagate
          lit = clause->literals[0];
          if (literal_has_value(lit, trail)) {
            // We've checked that it's not true, so it must be false
            assert(literal_is_false(lit, trail));
            bool_plugin_report_conflict(bp, prop, it_w->cref);
          } else {
            bool_plugin_propagate_literal(bp, lit, prop, it_w->cref);
          }
          // Keep the watch
          bcp_remove_iterator_next_and_keep(&it);
        } else {
          if (ctx_trace_enabled(bp->ctx, "bool::propagate")) {
            ctx_trace_printf(bp->ctx, "new watch found: %d ", it_w->cref);
            clause_print(clause, bp->ctx->var_db, bp->ctx->tracer->file);
            ctx_trace_printf(bp->ctx, "\n");
          }
          bcp_remove_iterator_next_and_remove(&it);
        }
      }

      // Done, destruct the iterator
      bcp_remove_iterator_destruct(&it);
    }
  }
}

static
void bool_plugin_decide(plugin_t* plugin, variable_t x, trail_token_t* decide, bool must) {
  bool_plugin_t* bp = (bool_plugin_t*) plugin;
  mcsat_literal_t literal;

  assert(!trail_has_value(bp->ctx->trail, x));

  if (trail_has_cached_value(bp->ctx->trail, x)) {
    // Use the cached value if exists
    literal = literal_construct(x, !trail_get_cached_value(bp->ctx->trail, x)->b);
  } else {
    // Go negative
    literal = literal_construct(x, true);
  }

  literal_set_value(literal, decide);
}

void bool_plugin_get_conflict(plugin_t* plugin, ivector_t* conflict) {
  bool_plugin_t* bp = (bool_plugin_t*) plugin;

  uint32_t i;
  mcsat_literal_t l_i;
  variable_t var_i;
  term_t term_i;
  mcsat_clause_t* conflict_clause;

  assert(bp->conflict != clause_ref_null);

  // Get the clause in conflict
  conflict_clause = clause_db_get_clause(&bp->clause_db, bp->conflict);

  // Add the negated literals to the conflict
  // (or l1 ... ln) is the same as
  // (and ~l1 ... ~ln) => false
  for (i = 0; i < conflict_clause->size; ++ i) {
    l_i = conflict_clause->literals[i];
    var_i = literal_get_variable(l_i);
    term_i = variable_db_get_term(bp->ctx->var_db, var_i);
    if (literal_is_negated(l_i)) {
      term_i = opposite_term(term_i);
    }
    ivector_push(conflict, opposite_term(term_i));
  }
}

term_t bool_plugin_explain_propagation(plugin_t* plugin, variable_t var, ivector_t* reasons) {
  bool_plugin_t* bp = (bool_plugin_t*) plugin;

  uint32_t i;
  mcsat_literal_t l_i;
  variable_t x_i;
  term_t t_i;
  bool var_value;
  const mcsat_clause_t* clause;

  // Add the other literals from the clause as explanations
  assert(trail_has_value(bp->ctx->trail, var));
  var_value = trail_get_value(bp->ctx->trail, var)->b;
  clause = bool_plugin_get_reason(bp, var);
  assert(clause->size == 2 || literal_get_variable(clause->literals[0]) == var);
  // Start from 0 to cover the binary clause case
  for (i = 0; i < clause->size; ++ i) {
    l_i = clause->literals[i];
    x_i = literal_get_variable(l_i);
    if (x_i == var) {
      continue;
    }

    t_i = variable_db_get_term(bp->ctx->var_db, x_i);
    if (literal_is_negated(l_i)) {
      t_i = opposite_term(t_i);
    }
    ivector_push(reasons, opposite_term(t_i));

    // Bump the reason variable -- give more weightage to boolean reasons
    bp->ctx->bump_variable_n(bp->ctx, x_i,
			     bp->heuristic_params.bool_var_bump_factor);
  }

  // Bump the clause as useful
  bool_plugin_bump_clause(bp, clause);

  return bool2term(var_value);
}

bool bool_plugin_explain_evaluation(plugin_t* plugin, term_t t, int_mset_t* vars, mcsat_value_t* value) {

  bool_plugin_t* bp = (bool_plugin_t*) plugin;
  const variable_db_t* var_db = bp->ctx->var_db;
  const mcsat_trail_t* trail = bp->ctx->trail;

  // Boolean plugin only explains evaluation of assigned false literals
  term_t t_unsigned = unsigned_term(t);
  variable_t t_var = variable_db_get_variable_if_exists(var_db, t_unsigned);
  if (t_var == variable_null) {
    // trying one step further to evaluate equality terms
    if (term_kind(bp->ctx->terms, t_unsigned) == EQ_TERM) {
      composite_term_t* t_desc = eq_term_desc(bp->ctx->terms, t);
      term_t t1 = t_desc->arg[0];
      term_t t2 = t_desc->arg[1];
      assert(t1 != NULL_TERM);
      assert(t2 != NULL_TERM);
      variable_t t1_var = variable_db_get_variable_if_exists(var_db, t1);
      variable_t t2_var = variable_db_get_variable_if_exists(var_db, t2);
      if (t1_var != variable_null && t2_var != variable_null) {
	if (trail_has_value(trail, t1_var) && trail_has_value(trail, t2_var)) {
	  bool negated = is_neg_term(t);
	  const mcsat_value_t* t1_var_value = trail_get_value(trail, t1_var);
	  const mcsat_value_t* t2_var_value = trail_get_value(trail, t2_var);
	  if (negated) {
	    return (t1_var_value->b == t2_var_value->b) != value->b;
	  } else {
	    return (t1_var_value->b == t2_var_value->b) == value->b;
	  }
	}
      }
    }
    // couldn't evaluate
    return false;
  }

  int_mset_add(vars, t_var);
  if (trail_has_value(trail, t_var)) {
    bool negated = is_neg_term(t);
    const mcsat_value_t* t_var_value = trail_get_value(trail, t_var);
    if (negated) {
      return t_var_value->b != value->b;
    } else {
      return t_var_value->b == value->b;
    }
  }

  return false;
}

void bool_plugin_push(plugin_t* plugin) {
  bool_plugin_t* bp = (bool_plugin_t*) plugin;

  bp->propagated_size = bp->propagated.size;

  scope_holder_push(&bp->scope,
      &bp->trail_i,
      &bp->propagated_size,
      NULL);
}

void bool_plugin_pop(plugin_t* plugin) {
  bool_plugin_t* bp = (bool_plugin_t*) plugin;

  variable_t propagated_var;

  scope_holder_pop(&bp->scope,
      &bp->trail_i,
      &bp->propagated_size,
      NULL);

  assert(bp->propagated.size >= bp->propagated_size);
  while (bp->propagated.size > bp->propagated_size) {
    propagated_var = ivector_pop2(&bp->propagated);
    bool_plugin_set_reason_ref(bp, propagated_var, clause_ref_null);
  }
}

/**
 * Comparison based on clause value. Better go front.
 */
static
bool bool_plugin_clause_compare_for_removal(void *data, clause_ref_t c1, clause_ref_t c2) {

  clause_db_t* clause_db = (clause_db_t*) data;
  mcsat_clause_tag_t *c1_tag, *c2_tag;

  c1_tag = clause_db_get_tag(clause_db, c1);
  c2_tag = clause_db_get_tag(clause_db, c2);

  assert(c1_tag->type == CLAUSE_LEMMA);
  assert(c2_tag->type == CLAUSE_LEMMA);

  return c1_tag->score > c2_tag->score;
}

void bool_plugin_gc_mark(plugin_t* plugin, gc_info_t* gc_vars) {

  bool_plugin_t* bp = (bool_plugin_t*) plugin;
  clause_db_t* db = &bp->clause_db;
  const mcsat_trail_t* trail = bp->ctx->trail;

  uint32_t i;
  float act_threshold;
  variable_t var;
  clause_ref_t clause_ref;
  mcsat_clause_t* c;
  mcsat_clause_tag_t *c_tag;

  if (gc_vars->level == 0) {

    // Construct the gc info (destructed in collect())
    gc_info_construct(&bp->gc_clauses, clause_ref_null, false);

    // Sort the lemmas based on scores
    int_array_sort2(bp->lemmas.data, bp->lemmas.size, (void*) db, bool_plugin_clause_compare_for_removal);

    // avg activity score
    act_threshold = bp->heuristic_params.clause_score_bump_factor / bp->lemmas.size;

    // Mark all the variables in half of lemmas as used
    for (i = 0; i < bp->lemmas.size / 2; ++ i) {
      clause_ref = bp->lemmas.data[i];
      assert(clause_db_is_clause(db, clause_ref, true));
      c_tag = clause_db_get_tag(db, clause_ref);
      if (c_tag->score <= act_threshold) {
        // consider clauses with score higher than the avg activity score
        // since the clauses are sorted according to their scores, we break here
        break;
      }
      gc_info_mark(&bp->gc_clauses, clause_ref);
    }

    // We also keep the clauses of any propagated literals
    for (i = 0; i < bp->propagated.size; ++ i) {
      var = bp->propagated.data[i];
      clause_ref = bool_plugin_get_reason_ref(bp, var);
      gc_info_mark(&bp->gc_clauses, clause_ref);
    }

    // keep binary clauses
    for (i = 0; i < bp->lemmas.size; ++ i) {
      clause_ref = bp->lemmas.data[i];
      assert(clause_db_is_clause(db, clause_ref, true));
      c = clause_db_get_clause(&bp->clause_db, clause_ref);
      if (c->size == 2) {
        if (!literal_is_true(c->literals[0], trail) &&
            !literal_is_true(c->literals[1], trail)) {
          gc_info_mark(&bp->gc_clauses, clause_ref);
        }
      }
    }
  }

  // Mark all the CNF definitions
  cnf_gc_mark(&bp->cnf, &bp->gc_clauses, gc_vars);

  // Mark all variables through the clause database
  clause_db_gc_mark(db, &bp->gc_clauses, gc_vars);
}

void bool_plugin_gc_sweep(plugin_t* plugin, const gc_info_t* gc_vars) {

  bool_plugin_t* bp = (bool_plugin_t*) plugin;

  uint32_t i;
  variable_t var;
  int_mset_t vars_undefined;
  clause_ref_t clause, clause_reloc;

  // Clauses
  int_mset_construct(&vars_undefined, variable_null);
  clause_db_gc_sweep(&bp->clause_db, &bp->gc_clauses, &vars_undefined);
  cnf_gc_sweep(&bp->cnf, &bp->gc_clauses, &vars_undefined);
  int_mset_destruct(&vars_undefined);

  // Vectors of clauses
  gc_info_sweep_ivector(&bp->gc_clauses, &bp->clauses_to_add);
  gc_info_sweep_ivector(&bp->gc_clauses, &bp->clauses);
  gc_info_sweep_ivector(&bp->gc_clauses, &bp->lemmas);
  gc_info_sweep_ivector(&bp->gc_clauses, &bp->clauses_to_repropagate);

  assert(clause_db_is_clause_vector(&bp->clause_db, &bp->clauses_to_add, true));
  assert(clause_db_is_clause_vector(&bp->clause_db, &bp->clauses, true));
  assert(clause_db_is_clause_vector(&bp->clause_db, &bp->lemmas, true));
  assert(clause_db_is_clause_vector(&bp->clause_db, &bp->clauses_to_repropagate, true));

  // Watch manager
  bcp_watch_manager_sweep(&bp->wlm, &bp->gc_clauses, gc_vars);

  // Reasons
  assert(gc_vars->is_id);
  for (i = 0; i < bp->propagated.size; ++ i) {

    // The variable itself
    var = bp->propagated.data[i];
    assert(bp->reason.data[var] != clause_ref_null);

    // Variable might be gone, just remove the reason
    if (gc_info_get_reloc(gc_vars, var) == variable_null) {
      bool_plugin_set_reason_ref(bp, var, clause_ref_null);
    } else {
      // The clausal reason for var propagation
      clause = bp->reason.data[var]; // Getting directly, not a valud reason anymore
      clause_reloc = gc_info_get_reloc(&bp->gc_clauses, clause);
      assert(clause_reloc != clause_ref_null);
      bool_plugin_set_reason_ref(bp, var, clause_reloc);
    }
  }

  // Propagated vector
  gc_info_sweep_ivector(gc_vars, &bp->propagated);

  // Destroy the gc info (constructed in mark())
  gc_info_destruct(&bp->gc_clauses);
}

static
void bool_plugin_remove_stale_clauses(bool_plugin_t* bp) {
  uint32_t i, to_keep;
  clause_ref_t clause_ref;
  clause_db_t* db = &bp->clause_db;
  uint32_t base_level = bp->ctx->trail->decision_level_base;
  for (i = 0, to_keep = 0; i < bp->lemmas.size; ++ i) {
    clause_ref = bp->lemmas.data[i];
    assert(clause_db_is_clause(db, clause_ref, true));
    // Keep the lemma if it's at the right level
    if (clause_db_get_tag(db, clause_ref)->level <= base_level) {
      bp->lemmas.data[to_keep++] = clause_ref;
    }
  }
  ivector_shrink(&bp->lemmas, to_keep);
}

static
void bool_plugin_event_notify(plugin_t* plugin, plugin_notify_kind_t kind) {
  bool_plugin_t* bp = (bool_plugin_t*) plugin;

  switch (kind) {
  case MCSAT_SOLVER_START:
    // Re-initialize the heuristics
    bp->lemmas_limit = bp->lemmas.size + bp->heuristic_params.lemma_limit_init;
    break;
  case MCSAT_SOLVER_RESTART:
    // Check if clause compaction needed
    if (bp->lemmas.size > bp->lemmas_limit) {
      bp->ctx->request_gc(bp->ctx);
      bp->lemmas_limit *= bp->heuristic_params.lemma_limit_factor;
    }
    break;
  case MCSAT_SOLVER_CONFLICT:
    // Decay the scores each conflict
    bool_plugin_decay_clause_scores(bp);
    break;
  case MCSAT_SOLVER_POP:
    // Remove all learnt clauses above base level, regular clauses will be
    // removed trhough garbage collection
    bool_plugin_remove_stale_clauses(bp);
    break;
  default:
    assert(false);
  }
}

static
void bool_plugin_set_exception_handler(plugin_t* plugin, jmp_buf* handler) {
  bool_plugin_t* bp = (bool_plugin_t*) plugin;
  bp->exception = handler;
}

static
void bool_plugin_decide_assignment(plugin_t* plugin, variable_t x, const mcsat_value_t* value, trail_token_t* decide) {
  // Nothing to do here apart from setting the value
  decide->add(decide, x, value);
}


plugin_t* bool_plugin_allocator(void) {
  bool_plugin_t* plugin = safe_malloc(sizeof(bool_plugin_t));
  plugin_construct((plugin_t*) plugin);
  plugin->plugin_interface.construct             = bool_plugin_construct;
  plugin->plugin_interface.destruct              = bool_plugin_destruct;
  plugin->plugin_interface.new_term_notify       = bool_plugin_new_term_notify;
  plugin->plugin_interface.new_lemma_notify      = bool_plugin_new_lemma_notify;
  plugin->plugin_interface.event_notify          = bool_plugin_event_notify;
  plugin->plugin_interface.propagate             = bool_plugin_propagate;
  plugin->plugin_interface.decide                = bool_plugin_decide;
  plugin->plugin_interface.decide_assignment     = bool_plugin_decide_assignment;
  plugin->plugin_interface.get_conflict          = bool_plugin_get_conflict;
  plugin->plugin_interface.explain_propagation   = bool_plugin_explain_propagation;
  plugin->plugin_interface.explain_evaluation    = bool_plugin_explain_evaluation;
  plugin->plugin_interface.push                  = bool_plugin_push;
  plugin->plugin_interface.pop                   = bool_plugin_pop;
  plugin->plugin_interface.gc_mark               = bool_plugin_gc_mark;
  plugin->plugin_interface.gc_sweep              = bool_plugin_gc_sweep;
  plugin->plugin_interface.set_exception_handler = bool_plugin_set_exception_handler;

  return (plugin_t*) plugin;
}
