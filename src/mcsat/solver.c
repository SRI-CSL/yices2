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

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include "mcsat/solver.h"

#include "context/context.h"
#include "model/models.h"
#include "model/concrete_values.h"
#include "model/model_queries.h"
#include "io/concrete_value_printer.h"

#include "mcsat/variable_db.h"
#include "mcsat/variable_queue.h"
#include "mcsat/trail.h"
#include "mcsat/conflict.h"
#include "mcsat/plugin.h"
#include "mcsat/tracing.h"

#include "utils/int_queues.h"
#include "utils/bitvectors.h"
#include "utils/int_hash_sets.h"

#include "mcsat/bool/bool_plugin.h"
#include "mcsat/ite/ite_plugin.h"
#include "mcsat/nra/nra_plugin.h"
#include "mcsat/uf/uf_plugin.h"
#include "mcsat/bv/bv_plugin.h"
#include "mcsat/ff/ff_plugin.h"

#include "mcsat/preprocessor.h"

#include "mcsat/utils/statistics.h"

#include "utils/dprng.h"
#include "model/model_queries.h"
#include "io/model_printer.h"

#include "yices.h"
#include <inttypes.h>
#include <math.h>

/**
 * Notification of new variables for the main solver.
 */
typedef struct solver_new_variable_notify_s {
  void (*new_variable) (struct solver_new_variable_notify_s* self, variable_t x);
  mcsat_solver_t* mcsat;
} solver_new_variable_notify_t;

/**
 * Context of each plugin encapsulates its essential information, including
 * the solver itself, its index in the solver and its name (for debugging
 * purposes).
 */
typedef struct mcsat_plugin_context_s {
  /** The regular plugin context */
  plugin_context_t ctx;
  /** The solver reference */
  mcsat_solver_t* mcsat;
  /** The name of the plugin */
  const char* plugin_name;
} mcsat_plugin_context_t;

/**
 * The token is passed to plugins for trail operations (propagation and
 * decisions) and encapsulates additional information for debugging purposes.
 */
typedef struct {
  /** The token interface */
  trail_token_t token_interface;
  /** Link to the context */
  mcsat_plugin_context_t* ctx;
  /** If this is a decision token, this is the suggested variable to decide */
  variable_t x;
  /** How many times has the token been used */
  uint32_t used;
} plugin_trail_token_t;

/** Type of lemma weight for adding to restart counter */
typedef enum {
  /** Just add 1 */
  LEMMA_WEIGHT_UNIT,
  /** Add the size of the lemma */
  LEMMA_WEIGHT_SIZE,
  /** Add the glue of the lemma */
  LEMMA_WEIGHT_GLUE
} lemma_weight_type_t;

#define MCSAT_MAX_PLUGINS 10

typedef struct {
  /** Main evaluation method */
  bool (*evaluates_at) (const mcsat_evaluator_interface_t* data, term_t t, int_mset_t* vars, mcsat_value_t* value, uint32_t trail_size);
  /** The solver */
  mcsat_solver_t* solver;
} mcsat_evaluator_t;

struct mcsat_solver_s {

  /** Context of the solver */
  const context_t* ctx;

  /** Flag to stop the search */
  bool stop_search;

  /** Exception handler */
  jmp_buf* exception;

  /** Term manager for everyone to use */
  term_manager_t tm;

  /** Input types are are from this table */
  type_table_t* types;

  /** Input terms are from this table */
  term_table_t* terms;

  /** Size of the input table at entry to solve() */
  uint32_t terms_size_on_solver_entry;

  /** The status (real status is in trail, this is for context integration) */
  smt_status_t status;

  /** Number of inconsistent push calls */
  uint32_t inconsistent_push_calls;

  /** Notifications for new variables */
  solver_new_variable_notify_t var_db_notify;

  /** Variable database */
  variable_db_t* var_db;

  /** List of assertions (positive variables) asserted to true. */
  ivector_t assertion_vars;

  /**
   * List of assertions (terms) as sent to the solver through the API. These
   * terms have not been pre-processed.
   */
  ivector_t assertion_terms_original;

  /** Temp assertion vector while preprocessing */
  ivector_t assertions_tmp;

  /** The trail */
  mcsat_trail_t* trail;

  /** Mark when adding an assertion */
  bool registration_is_assertion;

  /** Queue for registering new variables */
  int_queue_t registration_queue;

  /** Has a term been registered already */
  int_hset_t registration_cache;

  /** Array of individual plugins, and the additional info */
  struct {
    plugin_t* plugin;
    mcsat_plugin_context_t* plugin_ctx;
    char* plugin_name;
  } plugins[MCSAT_MAX_PLUGINS];

  /** The evaluator */
  mcsat_evaluator_t evaluator;

  /** The preprocessor */
  preprocessor_t preprocessor;

  /**
   * Array of owners for each term kind. If there are more than one, they
   * continue at indices mod NUM_TERM_KINDS.
   */
  uint32_t kind_owners[NUM_TERM_KINDS * MCSAT_MAX_PLUGINS];

  /**
   * Which of the kinds are 'internal': not for external use.
   */
  int_hset_t internal_kinds;

  /**
   * Array of owners for each type. If there are more than one, they
   * continue at indices mod NUM_TYPE_KINDS.
   */
  uint32_t type_owners[NUM_TYPE_KINDS * MCSAT_MAX_PLUGINS];

  /**
   * Array of decision makers for each type. There can be only one.
   */
  uint32_t decision_makers[NUM_TYPE_KINDS];

  /** Plugin the reported a conflict */
  mcsat_plugin_context_t* plugin_in_conflict;

  /** Variable that is in conflict (if found during assumption decisions) */
  variable_t variable_in_conflict;

  /** Lemmas reported by plugins  */
  ivector_t plugin_lemmas;

  /** Lemmas defining a variable. Will be re-asserted on pop if the variable is still there */
  ivector_t plugin_definition_lemmas;

  /** Variables of definition lemmas (as terms) */
  ivector_t plugin_definition_vars;

  /** Last processed definition lemma */
  uint32_t plugin_definition_lemmas_i;

  /** Number of plugins */
  uint32_t plugins_count;

  /** Variable to decide on first */
  ivector_t top_decision_vars;

  /** Variables hinted by the plugins to decide next */
  int_queue_t hinted_decision_vars;

  /** The queue for variable decisions */
  var_queue_t var_queue;

  /** All pending requests */
  struct {
    bool restart;
    bool gc_calls;
    bool recache;
  } pending_requests_all;

  /** Any pending requests */
  bool pending_requests;

  /** Assumption variables */
  ivector_t assumption_vars;

  /** Index of the assumption to process next */
  uint32_t assumption_i;

  /** Level at which last assumption has been decided (-1 if not yet) */
  int32_t assumptions_decided_level;

  /** Model used for assumptions solving */
  model_t* assumptions_model;

  /** Interpolant */
  term_t interpolant;

  /** Statistics */
  statistics_t stats;

  struct {
    // Assertions added
    statistic_int_t* assertions;
    // Lemmas added
    statistic_int_t* lemmas;
    // Decisions performed
    statistic_int_t* decisions;
    // Restarts performed
    statistic_int_t* restarts;
    // Conflicts handled
    statistic_int_t* conflicts;
    // Average conflict size
    statistic_avg_t* avg_conflict_size;
    // GC calls
    statistic_int_t* gc_calls;
    // Recache calls
    statistic_int_t* recaches;
  } solver_stats;

  struct {
    // Restart interval (used as multiplier in luby sequence)
    uint32_t restart_interval;
    // Type of weight to use for restart counter
    lemma_weight_type_t lemma_restart_weight_type;
    // recache interval
    uint32_t recache_interval;
    // Random decision frequency
    double random_decision_freq;
    // Random decision seed
    double random_decision_seed;
  } heuristic_params;

  /** Scope holder for backtracking int variables */
  scope_holder_t scope;

  /** IDs of various plugins, if added */
  uint32_t bool_plugin_id;
  uint32_t uf_plugin_id;
  uint32_t ite_plugin_id;
  uint32_t nra_plugin_id;
  uint32_t bv_plugin_id;
  uint32_t ff_plugin_id;
};

static
bool mcsat_is_consistent(mcsat_solver_t* mcsat) {
  return trail_is_consistent(mcsat->trail) && mcsat->variable_in_conflict == variable_null;
}

static
void mcsat_add_lemma(mcsat_solver_t* mcsat, ivector_t* lemma, term_t decision_bound);

static
void propagation_check(const ivector_t* reasons, term_t x, term_t subst);

static
void mcsat_stats_init(mcsat_solver_t* mcsat) {
  mcsat->solver_stats.assertions = statistics_new_int(&mcsat->stats, "mcsat::assertions");
  mcsat->solver_stats.conflicts = statistics_new_int(&mcsat->stats, "mcsat::conflicts");
  mcsat->solver_stats.avg_conflict_size = statistics_new_avg(&mcsat->stats, "mcsat::avg_conflict_size");
  mcsat->solver_stats.decisions = statistics_new_int(&mcsat->stats, "mcsat::decisions");
  mcsat->solver_stats.gc_calls = statistics_new_int(&mcsat->stats, "mcsat::gc_calls");
  mcsat->solver_stats.lemmas = statistics_new_int(&mcsat->stats, "mcsat::lemmas");
  mcsat->solver_stats.restarts = statistics_new_int(&mcsat->stats, "mcsat::restarts");
  mcsat->solver_stats.recaches = statistics_new_int(&mcsat->stats, "mcsat::recaches");
}

static
void mcsat_heuristics_init(mcsat_solver_t* mcsat, const param_t *params) {
  mcsat->heuristic_params.restart_interval = 10;
  mcsat->heuristic_params.lemma_restart_weight_type = LEMMA_WEIGHT_SIZE;
  mcsat->heuristic_params.recache_interval = 300;
  // Use params for random decision parameters
  mcsat->heuristic_params.random_decision_freq = params->randomness;
  mcsat->heuristic_params.random_decision_seed = params->random_seed;
}

static
bool mcsat_evaluates_at(const mcsat_evaluator_interface_t* self, term_t t, int_mset_t* vars, mcsat_value_t* value, uint32_t trail_size) {

  const mcsat_solver_t* mcsat = ((const mcsat_evaluator_t*) self)->solver;
  assert(value != NULL);

  if (trace_enabled(mcsat->ctx->trace, "mcsat::resolve")) {
    FILE* out = trace_out(mcsat->ctx->trace);
    fprintf(out, "explaining eval of: ");
    term_print_to_file(out, mcsat->terms, t);
    fprintf(out, " -> ");
    mcsat_value_print(value, out);
    fprintf(out, "\n");
  }

  uint32_t i;
  term_kind_t kind;
  type_kind_t type_kind;
  bool evaluates = false;
  plugin_t* plugin;

  kind = term_kind(mcsat->terms, t);
  bool is_equality = false;
  switch (kind) {
  case EQ_TERM:
  case BV_EQ_ATOM:
  case ARITH_BINEQ_ATOM:
  case ARITH_FF_BINEQ_ATOM:
    is_equality = true;
    break;
  default:
    // Nothing
    break;
  }

  if (!is_equality) {
    for (i = kind; mcsat->kind_owners[i] != MCSAT_MAX_PLUGINS; i += NUM_TERM_KINDS) {
      int_mset_clear(vars);
      plugin = mcsat->plugins[mcsat->kind_owners[i]].plugin;
      if (plugin->explain_evaluation) {
        if (trace_enabled(mcsat->ctx->trace, "mcsat::resolve")) {
          FILE* out = trace_out(mcsat->ctx->trace);
          fprintf(out, "explaining eval with: %s\n", mcsat->plugins[mcsat->kind_owners[i]].plugin_name);
        }
        evaluates = plugin->explain_evaluation(plugin, t, vars, value);
        if (evaluates) {
          return true;
        }
      }
    }
  } else {
    composite_term_t* eq_desc = composite_term_desc(mcsat->terms, t);
    type_kind = term_type_kind(mcsat->terms, eq_desc->arg[0]);
    for (i = type_kind; mcsat->type_owners[i] != MCSAT_MAX_PLUGINS; i += NUM_TERM_KINDS) {
      int_mset_clear(vars);
      plugin = mcsat->plugins[mcsat->type_owners[i]].plugin;
      if (plugin->explain_evaluation) {
        if (trace_enabled(mcsat->ctx->trace, "mcsat::resolve")) {
          FILE* out = trace_out(mcsat->ctx->trace);
          fprintf(out, "explaining eval with: %s\n", mcsat->plugins[mcsat->type_owners[i]].plugin_name);
        }
        evaluates = plugin->explain_evaluation(plugin, t, vars, value);
        if (evaluates) {
          return true;
        }
      }
    }
  }

  if (!evaluates) {
    // Maybe the term itself evaluates
    term_t t_unsigned = unsigned_term(t);
    variable_t t_var = variable_db_get_variable_if_exists(mcsat->var_db, t_unsigned);
    if (t_var != variable_null) {
      if (trail_has_value(mcsat->trail, t_var)) {
        const mcsat_value_t* t_var_value = trail_get_value(mcsat->trail, t_var);
        bool negated = is_neg_term(t);
        if ((negated && t_var_value->b != value->b)
            || (!negated && t_var_value->b == value->b)) {
          int_mset_clear(vars);
          int_mset_add(vars, t_var);
          return true;
        }
      }
      if (vars->size == 0) {
        int_mset_add(vars, t_var);
      }
    }
  }

  return false;
}

/** Construct the mcsat evaluator */
void mcsat_evaluator_construct(mcsat_evaluator_t* evaluator, mcsat_solver_t* solver) {
  evaluator->evaluates_at = mcsat_evaluates_at;
  evaluator->solver = solver;
}

/** Callback on propagations */
static
bool trail_token_add(trail_token_t* token, variable_t x, const mcsat_value_t* value) {
  plugin_trail_token_t* tk = (plugin_trail_token_t*) token;
  mcsat_solver_t* mcsat = tk->ctx->mcsat;
  mcsat_trail_t* trail = mcsat->trail;
  bool is_decision;

  is_decision = tk->x != variable_null;

  if (ctx_trace_enabled(&tk->ctx->ctx, "trail::add")) {
    if (is_decision) {
      ctx_trace_printf(&tk->ctx->ctx, "plugin %s deciding ", tk->ctx->plugin_name);\
    } else {
      ctx_trace_printf(&tk->ctx->ctx, "plugin %s propagating ", tk->ctx->plugin_name);\
    }
    variable_db_print_variable(mcsat->var_db, x, ctx_trace_out(&tk->ctx->ctx));
    ctx_trace_printf(&tk->ctx->ctx, " -> ");
    mcsat_value_print(value, ctx_trace_out(&tk->ctx->ctx));
    ctx_trace_printf(&tk->ctx->ctx, "\n");
  }

  if (trail_has_value(trail, x)) {
    return false;
  }

  tk->used ++;

  if (is_decision) {
    trail_add_decision(trail, x, value, tk->ctx->ctx.plugin_id);
  } else {
    trail_add_propagation(trail, x, value, tk->ctx->ctx.plugin_id, trail->decision_level);
  }

  if (ctx_trace_enabled(&tk->ctx->ctx, "mcsat::propagation::check") && !is_decision) {
    uint32_t plugin_id = tk->ctx->ctx.plugin_id;
    if (plugin_id != mcsat->bool_plugin_id) {
      ivector_t reason;
      init_ivector(&reason, 0);
      plugin_t* plugin = mcsat->plugins[plugin_id].plugin;
      term_t substitution = plugin->explain_propagation(plugin, x, &reason);
      term_t x_term = variable_db_get_term(mcsat->var_db, x);
      propagation_check(&reason, x_term, substitution);
      delete_ivector(&reason);
    }
  }

  return true;
}

/** Callback on propagations at lower levels */
static
bool trail_token_add_at_level(trail_token_t* token, variable_t x, const mcsat_value_t* value, uint32_t level) {
  plugin_trail_token_t* tk = (plugin_trail_token_t*) token;
  mcsat_solver_t* mcsat = tk->ctx->mcsat;
  mcsat_trail_t* trail = mcsat->trail;

  if (ctx_trace_enabled(&tk->ctx->ctx, "trail::add")) {
    ctx_trace_printf(&tk->ctx->ctx, "plugin %s propagating ", tk->ctx->plugin_name);
    variable_db_print_variable(mcsat->var_db, x, ctx_trace_out(&tk->ctx->ctx));
    ctx_trace_printf(&tk->ctx->ctx, " -> ");
    mcsat_value_print(value, ctx_trace_out(&tk->ctx->ctx));
    ctx_trace_printf(&tk->ctx->ctx, "\n");
  }

  // Only for propagations, we can't decide on lower levels
  assert(tk->x == variable_null);

  if (trail_has_value(trail, x)) {
    return false;
  }

  tk->used ++;

  // Check for trail level
  if (level < trail->decision_level_base) {
    level = trail->decision_level_base;
  }

  // Add the propagation
  trail_add_propagation(trail, x, value, tk->ctx->ctx.plugin_id, level);

  return true;
}


static
void trail_token_conflict(trail_token_t* token) {
  plugin_trail_token_t* tk = (plugin_trail_token_t*) token;

  if (ctx_trace_enabled(&tk->ctx->ctx, "trail::conflict")) {
    ctx_trace_printf(&tk->ctx->ctx, "plugin %s reporting a conflict\n", tk->ctx->plugin_name);
  }

  tk->used ++;

  // Remember the plugin that reported the
  tk->ctx->mcsat->plugin_in_conflict = tk->ctx;

  // Set the trail to be inconsistent
  trail_set_inconsistent(tk->ctx->mcsat->trail);
}

static
void trail_token_lemma(trail_token_t* token, term_t lemma) {
  plugin_trail_token_t* tk = (plugin_trail_token_t*) token;

  if (ctx_trace_enabled(&tk->ctx->ctx, "trail::lemma")) {
    ctx_trace_printf(&tk->ctx->ctx, "plugin %s reporting a lemma\n", tk->ctx->plugin_name);
    ctx_trace_term(&tk->ctx->ctx, lemma);
  }

  tk->used ++;

  // Remember the lemma
  ivector_push(&tk->ctx->mcsat->plugin_lemmas, lemma);
}

static
void trail_token_definition_lemma(trail_token_t* token, term_t lemma, term_t t) {
  plugin_trail_token_t* tk = (plugin_trail_token_t*) token;

  if (ctx_trace_enabled(&tk->ctx->ctx, "trail::lemma")) {
    ctx_trace_printf(&tk->ctx->ctx, "plugin %s reporting a definition lemma\n", tk->ctx->plugin_name);
    ctx_trace_term(&tk->ctx->ctx, lemma);
  }

  tk->used ++;

  // Remember the definition
  ivector_push(&tk->ctx->mcsat->plugin_definition_lemmas, lemma);
  ivector_push(&tk->ctx->mcsat->plugin_definition_vars, t);
}

/** Construct the trail token */
static inline
void trail_token_construct(plugin_trail_token_t* token, mcsat_plugin_context_t* ctx, variable_t x) {
  token->token_interface.add = trail_token_add;
  token->token_interface.add_at_level = trail_token_add_at_level;
  token->token_interface.conflict = trail_token_conflict;
  token->token_interface.lemma = trail_token_lemma;
  token->token_interface.definition_lemma = trail_token_definition_lemma;
  token->ctx = ctx;
  token->x = x;
  token->used = 0;
}

void mcsat_plugin_term_notification_by_kind(plugin_context_t* self, term_kind_t kind, bool is_internal) {
  uint32_t i;
  mcsat_plugin_context_t* mctx;

  mctx = (mcsat_plugin_context_t*) self;
  assert(self->plugin_id != MCSAT_MAX_PLUGINS);
  for (i = kind; mctx->mcsat->kind_owners[i] != MCSAT_MAX_PLUGINS; i += NUM_TERM_KINDS) {}
  mctx->mcsat->kind_owners[i] = self->plugin_id;
  if (is_internal) {
    int_hset_add(&mctx->mcsat->internal_kinds, kind);
  }
}

void mcsat_plugin_term_notification_by_type(plugin_context_t* self, type_kind_t kind) {
  uint32_t i;
  mcsat_plugin_context_t* mctx;

  mctx = (mcsat_plugin_context_t*) self;
  assert(self->plugin_id != MCSAT_MAX_PLUGINS);
  for (i = kind; mctx->mcsat->type_owners[i] != MCSAT_MAX_PLUGINS; i += NUM_TYPE_KINDS) {}
  mctx->mcsat->type_owners[i] = self->plugin_id;
}

static
void mcsat_request_restart(mcsat_solver_t* mcsat) {
  mcsat->pending_requests = true;
  mcsat->pending_requests_all.restart = true;
}

static
void mcsat_request_gc(mcsat_solver_t* mcsat) {
  mcsat->pending_requests = true;
  mcsat->pending_requests_all.gc_calls = true;
}

static
void mcsat_request_recache(mcsat_solver_t* mcsat) {
  mcsat->pending_requests = true;
  mcsat->pending_requests_all.recache = true;
}

static
void mcsat_plugin_context_restart(plugin_context_t* self) {
  mcsat_plugin_context_t* mctx;

  mctx = (mcsat_plugin_context_t*) self;
  mcsat_request_restart(mctx->mcsat);
}

static
void mcsat_plugin_context_gc(plugin_context_t* self) {
  mcsat_plugin_context_t* mctx;

  mctx = (mcsat_plugin_context_t*) self;
  mcsat_request_gc(mctx->mcsat);
}

static inline
void mcsat_add_top_decision(mcsat_solver_t* mcsat, variable_t x) {
  for (int i = 0; i < mcsat->top_decision_vars.size; ++i) {
    if (mcsat->top_decision_vars.data[i] == x) {
      return;
    }
  }
  ivector_push(&mcsat->top_decision_vars, x);
}

static inline
void mcsat_add_decision_hint(mcsat_solver_t* mcsat, variable_t x) {
  int_queue_push(&mcsat->hinted_decision_vars, x);
}

static inline
void mcsat_bump_variable(mcsat_solver_t* mcsat, variable_t x, uint32_t factor) {
  var_queue_bump_variable(&mcsat->var_queue, x, factor);
}

#if 0
static inline
void mcsat_bump_variables_vector(mcsat_solver_t* mcsat, const ivector_t* vars) {
  uint32_t i;
  for (i = 0; i < vars->size; ++ i) {
    mcsat_bump_variable(mcsat, vars->data[i], 1);
  }
}
#endif

static inline
void mcsat_bump_variables_mset(mcsat_solver_t* mcsat, const int_mset_t* vars) {
  uint32_t i;
  for (i = 0; i < vars->element_list.size; ++ i) {
    variable_t x = vars->element_list.data[i];
    uint32_t n = int_mset_contains(vars, x);
    mcsat_bump_variable(mcsat, x, n);
  }
}

static
void mcsat_plugin_context_bump_variable(plugin_context_t* self, variable_t x) {
  mcsat_plugin_context_t* mctx;

  mctx = (mcsat_plugin_context_t*) self;
  mcsat_bump_variable(mctx->mcsat, x, 1);
}

static
void mcsat_plugin_context_bump_variable_n(plugin_context_t* self, variable_t x, uint32_t n) {
  mcsat_plugin_context_t* mctx;

  mctx = (mcsat_plugin_context_t*) self;
  mcsat_bump_variable(mctx->mcsat, x, n);
}

static
int mcsat_plugin_context_cmp_variables(plugin_context_t* self, variable_t x, variable_t y) {
  mcsat_plugin_context_t* mctx;
  mctx = (mcsat_plugin_context_t*) self;
  return var_queue_cmp_variables(&mctx->mcsat->var_queue, x, y);
}

static
void mcsat_plugin_context_request_top_decision(plugin_context_t* self, variable_t x) {
  mcsat_plugin_context_t* mctx;
  mctx = (mcsat_plugin_context_t*) self;
  mcsat_add_top_decision(mctx->mcsat, x);
}

static
void mcsat_plugin_context_hint_next_decision(plugin_context_t* self, variable_t x) {
  mcsat_plugin_context_t* mctx;
  mctx = (mcsat_plugin_context_t*) self;
  mcsat_add_decision_hint(mctx->mcsat, x);
}

/*
 * Provide hint to the trail cache.
 */
static
void mcsat_plugin_context_hint_value(plugin_context_t* self, variable_t x, const mcsat_value_t* val) {
  mcsat_plugin_context_t* mctx;
  mctx = (mcsat_plugin_context_t*) self;
  trail_set_cached_value(mctx->mcsat->trail, x, val);
}

static
void mcsat_plugin_context_decision_calls(plugin_context_t* self, type_kind_t type) {
  mcsat_plugin_context_t* mctx;

  mctx = (mcsat_plugin_context_t*) self;
  assert(mctx->mcsat->decision_makers[type] == MCSAT_MAX_PLUGINS);
  mctx->mcsat->decision_makers[type] = self->plugin_id;
}

void mcsat_plugin_context_construct(mcsat_plugin_context_t* ctx, mcsat_solver_t* mcsat, uint32_t plugin_i, const char* plugin_name) {
  ctx->ctx.plugin_id = plugin_i;
  ctx->ctx.var_db = mcsat->var_db;
  ctx->ctx.tm = &mcsat->tm;
  ctx->ctx.terms = mcsat->terms;
  ctx->ctx.types = mcsat->types;
  ctx->ctx.exception = mcsat->exception;
  ctx->ctx.options = &mcsat->ctx->mcsat_options;
  ctx->ctx.trail = mcsat->trail;
  ctx->ctx.stats = &mcsat->stats;
  ctx->ctx.tracer = mcsat->ctx->trace;
  ctx->ctx.stop_search = &mcsat->stop_search;
  ctx->ctx.request_decision_calls = mcsat_plugin_context_decision_calls;
  ctx->ctx.request_term_notification_by_kind = mcsat_plugin_term_notification_by_kind;
  ctx->ctx.request_term_notification_by_type = mcsat_plugin_term_notification_by_type;
  ctx->ctx.request_restart = mcsat_plugin_context_restart;
  ctx->ctx.request_gc = mcsat_plugin_context_gc;
  ctx->ctx.bump_variable = mcsat_plugin_context_bump_variable;
  ctx->ctx.bump_variable_n = mcsat_plugin_context_bump_variable_n;
  ctx->ctx.cmp_variables = mcsat_plugin_context_cmp_variables;
  ctx->ctx.request_top_decision = mcsat_plugin_context_request_top_decision;
  ctx->ctx.hint_next_decision = mcsat_plugin_context_hint_next_decision;
  ctx->ctx.hint_value = mcsat_plugin_context_hint_value;
  ctx->mcsat = mcsat;
  ctx->plugin_name = plugin_name;
}

static
void mcsat_term_registration_enqueue(mcsat_solver_t* mcsat, term_t t) {
  // Make sure it's positive polarity
  t = unsigned_term(t);

  // Enqueue if not processed already
  if (!int_hset_member(&mcsat->registration_cache, t)) {
    int_hset_add(&mcsat->registration_cache, t);
    int_queue_push(&mcsat->registration_queue, t);
  }
}

static
void mcsat_new_variable_notify(solver_new_variable_notify_t* self, variable_t x) {
  term_t t;
  uint32_t size;

  // Enqueue for registration
  t = variable_db_get_term(self->mcsat->var_db, x);
  mcsat_term_registration_enqueue(self->mcsat, t);

  // Ensure that the trail/model is aware of this
  trail_new_variable_notify(self->mcsat->trail, x);

  // Add the variable to the queue
  if (x >= self->mcsat->var_queue.size) {
    size = x + x/2 + 1;
    assert(size > x);
    var_queue_extend(&self->mcsat->var_queue, size);
  }
  var_queue_insert(&self->mcsat->var_queue, x);
}

static
uint32_t mcsat_add_plugin(mcsat_solver_t* mcsat, plugin_allocator_t plugin_allocator, const char* plugin_name) {

  // Allocate the plugin
  plugin_t* plugin = plugin_allocator();
  // The index of the plugin
  uint32_t plugin_i = mcsat->plugins_count;
  // Allocate the request
  mcsat_plugin_context_t* plugin_ctx = safe_malloc(sizeof(mcsat_plugin_context_t));
  mcsat_plugin_context_construct(plugin_ctx, mcsat, plugin_i, plugin_name);
  // Construct the plugin
  plugin->construct(plugin, (plugin_context_t*) plugin_ctx);

  // Add the plugin to the list of plugins
  mcsat->plugins[plugin_i].plugin = plugin;
  mcsat->plugins[plugin_i].plugin_ctx = plugin_ctx;
  mcsat->plugins[plugin_i].plugin_name = safe_strdup(plugin_name);
  mcsat->plugins_count ++;

  return plugin_i;
}

static
void mcsat_add_plugins(mcsat_solver_t* mcsat) {
  mcsat->bool_plugin_id = mcsat_add_plugin(mcsat, bool_plugin_allocator, "bool_plugin");
  mcsat->uf_plugin_id = mcsat_add_plugin(mcsat, uf_plugin_allocator, "uf_plugin");
  mcsat->ite_plugin_id = mcsat_add_plugin(mcsat, ite_plugin_allocator, "ite_plugin");
  mcsat->nra_plugin_id = mcsat_add_plugin(mcsat, nra_plugin_allocator, "nra_plugin");
  mcsat->bv_plugin_id = mcsat_add_plugin(mcsat, bv_plugin_allocator, "bv_plugin");
  mcsat->ff_plugin_id = mcsat_add_plugin(mcsat, ff_plugin_allocator, "ff_plugin");
}

static
void mcsat_construct(mcsat_solver_t* mcsat, const context_t* ctx) {
  uint32_t i;

  assert(ctx != NULL);
  assert(ctx->arch == CTX_ARCH_MCSAT);
  assert(ctx->terms != NULL);
  assert(ctx->types != NULL);

  mcsat->stop_search = false;
  mcsat->ctx = ctx;
  mcsat->exception = (jmp_buf*) &ctx->env;
  mcsat->types = ctx->types;
  mcsat->terms = ctx->terms;
  mcsat->terms_size_on_solver_entry = 0;
  mcsat->status = STATUS_IDLE;
  mcsat->inconsistent_push_calls = 0;

  // New term manager
  init_term_manager(&mcsat->tm, mcsat->terms);
  mcsat->tm.simplify_bveq1 = false;
  mcsat->tm.simplify_ite = false;

  // The new variable listener
  mcsat->var_db_notify.mcsat = mcsat;
  mcsat->var_db_notify.new_variable = mcsat_new_variable_notify;

  // The variable database
  mcsat->var_db = safe_malloc(sizeof(variable_db_t));
  variable_db_construct(mcsat->var_db, mcsat->terms, mcsat->types, mcsat->ctx->trace);
  variable_db_add_new_variable_listener(mcsat->var_db, (variable_db_new_variable_notify_t*)&mcsat->var_db_notify);

  // List of assertions
  init_ivector(&mcsat->assertion_vars, 0);
  init_ivector(&mcsat->assertion_terms_original, 0);
  init_ivector(&mcsat->assertions_tmp, 0);

  // The trail
  mcsat->trail = safe_malloc(sizeof(mcsat_trail_t));
  trail_construct(mcsat->trail, mcsat->var_db);

  // Variable registration queue
  init_int_queue(&mcsat->registration_queue, 0);
  init_int_hset(&mcsat->registration_cache, 0);

  // Init all the term owners to NULL
  for (i = 0; i < NUM_TERM_KINDS * MCSAT_MAX_PLUGINS; ++ i) {
    mcsat->kind_owners[i] = MCSAT_MAX_PLUGINS;
  }

  // Internal kinds
  init_int_hset(&mcsat->internal_kinds, 0);

  // Init all the type owners to NULL
  for (i = 0; i < NUM_TYPE_KINDS * MCSAT_MAX_PLUGINS; ++ i) {
    mcsat->type_owners[i] = MCSAT_MAX_PLUGINS;
  }

  // Init all the decision makers to NULL
  for (i = 0; i < NUM_TYPE_KINDS; ++ i) {
    mcsat->decision_makers[i] = MCSAT_MAX_PLUGINS;
  }

  // Plugin vectors
  mcsat->plugins_count = 0;
  mcsat->plugin_in_conflict = 0;

  // Construct the evaluator
  mcsat_evaluator_construct(&mcsat->evaluator, mcsat);

  // Construct the preprocessor
  preprocessor_construct(&mcsat->preprocessor, mcsat->terms, mcsat->exception, &mcsat->ctx->mcsat_options);

  // The variable queue
  init_ivector(&mcsat->top_decision_vars, 0);
  init_int_queue(&mcsat->hinted_decision_vars, 0);
  var_queue_construct(&mcsat->var_queue);

  mcsat->pending_requests_all.restart = false;
  mcsat->pending_requests_all.gc_calls = false;
  mcsat->pending_requests_all.recache = false;
  mcsat->pending_requests = false;

  mcsat->variable_in_conflict = variable_null;
  mcsat->assumption_i = 0;
  mcsat->assumptions_decided_level = -1;
  mcsat->interpolant = NULL_TERM;

  // Assumptions vector
  init_ivector(&mcsat->assumption_vars, 0);

  // Lemmas vector
  init_ivector(&mcsat->plugin_lemmas, 0);
  init_ivector(&mcsat->plugin_definition_lemmas, 0);
  init_ivector(&mcsat->plugin_definition_vars, 0);
  mcsat->plugin_definition_lemmas_i = 0;

  // Construct stats
  statistics_construct(&mcsat->stats);
  mcsat_stats_init(mcsat);

  // Scope for backtracking
  scope_holder_construct(&mcsat->scope);

  // Construct the plugins
  mcsat_add_plugins(mcsat);
}

void mcsat_destruct(mcsat_solver_t* mcsat) {
  uint32_t i;
  plugin_t* plugin;

  // Delete the plugin data
  for (i = 0; i < mcsat->plugins_count; ++ i) {
    // Plugin
    plugin = mcsat->plugins[i].plugin;
    plugin->destruct(mcsat->plugins[i].plugin);
    safe_free(plugin);
    // Plugin context
    safe_free(mcsat->plugins[i].plugin_ctx);
    // The name
    safe_free(mcsat->plugins[i].plugin_name);
  }

  delete_term_manager(&mcsat->tm);
  delete_int_queue(&mcsat->registration_queue);
  delete_int_hset(&mcsat->registration_cache);
  delete_ivector(&mcsat->assertion_vars);
  delete_ivector(&mcsat->assertion_terms_original);
  delete_ivector(&mcsat->assertions_tmp);
  trail_destruct(mcsat->trail);
  safe_free(mcsat->trail);
  variable_db_destruct(mcsat->var_db);
  safe_free(mcsat->var_db);
  preprocessor_destruct(&mcsat->preprocessor);
  delete_ivector(&mcsat->top_decision_vars);
  delete_int_queue(&mcsat->hinted_decision_vars);
  var_queue_destruct(&mcsat->var_queue);
  delete_ivector(&mcsat->plugin_lemmas);
  delete_ivector(&mcsat->plugin_definition_lemmas);
  delete_ivector(&mcsat->plugin_definition_vars);
  statistics_destruct(&mcsat->stats);
  scope_holder_destruct(&mcsat->scope);
  delete_ivector(&mcsat->assumption_vars);
  delete_int_hset(&mcsat->internal_kinds);
}

mcsat_solver_t* mcsat_new(const context_t* ctx) {
  mcsat_solver_t* mcsat = (mcsat_solver_t*) safe_malloc(sizeof(mcsat_solver_t));
  mcsat_construct(mcsat, ctx);
  return mcsat;
}


smt_status_t mcsat_status(const mcsat_solver_t* mcsat) {
  return mcsat->status;
}

static
void mcsat_notify_plugins(mcsat_solver_t* mcsat, plugin_notify_kind_t kind) {
  uint32_t i;
  plugin_t* plugin;

  for (i = 0; i < mcsat->plugins_count; ++ i) {
    plugin = mcsat->plugins[i].plugin;
    if (plugin->event_notify) {
      plugin->event_notify(plugin, kind);
    }
  }
}

void mcsat_reset(mcsat_solver_t* mcsat) {
  // Reset everything
  const context_t* ctx = mcsat->ctx;
  mcsat_destruct(mcsat);
  mcsat_construct(mcsat, ctx);
}

static
void mcsat_push_internal(mcsat_solver_t* mcsat) {
  uint32_t i;
  plugin_t* plugin;

  // Push the plugins
  for (i = 0; i < mcsat->plugins_count; ++ i) {
    plugin = mcsat->plugins[i].plugin;
    if (plugin->push) {
      plugin->push(plugin);
    }
  }
}

static
void mcsat_pop_internal(mcsat_solver_t* mcsat) {
  uint32_t i;
  plugin_t* plugin;
  ivector_t* unassigned;

  // Pop the plugins
  for (i = 0; i < mcsat->plugins_count; ++ i) {
    plugin = mcsat->plugins[i].plugin;
    if (plugin->pop) {
      plugin->pop(plugin);
    }
  }

  // Re-add the variables that were unassigned
  unassigned = trail_get_unassigned(mcsat->trail);
  for (i = 0; i < unassigned->size; ++ i) {
    var_queue_insert(&mcsat->var_queue, unassigned->data[i]);
  }
  ivector_reset(unassigned);

  // remove all the hints
  int_queue_reset(&mcsat->hinted_decision_vars);
}

static
void mcsat_backtrack_to(mcsat_solver_t* mcsat, uint32_t level, bool update_cache);

static
void mcsat_gc(mcsat_solver_t* mcsat, bool mark_and_gc_internal);

void mcsat_push(mcsat_solver_t* mcsat) {

  assert(mcsat->status == STATUS_IDLE); // We must have clear before

  if (trace_enabled(mcsat->ctx->trace, "mcsat::push")) {
    mcsat_trace_printf(mcsat->ctx->trace, "mcsat::push start\n");
    trail_print(mcsat->trail, trace_out(mcsat->ctx->trace));
  }

  if (!mcsat_is_consistent(mcsat)) {
    mcsat->inconsistent_push_calls ++;
    return;
  }

  // Internal stuff push
  scope_holder_push(&mcsat->scope,
      &mcsat->assertion_vars.size,
      &mcsat->assertion_terms_original.size,
      &mcsat->plugin_definition_lemmas.size,
      NULL);
  // Regular push for the internal data structures
  mcsat_push_internal(mcsat);
  // Push and set the base level on the trail
  trail_new_base_level(mcsat->trail);
  // Push the preprocessor
  preprocessor_push(&mcsat->preprocessor);

  if (trace_enabled(mcsat->ctx->trace, "mcsat::push")) {
    mcsat_trace_printf(mcsat->ctx->trace, "mcsat::pop end\n");
    trail_print(mcsat->trail, trace_out(mcsat->ctx->trace));
  }

  mcsat->interpolant = NULL_TERM;
}


void mcsat_pop(mcsat_solver_t* mcsat) {

  // External pop:
  // - internal pop
  // - assertions
  // - variables and terms

  if (trace_enabled(mcsat->ctx->trace, "mcsat::pop")) {
    mcsat_trace_printf(mcsat->ctx->trace, "mcsat::pop start\n");
    trail_print(mcsat->trail, trace_out(mcsat->ctx->trace));
  }

  if (mcsat->inconsistent_push_calls > 0) {
    mcsat->inconsistent_push_calls --;
    mcsat->status = STATUS_IDLE;
    return;
  }

  // Backtrack trail
  uint32_t new_base_level = trail_pop_base_level(mcsat->trail);

  // Backtrack solver
  mcsat_backtrack_to(mcsat, new_base_level, false);

  // Internal stuff pop
  uint32_t assertion_vars_size = 0;
  uint32_t assertion_terms_size = 0;
  uint32_t definition_lemmas_size = 0;
  scope_holder_pop(&mcsat->scope,
      &assertion_vars_size,
      &assertion_terms_size,
      &definition_lemmas_size,
      NULL);
  ivector_shrink(&mcsat->assertion_vars, assertion_vars_size);
  ivector_shrink(&mcsat->assertion_terms_original, assertion_terms_size);

  // Pop the preprocessor
  preprocessor_pop(&mcsat->preprocessor);

  // Notify all the plugins that we just popped
  mcsat_notify_plugins(mcsat, MCSAT_SOLVER_POP);

  // Garbage collect
  mcsat_gc(mcsat, false);
  (*mcsat->solver_stats.gc_calls) ++;

  // Definition lemmas (keep the ones that need the definition (variable still active)
  uint32_t lemma_i = definition_lemmas_size, lemma_to_keep = definition_lemmas_size;
  for (; lemma_i < mcsat->plugin_definition_lemmas.size; ++ lemma_i) {
    term_t lemma = mcsat->plugin_definition_lemmas.data[lemma_i];
    term_t variable = mcsat->plugin_definition_vars.data[lemma_i];
    if (variable_db_has_variable(mcsat->var_db, variable)) {
      mcsat->plugin_definition_lemmas.data[lemma_to_keep] = lemma;
      mcsat->plugin_definition_vars.data[lemma_to_keep] = variable;
      lemma_to_keep ++;
    }
  }
  ivector_shrink(&mcsat->plugin_definition_lemmas, lemma_to_keep);
  ivector_shrink(&mcsat->plugin_definition_vars, lemma_to_keep);
  mcsat->plugin_definition_lemmas_i = definition_lemmas_size;
  if (definition_lemmas_size < mcsat->plugin_definition_lemmas.size) {
    mcsat_assert_formulas(mcsat, 0, NULL);
  }

  // Set the status back to idle
  mcsat->status = STATUS_IDLE;
  mcsat->interpolant = NULL_TERM;

  if (trace_enabled(mcsat->ctx->trace, "mcsat::pop")) {
    mcsat_trace_printf(mcsat->ctx->trace, "mcsat::pop end\n");
    trail_print(mcsat->trail, trace_out(mcsat->ctx->trace));
  }
}

void mcsat_clear(mcsat_solver_t* mcsat) {
  // Clear to be ready for more assertions:
  // - Pop internal to base level
  mcsat->assumption_i = 0;
  mcsat->assumptions_decided_level = -1;
  mcsat_backtrack_to(mcsat, mcsat->trail->decision_level_base, true);
  mcsat->status = STATUS_IDLE;
  mcsat->interpolant = NULL_TERM; // BD
}

/**
 * Get the indices of the plugins that claim to own the term t by type.
 */
static inline
void mcsat_get_type_owners(mcsat_solver_t* mcsat, term_t t, int_mset_t* owners) {
  uint32_t i, plugin_i;
  i = type_kind(mcsat->types, term_type(mcsat->terms, t));
  plugin_i = mcsat->type_owners[i];
  assert(plugin_i != MCSAT_MAX_PLUGINS);
  do  {
    int_mset_add(owners, plugin_i);
    i += NUM_TYPE_KINDS;
    plugin_i = mcsat->type_owners[i];
  } while (plugin_i != MCSAT_MAX_PLUGINS);
}

/**
 * Get the indices of the plugins that claim to own the term t by kind.
 */
static inline
void mcsat_get_kind_owners(mcsat_solver_t* mcsat, term_t t, int_mset_t* owners) {
  uint32_t i, plugin_i;
  i = term_kind(mcsat->terms, t);
  plugin_i = mcsat->kind_owners[i];
  if (trace_enabled(mcsat->ctx->trace, "mcsat::get_kind_owner")) {
    mcsat_trace_printf(mcsat->ctx->trace, "get_kind_owner: ");
    trace_term_ln(mcsat->ctx->trace, mcsat->terms, t);
  }
  assert(plugin_i != MCSAT_MAX_PLUGINS || i == UNINTERPRETED_TERM || i == CONSTANT_TERM);
  while (plugin_i != MCSAT_MAX_PLUGINS) {
    int_mset_add(owners, plugin_i);
    i += NUM_TERM_KINDS;
    plugin_i = mcsat->kind_owners[i];
  };
}


static void mcsat_process_registration_queue(mcsat_solver_t* mcsat) {
  term_t t;
  uint32_t i, plugin_i;
  plugin_t* plugin;
  plugin_trail_token_t prop_token;
  int_mset_t to_notify;
  ivector_t* to_notify_list;

  int_mset_construct(&to_notify, MCSAT_MAX_PLUGINS);

  while (!int_queue_is_empty(&mcsat->registration_queue)) {
    // Next term to register
    t = int_queue_pop(&mcsat->registration_queue);
    assert(is_pos_term(t));

    if (trace_enabled(mcsat->ctx->trace, "mcsat::registration")) {
      mcsat_trace_printf(mcsat->ctx->trace, "term registration: ");
      trace_term_ln(mcsat->ctx->trace, mcsat->terms, t);
    }

    // Get who to notify
    int_mset_clear(&to_notify);

    // We notify the owners of the term type
    mcsat_get_type_owners(mcsat, t, &to_notify);

    // We also notify the term kind owners, except for equality
    term_kind_t kind = term_kind(mcsat->terms, t);
    if (kind == EQ_TERM) {
      mcsat_get_type_owners(mcsat, composite_term_arg(mcsat->terms, t, 0), &to_notify);
      mcsat_get_type_owners(mcsat, composite_term_arg(mcsat->terms, t, 1), &to_notify);
    } else {
      mcsat_get_kind_owners(mcsat, t, &to_notify);
    }

    // Notify
    to_notify_list = int_mset_get_list(&to_notify);
    for (i = 0; i < to_notify_list->size; ++i) {
      plugin_i = to_notify_list->data[i];
      plugin = mcsat->plugins[plugin_i].plugin;
      trail_token_construct(&prop_token, mcsat->plugins[plugin_i].plugin_ctx, variable_null);
      plugin->new_term_notify(plugin, t, (trail_token_t*) &prop_token);
    }
  }

  int_mset_destruct(&to_notify);
}

/** Pass true to mark terms and types in the internal yices term tables */
static
void mcsat_gc(mcsat_solver_t* mcsat, bool mark_and_gc_internal) {

  uint32_t i;
  variable_t var;
  gc_info_t gc_vars;
  plugin_t* plugin;

  if (trace_enabled(mcsat->ctx->trace, "mcsat::gc")) {
    mcsat_trace_printf(mcsat->ctx->trace, "mcsat_gc():\n");
    mcsat_show_stats(mcsat, mcsat->ctx->trace->file);
  }

  // Mark previously used term in the term table
  // set_bitvector(mcsat->terms->mark, mcsat->terms_size_on_solver_entry);

  // Construct the variable info
  gc_info_construct(&gc_vars, variable_null, true);

  if (trace_enabled(mcsat->ctx->trace, "mcsat::gc")) {
    mcsat_trace_printf(mcsat->ctx->trace, "mcsat_gc(): marking\n");
  }

  // Mark the assertion variables as needed
  for (i = 0; i < mcsat->assertion_vars.size; ++ i) {
    var = mcsat->assertion_vars.data[i];
    assert(variable_db_is_variable(mcsat->var_db, var, true));
    gc_info_mark(&gc_vars, var);
    if (trace_enabled(mcsat->ctx->trace, "mcsat::gc")) {
      mcsat_trace_printf(mcsat->ctx->trace, "mcsat_gc(): marking ");
      trace_term_ln(mcsat->ctx->trace, mcsat->terms, variable_db_get_term(mcsat->var_db, var));
    }
  }
  for (i = 0; i < mcsat->assumption_vars.size; ++ i) {
    var = mcsat->assumption_vars.data[i];
    assert(variable_db_is_variable(mcsat->var_db, var, true));
    gc_info_mark(&gc_vars, var);
    if (trace_enabled(mcsat->ctx->trace, "mcsat::gc")) {
      mcsat_trace_printf(mcsat->ctx->trace, "mcsat_gc(): marking ");
      trace_term_ln(mcsat->ctx->trace, mcsat->terms, variable_db_get_term(mcsat->var_db, var));
    }
  }

  // Mark the decision hints if there are any
  for (i = 0; i < int_queue_size(&mcsat->hinted_decision_vars); ++ i) {
    gc_info_mark(&gc_vars, int_queue_at(&mcsat->hinted_decision_vars, i));
  }
  for (i = 0; i < mcsat->top_decision_vars.size; ++i) {
    gc_info_mark(&gc_vars, mcsat->top_decision_vars.data[i]);
  }

  // Mark the trail variables as needed
  trail_gc_mark(mcsat->trail, &gc_vars);

  // Mark variables by plugins
  for (;;) {

    // Mark with each plugin
    for (i = 0; i < mcsat->plugins_count; ++ i) {
      if (trace_enabled(mcsat->ctx->trace, "mcsat::gc")) {
        mcsat_trace_printf(mcsat->ctx->trace, "mcsat_gc(): marking with %s\n", mcsat->plugins[i].plugin_name);
      }
      plugin = mcsat->plugins[i].plugin;
      if (plugin->gc_mark) {
        plugin->gc_mark(plugin, &gc_vars);
      }
    }

    // If any new ones marked, go to the new level and continue marking
    if (gc_info_get_level_size(&gc_vars) > 0) {
      gc_info_new_level(&gc_vars);
    } else {
      // Nothing new marked
      break;
    }
  }

  if (trace_enabled(mcsat->ctx->trace, "mcsat::gc")) {
    mcsat_trace_printf(mcsat->ctx->trace, "mcsat_gc(): sweeping\n");
  }

  // Collect the unused variables
  variable_db_gc_sweep(mcsat->var_db, &gc_vars);

  // Do the sweep
  for (i = 0; i < mcsat->plugins_count; ++ i) {
    plugin = mcsat->plugins[i].plugin;
    if (plugin->gc_sweep) {
      plugin->gc_sweep(plugin, &gc_vars);
    }
  }

  // Trail sweep
  trail_gc_sweep(mcsat->trail, &gc_vars);

  // Variable queue sweep
  var_queue_gc_sweep(&mcsat->var_queue, &gc_vars);

  // If asked mark all the terms
  if (mark_and_gc_internal) {
    for (i = 0; i < gc_vars.marked.size; ++ i) {
      variable_t x = gc_vars.marked.data[i];
      term_t x_term = variable_db_get_term(mcsat->var_db, x);
      term_t x_type = term_type(mcsat->terms, x_term);
      term_table_set_gc_mark(mcsat->terms, index_of(x_term));
      type_table_set_gc_mark(mcsat->types, x_type);
    }

    // Mark with each plugin
    for (i = 0; i < mcsat->plugins_count; ++ i) {
      if (trace_enabled(mcsat->ctx->trace, "mcsat::gc")) {
        mcsat_trace_printf(mcsat->ctx->trace, "mcsat_gc(): marking with %s\n", mcsat->plugins[i].plugin_name);
      }
      plugin = mcsat->plugins[i].plugin;
      if (plugin->gc_mark_and_clear) {
        plugin->gc_mark_and_clear(plugin);
      }
    }

    // Mark with the preprocessor
    preprocessor_gc_mark(&mcsat->preprocessor);
  }

  // Done, destruct
  gc_info_destruct(&gc_vars);

  // Remove terms from registration cache
  int_hset_t new_registration_cache;
  init_int_hset(&new_registration_cache, 0);
  int_hset_close(&mcsat->registration_cache);
  for (i = 0; i < mcsat->registration_cache.nelems; ++ i) {
    term_t t = mcsat->registration_cache.data[i];
    variable_t x = variable_db_get_variable_if_exists(mcsat->var_db, t);
    if (x != variable_null) {
      int_hset_add(&new_registration_cache, t);
    }
  }
  delete_int_hset(&mcsat->registration_cache);
  mcsat->registration_cache = new_registration_cache;

  // Garbage collect with yices
  // term_table_gc(mcsat->terms, 1);

  if (trace_enabled(mcsat->ctx->trace, "mcsat::gc")) {
    mcsat_trace_printf(mcsat->ctx->trace, "mcsat_gc(): done\n");
  }
}

static
void mcsat_backtrack_to(mcsat_solver_t* mcsat, uint32_t level, bool update_cache) {
  assert((int32_t) level >= mcsat->assumptions_decided_level);
  while (mcsat->trail->decision_level > level) {

    if (trace_enabled(mcsat->ctx->trace, "mcsat::incremental")) {
      trail_print(mcsat->trail, trace_out(mcsat->ctx->trace));
    }

    // Pop the trail
    trail_pop(mcsat->trail);

    if (trace_enabled(mcsat->ctx->trace, "mcsat::incremental")) {
      trail_print(mcsat->trail, trace_out(mcsat->ctx->trace));
    }

    // Pop the plugins
    mcsat_pop_internal(mcsat);
  }

  // save target cache (when backtracking)
  if (update_cache) trail_update_extra_cache(mcsat->trail);
}

static 
uint32_t mcsat_partial_restart_level(mcsat_solver_t *mcsat) {
  // If heap is empty, we go to base level
  if (var_queue_is_empty(&mcsat->var_queue)) {
    return mcsat->trail->decision_level_base;
  }

  uint32_t base = mcsat->trail->decision_level_base;
  uint32_t n = mcsat->trail->decision_level;
  uint32_t target_level = UINT32_MAX;
  variable_t x = mcsat->var_queue.heap[1];
  double ax = var_queue_get_activity(&mcsat->var_queue, x);
  // Most active unassigned variable in the heap
  while (!var_queue_is_empty(&mcsat->var_queue)) {
	  x = var_queue_pop(&mcsat->var_queue);
	  if (!trail_has_value(mcsat->trail, x)) {
	    ax = var_queue_get_activity(&mcsat->var_queue, x);
	    var_queue_insert(&mcsat->var_queue, x);
	    break;
	  }
	}

  // Scan the trail for decision variables
  for (uint32_t i = 0; i < mcsat->trail->elements.size; ++i) {
    variable_t v = mcsat->trail->elements.data[i];
    if (trail_get_assignment_type(mcsat->trail, v) == DECISION) {
      uint32_t level = trail_get_level(mcsat->trail, v);
      if (level > base && level <= n) {
        double v_activity = var_queue_get_activity(&mcsat->var_queue, v);
        //printf("  Level %u: decision var %d (activity %g)\n", level, v, v_activity);
        if (v_activity < ax) {
          //printf("  Backtracking to level %u\n", level - 1);
          target_level = level - 1;
          break;
        }
      }
    }
  }
  if (target_level != UINT32_MAX) {
    return target_level;
  }

  return base;
}

static
void mcsat_process_requests(mcsat_solver_t* mcsat) {

  if (mcsat->pending_requests) {

    // Restarts
    if (mcsat->pending_requests_all.restart) {
      // save target cache before restart
      trail_update_extra_cache(mcsat->trail);

      if (trace_enabled(mcsat->ctx->trace, "mcsat")) {
        mcsat_trace_printf(mcsat->ctx->trace, "restarting\n");
      }

      // Determine the backtrack level for restart:
      // If partial_restart is enabled, use mcsat_partial_restart_level to compute the level.
      // Otherwise, perform a full restart by backtracking to the base level.
      uint32_t backtrack_level = mcsat->trail->decision_level_base;
      if (mcsat->ctx->mcsat_options.partial_restart) {
        backtrack_level = mcsat_partial_restart_level(mcsat);
      }
      if (backtrack_level == mcsat->trail->decision_level_base) {
	      mcsat->assumptions_decided_level = -1;
	      mcsat->assumption_i = 0;
      }
      mcsat_backtrack_to(mcsat, backtrack_level, false);
      mcsat->pending_requests_all.restart = false;
      (*mcsat->solver_stats.restarts) ++;
      mcsat_notify_plugins(mcsat, MCSAT_SOLVER_RESTART);
    }

    // GC
    if (mcsat->pending_requests_all.gc_calls) {
      if (trace_enabled(mcsat->ctx->trace, "mcsat")) {
        mcsat_trace_printf(mcsat->ctx->trace, "garbage collection\n");
      }
      mcsat_gc(mcsat, false);
      mcsat->pending_requests_all.gc_calls = false;
      (*mcsat->solver_stats.gc_calls) ++;
    }

    // recache target cache
    if (mcsat->pending_requests_all.recache) {
      mcsat->pending_requests_all.recache = false;
      trail_recache(mcsat->trail, (*mcsat->solver_stats.recaches));
      (*mcsat->solver_stats.recaches) ++;
    }

    // All services
    mcsat->pending_requests = false;
  }
}

/**
 * Perform propagation by running all plugins in sequence. Stop if a conflict
 * is encountered.
 */
static
bool mcsat_propagate(mcsat_solver_t* mcsat, bool run_learning) {

  assert(int_queue_is_empty(&mcsat->registration_queue));

  uint32_t plugin_i;
  plugin_t* plugin;
  plugin_trail_token_t prop_token;
  bool someone_propagated;

  do {
    // Repeat until no plugin makes any progress
    someone_propagated = false;
    // Propagate with all the plugins in turn
    for (plugin_i = 0; mcsat_is_consistent(mcsat) && plugin_i < mcsat->plugins_count; ++ plugin_i) {
      if (trace_enabled(mcsat->ctx->trace, "mcsat::propagate")) {
        mcsat_trace_printf(mcsat->ctx->trace, "mcsat_propagate(): propagating with %s\n", mcsat->plugins[plugin_i].plugin_name);
      }
      // Make the token
      trail_token_construct(&prop_token, mcsat->plugins[plugin_i].plugin_ctx, variable_null);
      // Propagate
      plugin = mcsat->plugins[plugin_i].plugin;
      if (plugin->propagate) {
        plugin->propagate(plugin, (trail_token_t*) &prop_token);
      }
      if (prop_token.used > 0) {
        someone_propagated = true;
      }
    }
    // If at base level, plugins can do some more expensive learning/propagation
    if (run_learning && !someone_propagated && trail_is_at_base_level(mcsat->trail)) {
      // Propagate with all the plugins in turn
      for (plugin_i = 0; mcsat_is_consistent(mcsat) && plugin_i < mcsat->plugins_count; ++ plugin_i) {
        if (trace_enabled(mcsat->ctx->trace, "mcsat::propagate")) {
          mcsat_trace_printf(mcsat->ctx->trace, "mcsat_propagate(): learning with %s\n", mcsat->plugins[plugin_i].plugin_name);
        }
        // Make the token
        trail_token_construct(&prop_token, mcsat->plugins[plugin_i].plugin_ctx, variable_null);
        // Propagate
        plugin = mcsat->plugins[plugin_i].plugin;
        if (plugin->learn) {
          plugin->learn(plugin, (trail_token_t*) &prop_token);
        }
        if (prop_token.used > 0) {
          someone_propagated = true;
        }
      }
    }
  } while (someone_propagated && mcsat_is_consistent(mcsat));

  return someone_propagated;
}

static
void mcsat_assert_formula(mcsat_solver_t* mcsat, term_t f) {

  term_t f_pos;
  variable_t f_pos_var;

  if (trace_enabled(mcsat->ctx->trace, "mcsat")) {
    mcsat_trace_printf(mcsat->ctx->trace, "mcsat_assert_formula()\n");
    trace_term_ln(mcsat->ctx->trace, mcsat->terms, f);
  }

  // If we're unsat, no more assertions
  if (!mcsat_is_consistent(mcsat)) {
    return;
  }

  (*mcsat->solver_stats.assertions) ++;

  assert(trail_is_at_base_level(mcsat->trail));
  assert(int_queue_is_empty(&mcsat->registration_queue));

  // Add the terms
  f_pos = unsigned_term(f);
  f_pos_var = variable_db_get_variable(mcsat->var_db, f_pos);
  mcsat_process_registration_queue(mcsat);

  // Remember the assertion
  ivector_push(&mcsat->assertion_vars, f_pos_var);

  // Assert the formula
  if (f_pos == f) {
    // f = true
    if (!trail_has_value(mcsat->trail, f_pos_var)) {
      trail_add_propagation(mcsat->trail, f_pos_var, &mcsat_value_true, MCSAT_MAX_PLUGINS, mcsat->trail->decision_level);
    } else {
      // If negative already, we're inconsistent
      if (!trail_get_boolean_value(mcsat->trail, f_pos_var)) {
        trail_set_inconsistent(mcsat->trail);
        return;
      }
    }
  } else {
    // f = false
    if (!trail_has_value(mcsat->trail, f_pos_var)) {
      trail_add_propagation(mcsat->trail, f_pos_var, &mcsat_value_false, MCSAT_MAX_PLUGINS, mcsat->trail->decision_level);
    } else {
      // If positive already, we're inconsistent
      if (trail_get_boolean_value(mcsat->trail, f_pos_var)) {
        trail_set_inconsistent(mcsat->trail);
        return;
      }
    }
  }

  // Do propagation
  mcsat_propagate(mcsat, false);
}

/**
 * Decide one of the unassigned literals. Decide the first literal that is bigger
 * than the given bound (to make sure we decide on t(x) instead of x).
 */
static
bool mcsat_decide_one_of(mcsat_solver_t* mcsat, ivector_t* literals, term_t bound) {

  uint32_t i, unassigned_count;
  term_t literal;
  term_t literal_pos;
  variable_t literal_var;

  term_t to_decide_lit = NULL_TERM;
  term_t to_decide_atom = NULL_TERM;
  variable_t to_decide_var = variable_null;

  for (i = 0, unassigned_count = 0; i < literals->size; ++ i) {

    literal = literals->data[i];
    literal_pos = unsigned_term(literal);
    literal_var = variable_db_get_variable_if_exists(mcsat->var_db, literal_pos);

    assert(literal_var != variable_null);

    if (trace_enabled(mcsat->ctx->trace, "mcsat::lemma")) {
      mcsat_trace_printf(mcsat->ctx->trace, "trying undecided :\n");
      trace_term_ln(mcsat->ctx->trace, mcsat->ctx->terms, literal);
    }

    // Can be decided?
    if (!trail_has_value(mcsat->trail, literal_var)) {
      unassigned_count ++;
      if (trace_enabled(mcsat->ctx->trace, "mcsat::lemma")) {
        mcsat_trace_printf(mcsat->ctx->trace, "unassigned!\n");
      }
      if (bound == NULL_TERM || literal_pos > bound) {
        to_decide_lit = literal;
        to_decide_atom = literal_pos;
        to_decide_var = literal_var;
        break;
      }
    } else {
      if (trace_enabled(mcsat->ctx->trace, "mcsat::lemma")) {
        mcsat_trace_printf(mcsat->ctx->trace, "assigned!\n");
      }
    }
  }

  if (to_decide_var != variable_null) {
    if (trace_enabled(mcsat->ctx->trace, "mcsat::lemma")) {
      mcsat_trace_printf(mcsat->ctx->trace, "picked:\n");
      trace_term_ln(mcsat->ctx->trace, mcsat->ctx->terms, to_decide_lit);
    }
    mcsat_push_internal(mcsat);
    const mcsat_value_t* value = to_decide_atom == to_decide_lit ? &mcsat_value_true : &mcsat_value_false;
    trail_add_decision(mcsat->trail, to_decide_var, value, MCSAT_MAX_PLUGINS);
    return true;
  } else {
    if (unassigned_count > 0) {
      // Couldn't find a bound decision, do arbitrary
      return mcsat_decide_one_of(mcsat, literals, NULL_TERM);
    }
    return false;
  }
}

/**
 * Add a lemma (a disjunction). Each lemma needs to lead to some progress. This
 * means that:
 *  * no literal should evaluate to true
 *  * if only one literal is false, it should be propagated by one of the plugins
 *  * if more then one literals is false, one of them should be decided to true
 *    by one of the plugins
 */
static
void mcsat_add_lemma(mcsat_solver_t* mcsat, ivector_t* lemma, term_t decision_bound) {

  uint32_t i, level, top_level;
  ivector_t unassigned;
  term_t disjunct, disjunct_pos;
  variable_t disjunct_pos_var;
  plugin_t* plugin;

  (*mcsat->solver_stats.lemmas)++;

  // assert(int_queue_is_empty(&mcsat->registration_queue));
  // TODO: revisit this. it's done in integer solver to do splitting in
  // conflict analysis

  if (trace_enabled(mcsat->ctx->trace, "mcsat::lemma")) {
    mcsat_trace_printf(mcsat->ctx->trace, "lemma:\n");
    for (i = 0; i < lemma->size; ++ i) {
      mcsat_trace_printf(mcsat->ctx->trace, "\t");
      trace_term_ln(mcsat->ctx->trace, mcsat->ctx->terms, lemma->data[i]);
    }
    trail_print(mcsat->trail, trace_out(mcsat->ctx->trace));
  }

  init_ivector(&unassigned, 0);

  top_level = mcsat->trail->decision_level_base;
  for (i = 0; i < lemma->size; ++ i) {

    // Get the variables for the disjunct
    disjunct = lemma->data[i];
    assert(term_type_kind(mcsat->terms, disjunct) == BOOL_TYPE);
    disjunct_pos = unsigned_term(disjunct);
    disjunct_pos_var = variable_db_get_variable(mcsat->var_db, disjunct_pos);
    if (trace_enabled(mcsat->ctx->trace, "mcsat::lemma")) {
      mcsat_trace_printf(mcsat->ctx->trace, "literal: ");
      variable_db_print_variable(mcsat->var_db, disjunct_pos_var, stderr);
      if (trail_has_value(mcsat->trail, disjunct_pos_var)) {
        mcsat_trace_printf(mcsat->ctx->trace, "\nvalue: ");
        const mcsat_value_t* value = trail_get_value(mcsat->trail, disjunct_pos_var);
        mcsat_value_print(value, stderr);
        mcsat_trace_printf(mcsat->ctx->trace, "\n");
      } else {
        mcsat_trace_printf(mcsat->ctx->trace, "\nno value\n");
      }
    }

    // Process any newly registered variables
    mcsat_process_registration_queue(mcsat);

    // Check if the literal has value (only negative allowed)
    if (trail_has_value(mcsat->trail, disjunct_pos_var)) {
      assert(trail_get_value(mcsat->trail, disjunct_pos_var)->type == VALUE_BOOLEAN);
      assert(trail_get_value(mcsat->trail, disjunct_pos_var)->b == (disjunct != disjunct_pos));
      level = trail_get_level(mcsat->trail, disjunct_pos_var);
      if (level > top_level) {
        top_level = level;
      }
    } else {
      ivector_push(&unassigned, lemma->data[i]);
    }
  }

  assert(unassigned.size > 0);
  assert(top_level <= mcsat->trail->decision_level);

  // Backtrack to the appropriate level and do some progress
  if (unassigned.size == 1) {
    // UIP, just make sure we're not going below assumptions
    if ((int32_t) top_level >= mcsat->assumptions_decided_level) {
      mcsat_backtrack_to(mcsat, top_level, false);
    }
  } else {
    // Non-UIP, we're already below, and we'll split on a new term, that's enough
  }

  uint32_t old_trail_size = mcsat->trail->elements.size;

  // Notify the plugins about the lemma
  for (i = 0; i < mcsat->plugins_count; ++ i) {
    plugin = mcsat->plugins[i].plugin;
    if (plugin->new_lemma_notify) {
      // Make the token
      plugin_trail_token_t prop_token;
      trail_token_construct(&prop_token, mcsat->plugins[i].plugin_ctx, variable_null);
      plugin->new_lemma_notify(plugin, lemma, (trail_token_t*) &prop_token);
    }
  }

  // Propagate any
  mcsat_propagate(mcsat, false);
  bool propagated = old_trail_size < mcsat->trail->elements.size;

  // Decide a literal if necessary. At this point, if it was UIP they are all
  // assigned. If not, we assign arbitrary.
  bool decided = false;
  bool consistent = mcsat_is_consistent(mcsat);
  if (consistent) {
    decided = mcsat_decide_one_of(mcsat, &unassigned, decision_bound);
  }
  if(trace_enabled(mcsat->ctx->trace, "mcsat::lemma") && !(propagated || !consistent || decided)) {
    trail_print(mcsat->trail, trace_out(mcsat->ctx->trace));
  }
  assert(propagated || !consistent || decided);

  delete_ivector(&unassigned);
}

uint32_t mcsat_get_lemma_weight(mcsat_solver_t* mcsat, const ivector_t* lemma, lemma_weight_type_t type) {
  uint32_t i, weight = 0;
  term_t atom;
  variable_t atom_var;
  int_mset_t levels;

  switch(type) {
  case LEMMA_WEIGHT_UNIT:
    weight = 1;
    break;
  case LEMMA_WEIGHT_SIZE:
    weight = lemma->size;
    break;
  case LEMMA_WEIGHT_GLUE:
    int_mset_construct(&levels, UINT32_MAX);
    for (i = 0; i < lemma->size; ++ i) {
      atom = unsigned_term(lemma->data[i]);
      atom_var = variable_db_get_variable_if_exists(mcsat->var_db, atom);
      assert(atom_var != variable_null);
      if (trail_has_value(mcsat->trail, atom_var)) {
        int_mset_add(&levels, trail_get_level(mcsat->trail, atom_var));
      }
    }
    weight = int_mset_get_list(&levels)->size;
    int_mset_destruct(&levels);
    break;
  }

  return weight;
}

/** Check propagation with Yices: reasons => x = subst */
static
void propagation_check(const ivector_t* reasons, term_t x, term_t subst) {
  ctx_config_t* config = yices_new_config();
   context_t* ctx = yices_new_context(config);
   uint32_t i;
   for (i = 0; i < reasons->size; ++i) {
     term_t literal = reasons->data[i];
     int32_t ret = yices_assert_formula(ctx, literal);
     if (ret != 0) {
       // unsupported by regular yices
       fprintf(stderr, "skipping propagation (ret 1)\n");
       yices_print_error(stderr);
       return;
     }
   }
   term_t eq = yices_eq(x, subst);
   int32_t ret = yices_assert_formula(ctx, opposite_term(eq));
   if (ret != 0) {
     fprintf(stderr, "skipping propagation (ret 2)\n");
     yices_print_error(stderr);
     return;
   }
   smt_status_t result = yices_check_context(ctx, NULL);
   (void) result;
   assert(result == STATUS_UNSAT);
   yices_free_context(ctx);
   yices_free_config(config);
}

static
uint32_t mcsat_compute_backtrack_level(mcsat_solver_t* mcsat, uint32_t level) {
  uint32_t backtrack_level = mcsat->trail->decision_level_base;
  if (backtrack_level < level)
    backtrack_level = level;
  if ((int32_t) backtrack_level <= mcsat->assumptions_decided_level)
    backtrack_level = mcsat->assumptions_decided_level;
  return backtrack_level;
}

/**
 * Input: literals that can evaluate to true (or false if negated)
 * Output: simplified literals that can evaluate to true and imply the input literals
 */
static
void mcsat_simplify_literals(mcsat_solver_t* mcsat, ivector_t* literals, bool literals_negated, ivector_t* out_literals) {
  uint32_t i;
  for (i = 0; i < literals->size; ++ i) {
    term_t disjunct = literals->data[i];
    if (literals_negated) {
      disjunct = opposite_term(disjunct);
    }
    term_kind_t kind = term_kind(mcsat->terms, disjunct);
    if (int_hset_member(&mcsat->internal_kinds, kind)) {
      uint32_t kind_i = kind;
      bool simplified = false;
      for (; !simplified && mcsat->kind_owners[kind_i] != MCSAT_MAX_PLUGINS; kind_i += NUM_TERM_KINDS) {
        plugin_t* plugin = mcsat->plugins[mcsat->kind_owners[kind_i]].plugin;
        if (plugin->simplify_conflict_literal) {
          simplified = plugin->simplify_conflict_literal(plugin, disjunct, out_literals);
        }
      }
      assert(simplified);
    } else {
      ivector_push(out_literals, disjunct);
    }
  }
}

static
term_t mcsat_analyze_final(mcsat_solver_t* mcsat, conflict_t* input_conflict) {

  variable_t var;
  plugin_t* plugin = NULL;
  //  uint32_t plugin_i = MCSAT_MAX_PLUGINS; // BD: infer dead store
  uint32_t plugin_i;
  tracer_t* trace = mcsat->ctx->trace;
  term_t substitution;

  // First we try to massage the conflict into presentable form
  ivector_t literals;
  init_ivector(&literals, 0);
  conflict_get_negated_literals(input_conflict, &literals);

  ivector_t reason_literals;
  init_ivector(&reason_literals, 0);

  assert(mcsat->trail->elements.size > 0);

  mcsat_trail_t* trail = mcsat->trail;

  conflict_t conflict;
  conflict_construct(&conflict, &literals, false, (mcsat_evaluator_interface_t*) &mcsat->evaluator, mcsat->var_db, trail, &mcsat->tm, trace);

  // We save the trail, and then restore at the end
  mcsat_trail_t saved_trail;
  trail_construct_copy(&saved_trail, mcsat->trail);

  // Analyze while at least one variable at conflict level
  while (trail_size(mcsat->trail) > 0) {

    // Variable we might be resolving
    var = trail_back(mcsat->trail);

    if (trace_enabled(trace, "mcsat::conflict")) {
      mcsat_trace_printf(trace, "current trail:\n");
      trail_print(trail, trace->file);
      mcsat_trace_printf(trace, "current conflict: ");
      conflict_print(&conflict, trace->file);
      mcsat_trace_printf(trace, "var: ");
      variable_db_print_variable(mcsat->var_db, var, trace->file);
      mcsat_trace_printf(trace, "\n");
    }

    // Skip decisions
    if (trail_get_assignment_type(mcsat->trail, var) == DECISION) {
      trail_pop_decision(mcsat->trail);
      conflict_recompute_level_info(&conflict);
      continue;
    }

    // Skip the conflict variable (it was propagated)
    if (var == mcsat->variable_in_conflict) {
      trail_pop_propagation(mcsat->trail);
      conflict_recompute_level_info(&conflict);
      continue;
    }

    if (conflict_contains(&conflict, var)) {
      // Get the plugin that performed the propagation
      plugin_i = trail_get_source_id(trail, var);
      if (plugin_i != MCSAT_MAX_PLUGINS) {
        plugin = mcsat->plugins[plugin_i].plugin;
      } else {
        plugin = NULL;
      }

      if (trace_enabled(trace, "mcsat::conflict")) {
        mcsat_trace_printf(trace, "resolving ");
        variable_db_print_variable(mcsat->var_db, var, trace->file);
        if (plugin) {
          mcsat_trace_printf(trace, " with %s\n", mcsat->plugins[plugin_i].plugin_name);
        } else {
          mcsat_trace_printf(trace, " with assertion\n");
        }
        mcsat_trace_printf(trace, "current conflict:\n");
        conflict_print(&conflict, trace->file);
      }

      // Resolve the variable
      ivector_reset(&literals);
      if (plugin) {
        assert(plugin->explain_propagation);
        substitution = plugin->explain_propagation(plugin, var, &literals);
      } else {
        bool value = trail_get_boolean_value(trail, var);
        substitution = value ? true_term : false_term;
      }
      conflict_resolve_propagation(&conflict, var, substitution, &literals);
    } else {
      // Continue with resolution
      trail_pop_propagation(mcsat->trail);
    }
  }

  if (trace_enabled(trace, "mcsat::conflict")) {
    mcsat_trace_printf(trace, "final conflict:\n");
    conflict_print(&conflict, trace->file);
  }

  // Restore the trail
  mcsat_trail_t tmp;
  tmp = *mcsat->trail;
  *mcsat->trail = saved_trail;
  saved_trail = tmp;
  trail_destruct(&saved_trail);

  // Simplify the conflict literals
  ivector_t* final_literals = conflict_get_literals(&conflict);
  ivector_reset(&literals);
  mcsat_simplify_literals(mcsat, final_literals, true, &literals);

  // Construct the interpolant
  term_t interpolant = literals.size == 0 ? true_term : mk_and(&mcsat->tm, literals.size, literals.data);
  interpolant = opposite_term(interpolant);

  if (trace_enabled(trace, "mcsat::interpolant::check")) {
    value_t v = model_get_term_value(mcsat->assumptions_model, interpolant);
    bool interpolant_is_false = is_false(&mcsat->assumptions_model->vtbl, v);
    if (!interpolant_is_false) {
      fprintf(trace_out(trace), "model:\n");
      model_print(trace_out(trace), mcsat->assumptions_model);
      fprintf(trace_out(trace), "interpolant:\n");
      trace_term_ln(trace, conflict.terms, interpolant);
    }
    assert(interpolant_is_false);
  }

  // Remove temps
  delete_ivector(&literals);
  delete_ivector(&reason_literals);
  conflict_destruct(&conflict);

  if (trace_enabled(trace, "mcsat::conflict")) {
    mcsat_trace_printf(trace, "interpolant:\n");
    trace_term_ln(trace, conflict.terms, interpolant);
  }

  return interpolant;
}

static
bool mcsat_conflict_with_assumptions(mcsat_solver_t* mcsat, uint32_t conflict_level) {
  // If we decided some assumptions, then backtracked under that level
  if ((int32_t) conflict_level <= mcsat->assumptions_decided_level) {
    return true;
  }
  // If we haven't decided any assumptions yet but there is a conflict
  if (trail_is_at_base_level(mcsat->trail) && mcsat->assumption_vars.size > 0) {
    return true;
  }
  return false;
}

static
void mcsat_analyze_conflicts(mcsat_solver_t* mcsat, uint32_t* restart_resource) {

  conflict_t conflict;
  plugin_t* plugin = NULL;
  uint32_t plugin_i = MCSAT_MAX_PLUGINS;
  tracer_t* trace;

  uint32_t conflict_level, backtrack_level;
  variable_t var;

  term_t decision_bound = NULL_TERM;

  ivector_t reason;
  term_t substitution;

  ivector_t* conflict_disjuncts;

  init_ivector(&reason, 0);
  trace = mcsat->ctx->trace;

  // Plugin that's in conflict
  if (mcsat->plugin_in_conflict) {
    plugin_i = mcsat->plugin_in_conflict->ctx.plugin_id;
    plugin = mcsat->plugins[plugin_i].plugin;
  }

  if (trace_enabled(trace, "mcsat::conflict")) {
    if (plugin_i != MCSAT_MAX_PLUGINS) {
      mcsat_trace_printf(trace, "analyzing conflict from %s\n", mcsat->plugins[plugin_i].plugin_name);
    } else {
      mcsat_trace_printf(trace, "analyzing conflict from assertion\n");
    }
    mcsat_trace_printf(trace, "trail: ");
    trail_print(mcsat->trail, trace->file);
  }

  // Get the initial conflict
  if (mcsat->variable_in_conflict != variable_null) {
    // This conflict happened because an assumption conflicts with an already
    // propagated value. We're unsat here, but we need to produce a clause
    if (mcsat->ctx->mcsat_options.model_interpolation) {
      if (plugin) {
        term_t t = plugin->explain_propagation(plugin, mcsat->variable_in_conflict, &reason);
        term_t x = variable_db_get_term(mcsat->var_db, mcsat->variable_in_conflict);
        term_t x_eq_t = mk_eq(&mcsat->tm, x, t);
        // reason => x_eq_t is valid
        // reason && x_eq_t evaluates to false with assumptions
        // but x_eq_t evaluates to true with trail
        ivector_push(&reason, opposite_term(x_eq_t));
        conflict_construct(&conflict, &reason, false, (mcsat_evaluator_interface_t*) &mcsat->evaluator, mcsat->var_db, mcsat->trail, &mcsat->tm, mcsat->ctx->trace);
        mcsat->interpolant = mcsat_analyze_final(mcsat, &conflict);
        conflict_destruct(&conflict);
      } else {
        // an assertion, interpolant is !assertion
        mcsat->interpolant = variable_db_get_term(mcsat->var_db, mcsat->variable_in_conflict);
        bool value = trail_get_boolean_value(mcsat->trail, mcsat->variable_in_conflict);
        if (!value) {
          mcsat->interpolant = opposite_term(mcsat->interpolant);
        }
      }
    }
    mcsat->status = STATUS_UNSAT;
    mcsat->variable_in_conflict = variable_null;
    delete_ivector(&reason);
    return;
  } else {
    assert(plugin->get_conflict);
    plugin->get_conflict(plugin, &reason);
  }

  // Construct the conflict
  conflict_construct(&conflict, &reason, true, (mcsat_evaluator_interface_t*) &mcsat->evaluator, mcsat->var_db, mcsat->trail, &mcsat->tm, mcsat->ctx->trace);
  if (trace_enabled(trace, "mcsat::conflict::check")) {
    // Don't check bool conflicts: they are implied by the formula (clauses)
    if (plugin_i != mcsat->bool_plugin_id) {
      conflict_check(&conflict);
    }
  }
  statistic_avg_add(mcsat->solver_stats.avg_conflict_size, conflict.disjuncts.element_list.size);

  if (trace_enabled(trace, "mcsat::conflict") || trace_enabled(trace, "mcsat::lemma")) {
    mcsat_trace_printf(trace, "conflict from %s\n", mcsat->plugins[plugin_i].plugin_name);
    conflict_print(&conflict, trace->file);
  }

  // Get the level of the conflict and backtrack to it
  conflict_level = conflict_get_level(&conflict);
  // Backtrack max(base, assumptions, conflict)
  backtrack_level = mcsat_compute_backtrack_level(mcsat, conflict_level);
  mcsat_backtrack_to(mcsat, backtrack_level, false);

  // Analyze while at least one variable at conflict level
  while (true) {

    if (mcsat_conflict_with_assumptions(mcsat, conflict_level)) {
      // Resolved below assumptions, we're done
      break;
    }

    if (conflict_level <= mcsat->trail->decision_level_base) {
      // Resolved all the way
      break;
    }

    if (conflict_get_top_level_vars_count(&conflict) == 1) {
      // UIP-like situation, we can quit as long as we make progress, as in
      // the following cases:
      //
      // Assume finite basis B, with max{ term_size(t) | t in B } = M
      //
      // Termination based on weight(trail) = [..., weight(e), ...]
      // - weight(propagation) = M + 1
      // - weight(t -> d) = term_size(t)
      //
      // Max lex trail assuming finite basis:
      // - [prop, ..., prop, decide variables/terms by term size]
      //
      // Termination, after we resolve, the weight goes up:
      //
      // Examples:
      //   weight([b  , x -> T, y -> 0, (y + x < 0) -> 0]) =
      //          [M+1, 1     , 1     , 5]
      //
      // [backjump-learn]
      //   - Only one conflict literal contains the top variable.
      //   * weight increases by replacing decision with propagation (M+1)
      // [backjump-decide]
      //   - More then one conflict literal contains the top variable.
      //   - Top variable is decision t1 -> v
      //   - Replace with decision t2 -> v where t2 is larger than t1
      //   * weight increases by replacing decision with a heavier decision
      ivector_t* conflict_top_vars = conflict_get_variables(&conflict);
      assert(conflict_top_vars->size == 1);
      variable_t top_var = conflict_top_vars->data[0];
      if (trace_enabled(trace, "mcsat::conflict")) {
        mcsat_trace_printf(trace, "potential UIP:\n");
        variable_db_print_variable(mcsat->var_db, top_var, trace_out(trace));
        mcsat_trace_printf(trace, "conflict:\n");
        conflict_print(&conflict, trace->file);
        mcsat_trace_printf(trace, "trail:\n");
        trail_print(mcsat->trail, trace_out(trace));
      }
      // [backjump-learn]
      uint32_t top_var_lits = conflict_get_literal_count_of(&conflict, top_var);
      if (top_var_lits == 1) break;
      // [backjump-decide]
      assignment_type_t top_var_type = trail_get_assignment_type(mcsat->trail, top_var);
      if (top_var_type == DECISION) {
        // assert(variable_db_get_term(mcsat->var_db, top_var) < conflict_get_max_literal_of(&conflict, top_var));
        decision_bound = variable_db_get_term(mcsat->var_db, top_var);
        break;
      }
    }

    if (trace_enabled(trace, "mcsat::conflict")) {
      mcsat_trace_printf(trace, "current trail:\n");
      trail_print(mcsat->trail, trace->file);
      mcsat_trace_printf(trace, "current conflict: ");
      conflict_print(&conflict, trace->file);
    }

    // Current variable
    var = trail_back(mcsat->trail);
    assert(trail_get_assignment_type(mcsat->trail, var) != DECISION);

    // Resolve if in the conflict and current level
    if (conflict_contains(&conflict, var)) {

      // Get the plugin that performed the propagation
      plugin_i = trail_get_source_id(mcsat->trail, var);
      plugin = mcsat->plugins[plugin_i].plugin;

      if (trace_enabled(trace, "mcsat::conflict")) {
        mcsat_trace_printf(trace, "resolving ");
        variable_db_print_variable(mcsat->var_db, var, trace->file);
        mcsat_trace_printf(trace, " with %s\n", mcsat->plugins[plugin_i].plugin_name);
        mcsat_trace_printf(trace, "current conflict:\n");
        conflict_print(&conflict, trace->file);
      }

      // Resolve the variable
      ivector_reset(&reason);
      assert(plugin->explain_propagation);
      substitution = plugin->explain_propagation(plugin, var, &reason);
      if (trace_enabled(trace, "mcsat::propagation::check")) {
        if (plugin_i != mcsat->bool_plugin_id) {
          term_t var_term = variable_db_get_term(mcsat->var_db, var);
          propagation_check(&reason, var_term, substitution);
        } else {
//          fprintf(stderr, "skipping propagation (bool)\n");
        }
      }
      conflict_resolve_propagation(&conflict, var, substitution, &reason);
      // The trail pops with the resolution step
    } else {
      // Have to pop the trail manually
      trail_pop_propagation(mcsat->trail);
      assert(!conflict_contains_as_top(&conflict, var));
    }

    if (conflict_get_top_level_vars_count(&conflict) == 0) {
      // We have resolved the conflict even lower
      conflict_recompute_level_info(&conflict);
      conflict_level = conflict_get_level(&conflict);
      backtrack_level = mcsat_compute_backtrack_level(mcsat, conflict_level);
      mcsat_backtrack_to(mcsat, backtrack_level, false);
    }
  }

  if (trace_enabled(trace, "mcsat::conflict")) {
    mcsat_trace_printf(trace, "current conflict: ");
    conflict_print(&conflict, trace->file);
  }

  if (mcsat_conflict_with_assumptions(mcsat, conflict_level)) {
    mcsat->status = STATUS_UNSAT;
    if (mcsat->ctx->mcsat_options.model_interpolation) {
      mcsat->interpolant = mcsat_analyze_final(mcsat, &conflict);
    }
    mcsat->assumptions_decided_level = -1;
    mcsat_backtrack_to(mcsat, mcsat->trail->decision_level_base, false);
  } else if (conflict_level <= mcsat->trail->decision_level_base) {
    mcsat->status = STATUS_UNSAT;
  } else {
    assert(conflict_get_top_level_vars_count(&conflict) == 1);
    // We should still be in conflict, so back out
    assert(conflict.level == mcsat->trail->decision_level);
    mcsat_backtrack_to(mcsat, mcsat->trail->decision_level - 1, true);

    // Get the literals
    conflict_disjuncts = conflict_get_literals(&conflict);

    if (trace_enabled(trace, "mcsat::conflict")) {
      mcsat_trace_printf(trace, "conflict_disjuncts:\n");
      uint32_t i;
      for (i = 0; i < conflict_disjuncts->size; ++i) {
        mcsat_trace_printf(trace, "[%u]: ", i);
        trace_term_ln(trace, mcsat->ctx->terms, conflict_disjuncts->data[i]);
      }
    }

    // Now add the lemma
    mcsat_add_lemma(mcsat, conflict_disjuncts, decision_bound);

    // Use resources based on conflict size
    *restart_resource += mcsat_get_lemma_weight(mcsat, conflict_disjuncts,
        mcsat->heuristic_params.lemma_restart_weight_type);

    // Bump the variables
    mcsat_bump_variables_mset(mcsat, conflict_get_variables_all(&conflict));

    if (trace_enabled(trace, "mcsat::conflict::trail")) {
      mcsat_trace_printf(trace, "trail: ");
      trail_print(mcsat->trail, trace->file);
    }
  }

  delete_ivector(&reason);
  conflict_destruct(&conflict);
}

static
bool mcsat_decide_assumption(mcsat_solver_t* mcsat, model_t* mdl, uint32_t n_assumptions, const term_t assumptions[]) {
  assert(!mcsat->trail->inconsistent);

  variable_t var;
  term_t var_term;
  mcsat_value_t var_mdl_value;

  uint32_t plugin_i;
  plugin_t* plugin;

  plugin_trail_token_t decision_token;

  bool assumption_decided = false;
  for (; !assumption_decided && mcsat->assumption_i < n_assumptions; mcsat->assumption_i ++) {

    // Break if any conflicts
    if (mcsat->trail->inconsistent) {
      break;
    }
    if (mcsat->variable_in_conflict != variable_null) {
      break;
    }

    // The variable (should exist already)
    var_term = assumptions[mcsat->assumption_i];
    var = variable_db_get_variable_if_exists(mcsat->var_db, var_term);
    assert(var != variable_null);
    // Get the owner that will 'decide' the value of the variable
    plugin_i = mcsat->decision_makers[variable_db_get_type_kind(mcsat->var_db, var)];
    assert(plugin_i != MCSAT_MAX_PLUGINS);
    // The given value the variable in the provided model
    value_t value = model_get_term_value(mdl, var_term);
    mcsat_value_construct_from_value(&var_mdl_value, &mdl->vtbl, value);

    if (trace_enabled(mcsat->ctx->trace, "mcsat::decide")) {
      mcsat_trace_printf(mcsat->ctx->trace, "mcsat_decide_assumption(): with %s\n", mcsat->plugins[plugin_i].plugin_name);
      mcsat_trace_printf(mcsat->ctx->trace, "mcsat_decide_assumption(): variable ");
      variable_db_print_variable(mcsat->var_db, var, trace_out(mcsat->ctx->trace));
      mcsat_trace_printf(mcsat->ctx->trace, "\n");
    }

    // If the variable already has a value in the trail check for consistency
    if (trail_has_value(mcsat->trail, var)) {
      // If the value is different from given value, we are in conflict
      assert(trail_get_assignment_type(mcsat->trail, var) == PROPAGATION);
      const mcsat_value_t* var_trail_value = trail_get_value(mcsat->trail, var);
      bool eq = mcsat_value_eq(&var_mdl_value, var_trail_value);
      if (!eq) {
        // Who propagated the value (MCSAT_MAX_PLUGINS if an assertion)
        plugin_i = trail_get_source_id(mcsat->trail, var);
        if (plugin_i == MCSAT_MAX_PLUGINS) {
          mcsat->plugin_in_conflict = NULL;
        } else {
          mcsat->plugin_in_conflict = mcsat->plugins[plugin_i].plugin_ctx;
        }
        mcsat->variable_in_conflict = var;
      }
    } else {
      // Plugin used to check/decide
      plugin = mcsat->plugins[plugin_i].plugin;
      // Check if the decision is consistent (will report conflict if not)
      if (!mcsat->trail->inconsistent) {
        // Construct the token
        trail_token_construct(&decision_token, mcsat->plugins[plugin_i].plugin_ctx, var);
        // Decide with the owner plugin
        mcsat_push_internal(mcsat);
        assert(plugin->decide_assignment);
        plugin->decide_assignment(plugin, var, &var_mdl_value, (trail_token_t*) &decision_token);

        // If decided, we're done
        assert(decision_token.used);
        if (trace_enabled(mcsat->ctx->trace, "mcsat::decide")) {
          FILE* out = trace_out(mcsat->ctx->trace);
          fprintf(out, "mcsat_decide_assumption(): value = ");
          mcsat_value_print(trail_get_value(mcsat->trail, var), out);
          fprintf(out, "\n");
        }
        // We've decided something!
        assumption_decided = true;
        mcsat->assumptions_decided_level = mcsat->trail->decision_level;
      }
    }

    // Remove temp
    mcsat_value_destruct(&var_mdl_value);
  }

  return assumption_decided;
}

/**
 * Finds the correct plugin for var and asks it to make a decision.
 * Returns true if a decision was made on var.
 */
static
bool mcsat_decide_var(mcsat_solver_t* mcsat, variable_t var, bool force_decision) {
  // must be a valid variable that is not yet decided upon
  assert(var != variable_null);
  assert(!trail_has_value(mcsat->trail, var));

  uint32_t i;
  plugin_t* plugin;
  plugin_trail_token_t decision_token;
  bool made_decision = false;

  // Get the owner that will decide that value of the variable
  i = mcsat->decision_makers[variable_db_get_type_kind(mcsat->var_db, var)];
  assert(i != MCSAT_MAX_PLUGINS);
  // Construct the token
  trail_token_construct(&decision_token, mcsat->plugins[i].plugin_ctx, var);
  // Decide
  if (trace_enabled(mcsat->ctx->trace, "mcsat::decide")) {
    mcsat_trace_printf(mcsat->ctx->trace, "mcsat_decide(): with %s\n", mcsat->plugins[i].plugin_name);
    mcsat_trace_printf(mcsat->ctx->trace, "mcsat_decide(): variable ");
    variable_db_print_variable(mcsat->var_db, var, trace_out(mcsat->ctx->trace));
    mcsat_trace_printf(mcsat->ctx->trace, "\n");
  }
  plugin = mcsat->plugins[i].plugin;

  // Ask the owner to decide
  mcsat_push_internal(mcsat);
  assert(plugin->decide);
  plugin->decide(plugin, var, (trail_token_t*) &decision_token, force_decision);

  if (decision_token.used == 0) {
    // If not decided, remember and go on
    made_decision = false;
    mcsat_pop_internal(mcsat);
  } else {
    made_decision = true;
    // Decided, we can continue with the search
    (*mcsat->solver_stats.decisions)++;
    // Plugins are not allowed to cheat and decide on another variable
    assert(trail_has_value(mcsat->trail, var));
    if (trace_enabled(mcsat->ctx->trace, "mcsat::decide")) {
      FILE* out = trace_out(mcsat->ctx->trace);
      fprintf(out, "mcsat_decide(): value = ");
      mcsat_value_print(trail_get_value(mcsat->trail, var), out);
      fprintf(out, "\n");
    }
  }

  // a forced decision implies a made decision
  assert(!force_decision || made_decision);
  return made_decision;
}

/**
 * Decides a variable using one of the plugins. Returns true if a variable
 * has been decided, or a conflict detected.
 */
static
bool mcsat_decide(mcsat_solver_t* mcsat) {

  assert(!mcsat->trail->inconsistent);

  ivector_t skipped_variables; // Variables we took from the queue but plugin didn't decide
  init_ivector(&skipped_variables, 0);

  variable_t var;
  bool aux_choice; // indicates that var was not taken from the queue
  bool force_decision = false;
  double rand_freq = mcsat->heuristic_params.random_decision_freq;

  while (true) {
    var = variable_null;
    aux_choice = true;

    // Use the top variables first
    for (uint32_t i = 0; i < mcsat->top_decision_vars.size; ++i) {
      var = mcsat->top_decision_vars.data[i];
      assert(var != variable_null);
      if (!trail_has_value(mcsat->trail, var)) {
        force_decision = true;
        break;
      }
      var = variable_null;
    }

    // If there is a fixed order that was passed in, try that
    if (var == variable_null) {
      const ivector_t* order = &mcsat->ctx->mcsat_var_order;
      if (order->size > 0) {
        if (trace_enabled(mcsat->ctx->trace, "mcsat::decide")) {
          FILE* out = trace_out(mcsat->ctx->trace);
          fprintf(out, "mcsat_decide(): var_order is ");
          for (uint32_t i = 0; i < order->size; ++ i) {
            term_print_to_file(out, mcsat->ctx->terms, order->data[i]);
            fprintf(out, " ");
          }
          fprintf(out, "\n");
        }
        for (uint32_t i = 0; var == variable_null && i < order->size; ++i) {
          term_t ovar_term = order->data[i];
          variable_t ovar = variable_db_get_variable_if_exists(mcsat->var_db, ovar_term);
          if (ovar == variable_null) continue; // Some variables are not used
          if (!trail_has_value(mcsat->trail, ovar)) {
            var = ovar;
            force_decision = true;
          }
        }
      }
    }

    // then try the variables a plugin requested
    if (var == variable_null) {
      while (!int_queue_is_empty(&mcsat->hinted_decision_vars)) {
        var = int_queue_pop(&mcsat->hinted_decision_vars);
        assert(var != variable_null);
        if (!trail_has_value(mcsat->trail, var)) {
          force_decision = true;
          break;
        }
        var = variable_null;
      }
    }

    // Random decision
    if (var == variable_null && rand_freq > 0.0) {
      double* seed = &mcsat->heuristic_params.random_decision_seed;
      if (drand(seed) < rand_freq && !var_queue_is_empty(&mcsat->var_queue)) {
        var = var_queue_random(&mcsat->var_queue, seed);
        if (trail_has_value(mcsat->trail, var)) {
          var = variable_null;
        }
      }
    }

    if (var == variable_null) {
      // No auxiliary choice performed
      aux_choice = false;
    }

    // Use the queue
    while (!var_queue_is_empty(&mcsat->var_queue) && var == variable_null) {
      // Get the next variable from the queue
      var = var_queue_pop(&mcsat->var_queue);
      // If already assigned go on
      if (trail_has_value(mcsat->trail, var)) {
        if (trace_enabled(mcsat->ctx->trace, "mcsat::decide")) {
          FILE *out = trace_out(mcsat->ctx->trace);
          fprintf(out, "mcsat_decide(): skipping ");
          variable_db_print_variable(mcsat->var_db, var, out);
          fprintf(out, "\n");
        }
        var = variable_null;
        continue;
      }
    }

    if (var != variable_null) {
      bool made_decision = mcsat_decide_var(mcsat, var, force_decision);
      if (made_decision) {
        break;
      } else if (!aux_choice) {
        ivector_push(&skipped_variables, var);
      }
    } else {
      assert(!aux_choice);
      // No variables left to decide
      if (skipped_variables.size == 0) {
        // Didn't skip any, we're done
        break;
      } else {
        // Put the skipped back in the queue, and continue but force next decision
        for (uint32_t i = 0; i < skipped_variables.size; ++ i) {
          var_queue_insert(&mcsat->var_queue, skipped_variables.data[i]);
        }
        ivector_reset(&skipped_variables);
        force_decision = true;
      }
    }
  }

  // Put any skipped variables back into the queue
  if (skipped_variables.size > 0) {
    // If we skipped some, we had to decided one, we put the skipped scores to
    // the decided score
    assert(var != variable_null);
    double var_score = var_queue_get_activity(&mcsat->var_queue, var);
    for (uint32_t i = 0; i < skipped_variables.size; ++ i) {
      variable_t skipped_var = skipped_variables.data[i];
      var_queue_set_activity(&mcsat->var_queue, skipped_var, var_score);
      var_queue_insert(&mcsat->var_queue, skipped_var);
    }
  }

  delete_ivector(&skipped_variables);

  return var != variable_null;
}

typedef struct {
  uint32_t u, v;
  uint32_t restart_threshold;
  uint32_t interval;
} luby_t;

static inline
void luby_init(luby_t* luby, uint32_t interval) {
  luby->u = 1;
  luby->v = 1;
  luby->restart_threshold = interval;
  luby->interval = interval;
}

static inline
void luby_next(luby_t* luby) {
  if ((luby->u & -luby->u) == luby->v) {
    luby->u ++;
    luby->v = 1;
  } else {
    luby->v <<= 1;
  }
  luby->restart_threshold = luby->v * luby->interval;
}

static
void mcsat_check_model(mcsat_solver_t* mcsat, bool assert) {
  // Check models
  model_t model;
  init_model(&model, mcsat->terms, true);
  mcsat_build_model(mcsat, &model);
  uint32_t i = 0;
  for (i = 0; i < mcsat->assertion_terms_original.size; ++i) {
    term_t assertion = mcsat->assertion_terms_original.data[i];
    int32_t code = 0;
    bool assertion_is_true = formula_holds_in_model(&model, assertion, &code);
    if (false && !assertion_is_true) {
      FILE *out = trace_out(mcsat->ctx->trace);
      fprintf(out, "Assertion not true in model: ");
      trace_term_ln(mcsat->ctx->trace, mcsat->terms, assertion);
      fprintf(out, "In model:\n");
      model_print(out, &model);
    }
    assert(!assert || assertion_is_true);
  }
  delete_model(&model);
}

static
void mcsat_assert_formulas_internal(mcsat_solver_t* mcsat, uint32_t n, const term_t *f, bool preprocess);

void mcsat_set_model_hint(mcsat_solver_t* mcsat, model_t* mdl, uint32_t n_mdl_filter,
			  const term_t mdl_filter[]) {
  if (n_mdl_filter == 0) {
    return;
  }

  assert(mdl != NULL);
  assert(mdl_filter != NULL);

  value_table_t* vtbl = model_get_vtbl(mdl);

  trail_clear_cache(mcsat->trail);
  trail_update_extra_cache(mcsat->trail);

  for (uint32_t i = 0; i < n_mdl_filter; ++i) {
    term_t x = mdl_filter[i];
    assert(term_kind(mcsat->terms, x) == UNINTERPRETED_TERM || term_kind(mcsat->terms, x) == VARIABLE);
    assert(is_pos_term(x));

    variable_t x_var = variable_db_get_variable(mcsat->var_db, unsigned_term(x));    
    value_t x_value = model_get_term_value(mdl, x);
    mcsat_value_t value;

    mcsat_value_construct_from_value(&value, vtbl, x_value);
    assert(x_value >= 0);

    trail_set_cached_value(mcsat->trail, x_var, &value);
  }

  mcsat_process_registration_queue(mcsat);
}

static
void mcsat_set_initial_var_order(mcsat_solver_t* mcsat) {
  const ivector_t* vars = &mcsat->ctx->mcsat_initial_var_order;
  uint32_t n = vars->size;
  if (n == 0) {
    return;
  }

  assert(vars != NULL);

  uint32_t i;
  for (i = 0; i < n; ++i) {
    term_t x = vars->data[i];
    assert(term_kind(mcsat->terms, x) == UNINTERPRETED_TERM || term_kind(mcsat->terms, x) == VARIABLE);
    variable_t v = variable_db_get_variable(mcsat->var_db, unsigned_term(x));
    int_queue_push(&mcsat->hinted_decision_vars, v);
    mcsat_process_registration_queue(mcsat);
  }
}

void mcsat_solve(mcsat_solver_t* mcsat, const param_t *params, model_t* mdl, uint32_t n_assumptions, const term_t assumptions[]) {

  uint32_t restart_resource;
  luby_t luby;

  // Make sure we have variables for all the assumptions
  if (n_assumptions > 0) {
    if (trace_enabled(mcsat->ctx->trace, "mcsat")) {
      mcsat_trace_printf(mcsat->ctx->trace, "solving with assumptions\n");
    }
    assert(mcsat->assumption_vars.size == 0);
    uint32_t i;
    for (i = 0; i < n_assumptions; ++ i) {
      // Apply the pre-processor. If the variable is substituted, we
      // need to add the equality x = t
      term_t x = assumptions[i];
      assert(term_kind(mcsat->terms, x) == UNINTERPRETED_TERM || term_kind(mcsat->terms, x) == VARIABLE);
      assert(is_pos_term(x));
      term_t x_pre = preprocessor_apply(&mcsat->preprocessor, x, NULL, true);
      if (x != x_pre) {
        // Assert x = t although we solved it already :(
        term_t eq = mk_eq(&mcsat->tm, x, x_pre);
        mcsat_assert_formulas_internal(mcsat, 1, &eq, false);
      }
      // Make sure the variable is registered (maybe it doesn't appear in assertions)
      variable_t x_var = variable_db_get_variable(mcsat->var_db, unsigned_term(x));
      ivector_push(&mcsat->assumption_vars, x_var);
      mcsat_process_registration_queue(mcsat);
    }
  }

  // Initialize assumption info
  mcsat->interpolant = NULL_TERM;
  mcsat->variable_in_conflict = variable_null;
  mcsat->assumption_i = 0;
  mcsat->assumptions_decided_level = -1;
  mcsat->assumptions_model = mdl;

  // Start the search
  mcsat->status = STATUS_SEARCHING;

  // If we're already unsat, just return
  if (!mcsat_is_consistent(mcsat)) {
    mcsat->interpolant = false_term;
    mcsat->status = STATUS_UNSAT;
    assert(int_queue_is_empty(&mcsat->registration_queue));
    goto solve_done;
  }

  if (trace_enabled(mcsat->ctx->trace, "mcsat::solve")) {
    static int count = 0;
    mcsat_trace_printf(mcsat->ctx->trace, "solve %d\n", count ++);
  }

  // Remember existing terms
  mcsat->terms_size_on_solver_entry = nterms(mcsat->terms);

  // Initialize for search
  mcsat_heuristics_init(mcsat, params);
  mcsat_notify_plugins(mcsat, MCSAT_SOLVER_START);

  // set initial variable order
  mcsat_set_initial_var_order(mcsat);

  // Initialize the Luby sequence with interval 10
  restart_resource = 0;
  luby_init(&luby, mcsat->heuristic_params.restart_interval);

  // recache parameters
  uint32_t recache_limit = (*mcsat->solver_stats.conflicts) + mcsat->heuristic_params.recache_interval;
  uint32_t recache_round = 0;

  // Whether to run learning
  bool learning = true;

  while (!mcsat->stop_search) {

    // Do we restart
    if (mcsat_is_consistent(mcsat) && restart_resource > luby.restart_threshold) {
      restart_resource = 0;
      luby_next(&luby);
      mcsat_request_restart(mcsat);

    } else if ((*mcsat->solver_stats.conflicts) > recache_limit) {
      // recache
      ++recache_round;
      mcsat_request_recache(mcsat);
      double l = log10(recache_round + 9);
      recache_limit = (*mcsat->solver_stats.conflicts) +
	(recache_round * l * l * l *  mcsat->heuristic_params.recache_interval);
    }

    // Process any outstanding requests
    mcsat_process_requests(mcsat);

    // Do propagation
    mcsat_propagate(mcsat, learning);
    learning = false;

    // If inconsistent, analyze the conflict
    if (!mcsat_is_consistent(mcsat)) {
      goto conflict;
    }

    // If any requests, process them and go again
    if (mcsat->pending_requests) {
      continue;
    }

    // Should we decide on an assumption
    bool assumption_decided = mcsat_decide_assumption(mcsat, mdl, n_assumptions, assumptions);
    if (assumption_decided) {
      continue;
    }

    // If inconsistent, analyze the conflict
    if (!mcsat_is_consistent(mcsat)) {
      goto conflict;
    }

    // Time to make a decision
    bool variable_decided = mcsat_decide(mcsat);

    // Decision made, continue with the search
    if (variable_decided) {
      continue;
    }

    // If inconsistent, analyze the conflict
    if (!mcsat_is_consistent(mcsat)) {
      goto conflict;
    }

    // Nothing to decide, we're satisfiable
    mcsat->status = STATUS_SAT;
    if (trace_enabled(mcsat->ctx->trace, "mcsat::model::check")) {
      mcsat_check_model(mcsat, true);
    }

    break;

  conflict:

    (*mcsat->solver_stats.conflicts)++;
    mcsat_notify_plugins(mcsat, MCSAT_SOLVER_CONFLICT);

    // If at level 0 we're unsat
    if (n_assumptions == 0 && trail_is_at_base_level(mcsat->trail)) {
      mcsat->interpolant = false_term;
      mcsat->status = STATUS_UNSAT;
      break;
    }

    // Analyze the conflicts
    mcsat_analyze_conflicts(mcsat, &restart_resource);

    // Analysis might have discovered base level conflict
    if (mcsat->status == STATUS_UNSAT) {
      if (n_assumptions == 0) {
        mcsat->interpolant = false_term;
      }
      break;
    }

    // update the variable selection heuristic
    var_queue_decay_activities(&mcsat->var_queue);
  }

  if (mcsat->stop_search) {
    if (mcsat->status == STATUS_SEARCHING) {
      mcsat->status = YICES_STATUS_INTERRUPTED;
    }
    mcsat->stop_search = false;
  }

  // Make sure any additional terms are registered
  mcsat_process_registration_queue(mcsat);

solve_done:

  ivector_reset(&mcsat->assumption_vars);
}

void mcsat_set_tracer(mcsat_solver_t* mcsat, tracer_t* tracer) {
  uint32_t i;
  mcsat_plugin_context_t* ctx;

  // Update the contexts with the new tracer
  variable_db_set_tracer(mcsat->var_db, tracer);
  for (i = 0; i < mcsat->plugins_count; ++ i) {
    ctx = mcsat->plugins[i].plugin_ctx;
    ctx->ctx.tracer = tracer;
  }

  // Set the trace for the preprocessor
  preprocessor_set_tracer(&mcsat->preprocessor, tracer);
}


void mcsat_flush_lemmas(mcsat_solver_t* mcsat, ivector_t* out) {
  // Flush regular lemmas
  ivector_add(out, mcsat->plugin_lemmas.data, mcsat->plugin_lemmas.size);
  ivector_reset(&mcsat->plugin_lemmas);

  // Copy definition lemmas
  uint32_t i = mcsat->plugin_definition_lemmas_i;
  for (; i < mcsat->plugin_definition_lemmas.size; ++ i) {
    ivector_push(out, mcsat->plugin_definition_lemmas.data[i]);
  }
  mcsat->plugin_definition_lemmas_i = mcsat->plugin_definition_lemmas.size;
}

static
void mcsat_assert_formulas_internal(mcsat_solver_t* mcsat, uint32_t n, const term_t *f, bool preprocess) {
  uint32_t i;

  // Remember the original assertions
  for (i = 0; i < n; ++ i) {
    ivector_push(&mcsat->assertion_terms_original, f[i]);
  }

  // Add any leftover lemmas
  ivector_t* assertions = &mcsat->assertions_tmp;
  ivector_reset(assertions);
  mcsat_flush_lemmas(mcsat, assertions);

  // Preprocess the formulas (preprocessor might throw)
  ivector_add(assertions, f, n);

  // Preprocess the formulas (preprocessor might throw)
  if (preprocess) {
    for (i = 0; i < assertions->size; ++ i) {
      term_t f = assertions->data[i];
      term_t f_pre = preprocessor_apply(&mcsat->preprocessor, f, assertions, true);
      assertions->data[i] = f_pre;
    }
  }

  // Assert individual formulas
  for (i = 0; i < assertions->size; ++ i) {
    // Assert it
    mcsat_assert_formula(mcsat, assertions->data[i]);
    // Add any lemmas that were added
    mcsat_flush_lemmas(mcsat, assertions);
  }

  // Delete the temp
  ivector_reset(assertions);
}

int32_t mcsat_assert_formulas(mcsat_solver_t* mcsat, uint32_t n, const term_t *f) {
  mcsat_assert_formulas_internal(mcsat, n, f, true);
  mcsat->interpolant = NULL_TERM;
  return CTX_NO_ERROR;
}

void mcsat_show_stats(mcsat_solver_t* mcsat, FILE* out) {
  int fd = fileno(out);
  assert(fd >= 0);
  statistics_print(&mcsat->stats, fd);
}

void mcsat_show_stats_fd(mcsat_solver_t* mcsat, int out) {
  statistics_print(&mcsat->stats, out);
}

void mcsat_build_model(mcsat_solver_t* mcsat, model_t* model) {

  value_table_t* vtbl = model_get_vtbl(model);

  if (trace_enabled(mcsat->ctx->trace, "mcsat")) {
    mcsat_trace_printf(mcsat->ctx->trace, "mcsat_build_model()\n");
    trail_print(mcsat->trail, trace_out(mcsat->ctx->trace));
  }

  // Just copy the trail into the model
  uint32_t i;
  ivector_t* trail_elements = &mcsat->trail->elements;
  for (i = 0; i < trail_elements->size; ++ i) {
    variable_t x = trail_elements->data[i];
    term_t x_term = variable_db_get_term(mcsat->var_db, x);
    term_kind_t x_kind = term_kind(mcsat->terms, x_term);

    if (x_kind == UNINTERPRETED_TERM &&
        term_type_kind(mcsat->terms, x_term) != FUNCTION_TYPE) {

      if (trace_enabled(mcsat->ctx->trace, "mcsat")) {
        mcsat_trace_printf(mcsat->ctx->trace, "var = ");
        trace_term_ln(mcsat->ctx->trace, mcsat->terms, x_term);
      }

      // Type of the variable
      type_t x_type = term_type(mcsat->terms, x_term);

      // Get mcsat value (have to case to remove const because yices api doesn't care for const)
      mcsat_value_t* x_value_mcsat = (mcsat_value_t*) trail_get_value(mcsat->trail, x);

      if (trace_enabled(mcsat->ctx->trace, "mcsat")) {
        mcsat_trace_printf(mcsat->ctx->trace, "value = ");
        mcsat_value_print(x_value_mcsat, trace_out(mcsat->ctx->trace));
        mcsat_trace_printf(mcsat->ctx->trace, "\n");
      }

      // Set up the yices value
      value_t x_value = mcsat_value_to_value(x_value_mcsat, mcsat->types, x_type, vtbl);

      if (trace_enabled(mcsat->ctx->trace, "mcsat")) {
        mcsat_trace_printf(mcsat->ctx->trace, "value = ");
        vtbl_print_object(trace_out(mcsat->ctx->trace), vtbl, x_value);
        mcsat_trace_printf(mcsat->ctx->trace, "\n");
      }

      // Add to model
      model_map_term(model, x_term, x_value);
    }
  }

  // Let the plugins run add to the model (e.g. UF, division, ...)
  for (i = 0; i < mcsat->plugins_count; ++ i) {
    plugin_t* plugin = mcsat->plugins[i].plugin;
    if (plugin->build_model) {
      plugin->build_model(plugin, model);
    }
  }

  // Let the preprocessor add to the model
  preprocessor_build_model(&mcsat->preprocessor, model);
}

void mcsat_set_exception_handler(mcsat_solver_t* mcsat, jmp_buf* handler) {
  uint32_t i;
  mcsat->exception = handler;
  preprocessor_set_exception_handler(&mcsat->preprocessor, handler);
  for (i = 0; i < mcsat->plugins_count; ++ i) {
    plugin_t* plugin = mcsat->plugins[i].plugin;
    plugin->set_exception_handler(plugin, handler);
  }
}

void mcsat_gc_mark(mcsat_solver_t* mcsat) {
  mcsat_clear(mcsat);
  mcsat_gc(mcsat, true);
}

void mcsat_stop_search(mcsat_solver_t* mcsat) {
  mcsat->stop_search = true;
}

term_t mcsat_get_unsat_model_interpolant(mcsat_solver_t* mcsat) {
  return mcsat->interpolant;
}
