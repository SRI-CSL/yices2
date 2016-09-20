/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "mcsat/solver.h"

#include "context/context.h"
#include "model/models.h"
#include "model/concrete_values.h"
#include "io/concrete_value_printer.h"

#include "mcsat/variable_db.h"
#include "mcsat/variable_queue.h"
#include "mcsat/trail.h"
#include "mcsat/conflict.h"
#include "mcsat/plugin.h"
#include "mcsat/tracing.h"

#include "utils/int_queues.h"
#include "utils/bitvectors.h"

#include "mcsat/bool/bool_plugin.h"
#include "mcsat/ite/ite_plugin.h"
#include "mcsat/nra/nra_plugin.h"
#include "mcsat/uf/uf_plugin.h"

#include "mcsat/preprocessor.h"

#include "mcsat/utils/statistics.h"

#include "utils/dprng.h"

#include <inttypes.h>


/**
 * Notification of new variables for the main solver.
 */
typedef struct solver_new_variable_notify_s {
  void (*new_variable) (struct solver_new_variable_notify_s* self, variable_t x);
  mcsat_solver_t* mcsat;
} solver_new_variable_notify_t;

/**
 * Context of each plugin encapsulate it's essential information, including
 * the solver itself, it's index in the solver and it's name (for debugging
 * purposes).
 */
typedef struct mcsat_plugin_context_s {
  /** The regular plugin context */
  plugin_context_t ctx;
  /** The solver reference */
  mcsat_solver_t* mcsat;
  /** Index of the plugin in the solver */
  uint32_t plugin_i;
  /** The name of the plugin */
  const char* plugin_name;
} mcsat_plugin_context_t;

/**
 * The token is passed to plugins for trail operations (propagation and
 * decisions) and encapsulates additional information for debuging purposes.
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
  bool (*evaluates) (const mcsat_evaluator_interface_t* data, term_t t, int_mset_t* vars, mcsat_value_t* value);
  /** The solver */
  mcsat_solver_t* solver;
} mcsat_evaluator_t;

struct mcsat_solver_s {

  /** Context of the solver */
  const context_t* ctx;

  /** Exception handler */
  jmp_buf* exception;

  /** Input types are are from this table */
  type_table_t* types;

  /** Input terms are from this table */
  term_table_t* terms;

  /** Size of the input table at entry to solve() */
  uint32_t terms_size_on_solver_entry;

  /** The status */
  smt_status_t status;

  /** Notifications for new variables */
  solver_new_variable_notify_t var_db_notify;

  /** Variable database */
  variable_db_t* var_db;

  /** List of assertions (positive variables). */
  ivector_t assertion_vars;

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
   * continue at indices mod MCSAT_MAX_PLUGINS.
   */
  uint32_t kind_owners[NUM_TERM_KINDS * MCSAT_MAX_PLUGINS];

  /**
   * Array of owners for each type. If there are more than one, they
   * continue at indices mod MCSAT_MAX_PLUGINS.
   */
  uint32_t type_owners[NUM_TYPE_KINDS * MCSAT_MAX_PLUGINS];

  /**
   * Array of decision makers for each type. There can be only one.
   */
  uint32_t decision_makers[NUM_TYPE_KINDS];

  /** Plugin the reported a conflict */
  mcsat_plugin_context_t* plugin_in_conflict;

  /** Lemmas reported by plugins  */
  ivector_t plugin_lemmas;

  /** Number of plugins */
  uint32_t plugins_count;

  /** The queue for variable decisions */
  var_queue_t var_queue;

  /** All pending requests */
  struct {
    bool restart;
    bool gc_calls;
  } pending_requests_all;

  /** Any pending requests */
  bool pending_requests;

  /** Statistics */
  statistics_t stats;

  struct {
    // Assertions added
    uint32_t* assertions;
    // Lemmas added
    uint32_t* lemmas;
    // Decisions performed
    uint32_t* decisions;
    // Restarts performed
    uint32_t* restarts;
    // Conflicts handled
    uint32_t* conflicts;
    // GC calls
    uint32_t* gc_calls;
  } solver_stats;

  struct {
    // Restart interval (used as multiplier in luby sequence)
    uint32_t restart_interval;
    // Type of weight to use for restart counter
    lemma_weight_type_t lemma_restart_weight_type;
    // Random decision frequency
    double random_decision_freq;
    // Random decision seed
    double random_decision_seed;
  } heuristic_params;
};

static
void mcsat_add_lemma(mcsat_solver_t* mcsat, ivector_t* lemma);

static
void mcsat_stats_init(mcsat_solver_t* mcsat) {
  mcsat->solver_stats.assertions = statistics_new_uint32(&mcsat->stats, "mcsat::assertions");
  mcsat->solver_stats.conflicts = statistics_new_uint32(&mcsat->stats, "mcsat::conflicts");
  mcsat->solver_stats.decisions = statistics_new_uint32(&mcsat->stats, "mcsat::decisions");
  mcsat->solver_stats.gc_calls = statistics_new_uint32(&mcsat->stats, "mcsat::gc_calls");
  mcsat->solver_stats.lemmas = statistics_new_uint32(&mcsat->stats, "mcsat::lemmas");
  mcsat->solver_stats.restarts = statistics_new_uint32(&mcsat->stats, "mcsat::restarts");
}

static
void mcsat_heuristics_init(mcsat_solver_t* mcsat) {
  mcsat->heuristic_params.restart_interval = 10;
  mcsat->heuristic_params.lemma_restart_weight_type = LEMMA_WEIGHT_SIZE;
  mcsat->heuristic_params.random_decision_freq = 0;
  mcsat->heuristic_params.random_decision_seed = 0;
}

bool mcsat_evaluates(const mcsat_evaluator_interface_t* self, term_t t, int_mset_t* vars, mcsat_value_t* value) {

  const mcsat_solver_t* mcsat = ((const mcsat_evaluator_t*) self)->solver;

  uint32_t i;
  term_kind_t kind;
  bool evaluates;
  plugin_t* plugin;

  kind = term_kind(mcsat->terms, t);

  if (kind != EQ_TERM) {
    for (i = kind; mcsat->kind_owners[i] != MCSAT_MAX_PLUGINS; i += MCSAT_MAX_PLUGINS) {
      int_mset_clear(vars);
      plugin = mcsat->plugins[mcsat->kind_owners[i]].plugin;
      if (plugin->explain_evaluation) {
        evaluates = plugin->explain_evaluation(plugin, t, vars, value);
        if (evaluates) {
          return true;
        }
      }
    }
  } else {
    composite_term_t* eq_desc = eq_term_desc(mcsat->terms, t);
    type_kind_t type_kind = term_type_kind(mcsat->terms, eq_desc->arg[0]);
    for (i = type_kind; mcsat->type_owners[i] != MCSAT_MAX_PLUGINS; i += MCSAT_MAX_PLUGINS) {
      int_mset_clear(vars);
      plugin = mcsat->plugins[mcsat->type_owners[i]].plugin;
      if (plugin->explain_evaluation) {
        evaluates = plugin->explain_evaluation(plugin, t, vars, value);
        if (evaluates) {
          return true;
        }
      }
    }
  }

  return false;
}

/** Construct the mcsat evaluator */
void mcsat_evaluator_construct(mcsat_evaluator_t* evaluator, mcsat_solver_t* solver) {
  evaluator->evaluates = mcsat_evaluates;
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
    trail_add_decision(trail, x, value, tk->ctx->plugin_i);
  } else {
    trail_add_propagation(trail, x, value, tk->ctx->plugin_i, trail->decision_level);
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

  // Add the propagation
  trail_add_propagation(trail, x, value, tk->ctx->plugin_i, level);

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
  tk->ctx->mcsat->trail->inconsistent = true;
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


/** Concstruct the trail token */
static inline
void trail_token_construct(plugin_trail_token_t* token, mcsat_plugin_context_t* ctx, variable_t x) {
  token->token_interface.add = trail_token_add;
  token->token_interface.add_at_level = trail_token_add_at_level;
  token->token_interface.conflict = trail_token_conflict;
  token->token_interface.lemma = trail_token_lemma;
  token->ctx = ctx;
  token->x = x;
  token->used = 0;
}

void mcsat_plugin_term_notification_by_kind(plugin_context_t* self, term_kind_t kind) {
  uint32_t i;
  mcsat_plugin_context_t* mctx;

  mctx = (mcsat_plugin_context_t*) self;
  assert(mctx->plugin_i != MCSAT_MAX_PLUGINS);
  for (i = kind; mctx->mcsat->kind_owners[i] != MCSAT_MAX_PLUGINS; i += MCSAT_MAX_PLUGINS) {}
  mctx->mcsat->kind_owners[i] = mctx->plugin_i;
}

void mcsat_plugin_term_notification_by_type(plugin_context_t* self, type_kind_t kind) {
  uint32_t i;
  mcsat_plugin_context_t* mctx;

  mctx = (mcsat_plugin_context_t*) self;
  assert(mctx->plugin_i != MCSAT_MAX_PLUGINS);
  for (i = kind; mctx->mcsat->type_owners[i] != MCSAT_MAX_PLUGINS; i += MCSAT_MAX_PLUGINS) {}
  mctx->mcsat->type_owners[i] = mctx->plugin_i;
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
int mcsat_plugin_context_cmp_variables(plugin_context_t* self, variable_t x, variable_t y) {
  mcsat_plugin_context_t* mctx;
  mctx = (mcsat_plugin_context_t*) self;
  return var_queue_cmp_variables(&mctx->mcsat->var_queue, x, y);
}

static
void mcsat_plugin_context_propagation_calls(plugin_context_t* self) {

}

static
void mcsat_plugin_context_decision_calls(plugin_context_t* self, type_kind_t type) {
  mcsat_plugin_context_t* mctx;

  mctx = (mcsat_plugin_context_t*) self;
  assert(mctx->mcsat->decision_makers[type] == MCSAT_MAX_PLUGINS);
  mctx->mcsat->decision_makers[type] = mctx->plugin_i;
}

void mcsat_plugin_context_construct(mcsat_plugin_context_t* ctx, mcsat_solver_t* mcsat, uint32_t plugin_i, const char* plugin_name) {
  ctx->ctx.var_db = mcsat->var_db;
  ctx->ctx.terms = mcsat->terms;
  ctx->ctx.types = mcsat->types;
  ctx->ctx.exception = mcsat->exception;
  ctx->ctx.options = &mcsat->ctx->mcsat_options;
  ctx->ctx.trail = mcsat->trail;
  ctx->ctx.stats = &mcsat->stats;
  ctx->ctx.tracer = mcsat->ctx->trace;
  ctx->ctx.request_decision_calls = mcsat_plugin_context_decision_calls;
  ctx->ctx.request_term_notification_by_kind = mcsat_plugin_term_notification_by_kind;
  ctx->ctx.request_term_notification_by_type = mcsat_plugin_term_notification_by_type;
  ctx->ctx.request_propagation_calls = mcsat_plugin_context_propagation_calls;
  ctx->ctx.request_restart = mcsat_plugin_context_restart;
  ctx->ctx.request_gc = mcsat_plugin_context_gc;
  ctx->ctx.bump_variable = mcsat_plugin_context_bump_variable;
  ctx->ctx.cmp_variables = mcsat_plugin_context_cmp_variables;
  ctx->mcsat = mcsat;
  ctx->plugin_i = plugin_i;
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
void mcsat_add_plugin(mcsat_solver_t* mcsat, plugin_allocator_t plugin_allocator, const char* plugin_name) {

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
  mcsat->plugins[plugin_i].plugin_name = strdup(plugin_name);
  mcsat->plugins_count ++;
}

static
void mcsat_add_plugins(mcsat_solver_t* mcsat) {
  mcsat_add_plugin(mcsat, bool_plugin_allocator, "bool_plugin");
  mcsat_add_plugin(mcsat, uf_plugin_allocator, "uf_plugin");
  mcsat_add_plugin(mcsat, ite_plugin_allocator, "ite_plugin");
  mcsat_add_plugin(mcsat, nra_plugin_allocator, "nra_plugin");
}

static
void mcsat_construct(mcsat_solver_t* mcsat, context_t* ctx) {
  uint32_t i;

  assert(ctx != NULL);
  assert(ctx->arch == CTX_ARCH_MCSAT);
  assert(ctx->terms != NULL);
  assert(ctx->types != NULL);

  mcsat->ctx = ctx;
  mcsat->exception = &ctx->env;
  mcsat->types = ctx->types;
  mcsat->terms = ctx->terms;
  mcsat->terms_size_on_solver_entry = 0;
  mcsat->status = STATUS_IDLE;

  // The new variable listener
  mcsat->var_db_notify.mcsat = mcsat;
  mcsat->var_db_notify.new_variable = mcsat_new_variable_notify;

  // The variable database
  mcsat->var_db = safe_malloc(sizeof(variable_db_t));
  variable_db_construct(mcsat->var_db, mcsat->terms, mcsat->types, mcsat->ctx->trace);
  variable_db_add_new_variable_listener(mcsat->var_db, (variable_db_new_variable_notify_t*)&mcsat->var_db_notify);

  // List of assertions
  init_ivector(&mcsat->assertion_vars, 0);

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
  preprocessor_construct(&mcsat->preprocessor, mcsat->terms, mcsat->exception);

  // The variable queue
  var_queue_construct(&mcsat->var_queue);

  mcsat->pending_requests_all.restart = false;
  mcsat->pending_requests_all.gc_calls = false;
  mcsat->pending_requests = false;

  // Lemmas vector
  init_ivector(&mcsat->plugin_lemmas, 0);

  // Construct stats
  statistics_construct(&mcsat->stats);
  mcsat_stats_init(mcsat);

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

  delete_int_queue(&mcsat->registration_queue);
  delete_int_hset(&mcsat->registration_cache);
  delete_ivector(&mcsat->assertion_vars);
  trail_destruct(mcsat->trail);
  safe_free(mcsat->trail);
  variable_db_destruct(mcsat->var_db);
  safe_free(mcsat->var_db);
  preprocessor_destruct(&mcsat->preprocessor);
  var_queue_destruct(&mcsat->var_queue);
  delete_ivector(&mcsat->plugin_lemmas);
  statistics_destruct(&mcsat->stats);
}

mcsat_solver_t* mcsat_new(context_t* ctx) {
  mcsat_solver_t* mcsat = (mcsat_solver_t*) safe_malloc(sizeof(mcsat_solver_t));
  mcsat_construct(mcsat, ctx);
  return mcsat;
}


smt_status_t mcsat_status(const mcsat_solver_t* mcsat) {
  return mcsat->status;
}

void mcsat_reset(mcsat_solver_t* mcsat) {

}

static
void mcsat_push_internal(mcsat_solver_t* mcsat) {
  uint32_t i;
  plugin_t* plugin;

  for (i = 0; i < mcsat->plugins_count; ++ i) {
    plugin = mcsat->plugins[i].plugin;
    if (plugin->push) {
      plugin->push(plugin);
    }
  }
}

void mcsat_push(mcsat_solver_t* mcsat) {
  assert(false);
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
}

void mcsat_pop(mcsat_solver_t* mcsat) {
  assert(false);
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
    i += MCSAT_MAX_PLUGINS;
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
  assert(plugin_i != MCSAT_MAX_PLUGINS || i == UNINTERPRETED_TERM || i == CONSTANT_TERM);
  while (plugin_i != MCSAT_MAX_PLUGINS) {
    int_mset_add(owners, plugin_i);
    i += MCSAT_MAX_PLUGINS;
    plugin_i = mcsat->kind_owners[i];
  };
}


static void mcsat_process_registeration_queue(mcsat_solver_t* mcsat) {
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
      trace_printf(mcsat->ctx->trace, "term registration: ");
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

static
void mcsat_gc(mcsat_solver_t* mcsat) {

  uint32_t i;
  variable_t var;
  gc_info_t gc_vars;
  plugin_t* plugin;

  if (trace_enabled(mcsat->ctx->trace, "mcsat::gc")) {
    trace_printf(mcsat->ctx->trace, "mcsat_gc():\n");
    mcsat_show_stats(mcsat, mcsat->ctx->trace->file);
  }

  // Mark previously used term in the term table
  // set_bitvector(mcsat->terms->mark, mcsat->terms_size_on_solver_entry);

  // Construct the variable info
  gc_info_construct(&gc_vars, variable_null, true);

  if (trace_enabled(mcsat->ctx->trace, "mcsat::gc")) {
    trace_printf(mcsat->ctx->trace, "mcsat_gc(): marking\n");
  }

  // Mark the assertion variables as needed
  for (i = 0; i < mcsat->assertion_vars.size; ++ i) {
    var = mcsat->assertion_vars.data[i];
    assert(variable_db_is_variable(mcsat->var_db, var, true));
    gc_info_mark(&gc_vars, var);
  }

  // Mark the trail variables as needed
  trail_gc_mark(mcsat->trail, &gc_vars);

  // Mark variables by plugins
  for (;;) {

    // Mark with each plugin
    for (i = 0; i < mcsat->plugins_count; ++ i) {
      if (trace_enabled(mcsat->ctx->trace, "mcsat::gc")) {
        trace_printf(mcsat->ctx->trace, "mcsat_gc(): marking with %s\n", mcsat->plugins[i].plugin_name);
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
    trace_printf(mcsat->ctx->trace, "mcsat_gc(): sweeping\n");
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
    trace_printf(mcsat->ctx->trace, "mcsat_gc(): done\n");
  }
}

static
void mcsat_backtrack_to(mcsat_solver_t* mcsat, uint32_t level) {
  while (mcsat->trail->decision_level > level) {
    // Pop the trail
    trail_pop(mcsat->trail);
    // Pop the plugins
    mcsat_pop_internal(mcsat);
  }
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

static
void mcsat_process_requests(mcsat_solver_t* mcsat) {

  if (mcsat->pending_requests) {

    // Restarts
    if (mcsat->pending_requests_all.restart) {
      if (trace_enabled(mcsat->ctx->trace, "mcsat")) {
        trace_printf(mcsat->ctx->trace, "restarting\n");
      }
      mcsat_backtrack_to(mcsat, mcsat->trail->decision_level_base);
      mcsat->pending_requests_all.restart = false;
      (*mcsat->solver_stats.restarts) ++;
      mcsat_notify_plugins(mcsat, MCSAT_SOLVER_RESTART);
    }

    // GC
    if (mcsat->pending_requests_all.gc_calls) {
      if (trace_enabled(mcsat->ctx->trace, "mcsat")) {
        trace_printf(mcsat->ctx->trace, "garbage collection\n");
      }
      mcsat_gc(mcsat);
      mcsat->pending_requests_all.gc_calls = false;
      (*mcsat->solver_stats.gc_calls) ++;
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
bool mcsat_propagate(mcsat_solver_t* mcsat) {

  uint32_t plugin_i;
  plugin_t* plugin;
  plugin_trail_token_t prop_token;
  bool someone_propagated;

  do {
    // Repeat until no plugin makes any progress
    someone_propagated = false;
    // Propagate with all the plugins in turn
    for (plugin_i = 0; trail_is_consistent(mcsat->trail) && plugin_i < mcsat->plugins_count; ++ plugin_i) {
      if (trace_enabled(mcsat->ctx->trace, "mcsat::propagate")) {
        trace_printf(mcsat->ctx->trace, "mcsat_propagate(): with %s\n", mcsat->plugins[plugin_i].plugin_name);
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
  } while (someone_propagated && trail_is_consistent(mcsat->trail));

  return someone_propagated;
}

static
void mcsat_assert_formula(mcsat_solver_t* mcsat, term_t f) {

  term_t f_pos;
  variable_t f_pos_var;

  if (trace_enabled(mcsat->ctx->trace, "mcsat")) {
    trace_printf(mcsat->ctx->trace, "mcsat_assert_formula()\n");
    trace_term_ln(mcsat->ctx->trace, mcsat->terms, f);
  }

  // If we're unsat, no more assertions
  if (mcsat->status == STATUS_UNSAT) {
    return;
  }

  (*mcsat->solver_stats.assertions) ++;

  assert(trail_is_at_base_level(mcsat->trail));
  assert(int_queue_is_empty(&mcsat->registration_queue));

  // Add the terms
  f_pos = unsigned_term(f);
  f_pos_var = variable_db_get_variable(mcsat->var_db, f_pos);
  mcsat_process_registeration_queue(mcsat);

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
        mcsat->status = STATUS_UNSAT;
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
        mcsat->status = STATUS_UNSAT;
        return;
      }
    }
  }

  // Do propagation
  mcsat_propagate(mcsat);
}

/**
 * Decide one of the unassigned literals.
 */
static
bool mcsat_decide_one_of(mcsat_solver_t* mcsat, ivector_t* literals) {

  uint32_t i;
  term_t literal;
  term_t literal_pos;
  variable_t literal_var;

  for (i = 0; i < literals->size; ++ i) {
    literal = literals->data[i];
    literal_pos = unsigned_term(literal);
    literal_var = variable_db_get_variable_if_exists(mcsat->var_db, literal_pos);

    assert(literal_var != variable_null);

    if (trace_enabled(mcsat->ctx->trace, "mcsat::lemma")) {
      trace_printf(mcsat->ctx->trace, "trying undecided :\n");
      trace_term_ln(mcsat->ctx->trace, mcsat->ctx->terms, literal);
    }

    // Decide positive
    if (!trail_has_value(mcsat->trail, literal_var)) {
      if (trace_enabled(mcsat->ctx->trace, "mcsat::lemma")) {
        trace_printf(mcsat->ctx->trace, "unassigned, deciding!\n");
      }
      mcsat_push_internal(mcsat);
      trail_add_decision(mcsat->trail, literal_var, literal_pos == literal ? &mcsat_value_true : &mcsat_value_false, MCSAT_MAX_PLUGINS);
      return true;
    } else {
      if (trace_enabled(mcsat->ctx->trace, "mcsat::lemma")) {
        trace_printf(mcsat->ctx->trace, "assigned!\n");
      }
    }
  }

  return false;
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
void mcsat_add_lemma(mcsat_solver_t* mcsat, ivector_t* lemma) {

  uint32_t i, level, top_level;
  ivector_t unassigned;
  term_t disjunct, disjunct_pos;
  variable_t disjunct_pos_var;
  plugin_t* plugin;

  (*mcsat->solver_stats.lemmas)++;

  if (trace_enabled(mcsat->ctx->trace, "mcsat::lemma")) {
    trace_printf(mcsat->ctx->trace, "lemma:\n");
    for (i = 0; i < lemma->size; ++ i) {
      trace_printf(mcsat->ctx->trace, "\t");
      trace_term_ln(mcsat->ctx->trace, mcsat->ctx->terms, lemma->data[i]);
    }
    trail_print(mcsat->trail, trace_out(mcsat->ctx->trace));
  }

  init_ivector(&unassigned, 0);

  top_level = 0;
  for (i = 0; i < lemma->size; ++ i) {

    // Get the variables for the disjunct
    disjunct = lemma->data[i];
    disjunct_pos = unsigned_term(disjunct);
    disjunct_pos_var = variable_db_get_variable(mcsat->var_db, disjunct_pos);

    // Process any newly registered variables
    mcsat_process_registeration_queue(mcsat);

    // Check if the literal has value (only negative allowed)
    if (trail_has_value(mcsat->trail, disjunct_pos_var)) {

      if (trace_enabled(mcsat->ctx->trace, "mcsat::lemma")) {
        trace_printf(mcsat->ctx->trace, "literal: ");
        variable_db_print_variable(mcsat->var_db, disjunct_pos_var, stderr);
        trace_printf(mcsat->ctx->trace, "\nvalue: ");
        const mcsat_value_t* value = trail_get_value(mcsat->trail, disjunct_pos_var);
        mcsat_value_print(value, stderr);
        trace_printf(mcsat->ctx->trace, "\n");
      }

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
    // UIP
    mcsat_backtrack_to(mcsat, top_level);
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
  mcsat_propagate(mcsat);
  bool propagated = old_trail_size < mcsat->trail->elements.size;

  // Decide a literal if necessary. At this point, if it was UIP they are all
  // assigned. If not, we assign arbitrary.
  bool decided = false;
  bool consistent = trail_is_consistent(mcsat->trail);
  if (consistent) {
    decided = mcsat_decide_one_of(mcsat, &unassigned);
  }
  if(!(propagated || !consistent || decided)) {
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

static
void mcsat_analyze_conflicts(mcsat_solver_t* mcsat, uint32_t* restart_resource) {

  conflict_t conflict;
  plugin_t* plugin;
  uint32_t plugin_i;
  tracer_t* trace;

  uint32_t conflict_level;
  variable_t var;

  ivector_t reason;
  term_t substitution;

  ivector_t* conflict_disjuncts;

  init_ivector(&reason, 0);
  trace = mcsat->ctx->trace;

  // Plugin that's in conflict
  plugin_i = mcsat->plugin_in_conflict->plugin_i;
  plugin = mcsat->plugins[plugin_i].plugin;

  if (trace_enabled(trace, "mcsat::conflict")) {
    trace_printf(trace, "analyzing conflict from %s\n", mcsat->plugins[plugin_i].plugin_name);
    trace_printf(trace, "trail: ");
    trail_print(mcsat->trail, trace->file);
  }

  // Construct the conflict
  assert(plugin->get_conflict);
  plugin->get_conflict(plugin, &reason);
  conflict_construct(&conflict, &reason, (mcsat_evaluator_interface_t*) &mcsat->evaluator, mcsat->var_db, mcsat->trail, mcsat->ctx->terms, mcsat->ctx->trace);

  if (trace_enabled(trace, "mcsat::conflict") || trace_enabled(trace, "mcsat::lemma")) {
    trace_printf(trace, "conflict from %s\n", mcsat->plugins[plugin_i].plugin_name);
    conflict_print(&conflict, trace->file);
  }

  // Get the level of the conflict and backtrack to it
  conflict_level = conflict_get_level(&conflict);
  mcsat_backtrack_to(mcsat, conflict_level);

  // Analyze while at least one variable at conflict level
  while (true) {

    if (conflict_level == 0) {
      // Resolved all the way
      break;
    }

    if (conflict_get_top_level_vars_count(&conflict) == 1) {
      // UIP, we're done
      break;
    }

    if (trace_enabled(trace, "mcsat::conflict")) {
      trace_printf(trace, "current trail:\n");
      trail_print(mcsat->trail, trace->file);
      trace_printf(trace, "current conflict: ");
      conflict_print(&conflict, trace->file);
    }

    // Current variable
    var = trail_back(mcsat->trail);
    assert(trail_get_assignment_type(mcsat->trail, var) != DECISION);

    // Resolve if in the conflict and current level
    if (conflict_contains_as_top(&conflict, var)) {

      // Get the plugin that performed the propagation
      plugin_i = trail_get_source_id(mcsat->trail, var);
      plugin = mcsat->plugins[plugin_i].plugin;

      if (trace_enabled(trace, "mcsat::conflict")) {
        trace_printf(trace, "resolving ");
        variable_db_print_variable(mcsat->var_db, var, trace->file);
        trace_printf(trace, " with %s\n", mcsat->plugins[plugin_i].plugin_name);
        trace_printf(trace, "current conflict:\n");
        conflict_print(&conflict, trace->file);
      }

      // Resolve the variable
      ivector_reset(&reason);
      assert(plugin->explain_propagation);
      substitution = plugin->explain_propagation(plugin, var, &reason);
      conflict_resolve_propagation(&conflict, var, substitution, &reason);
      // The trail pops with the resolution step
    } else {
      // Have to pop the trail manually
      trail_pop_propagation(mcsat->trail);
      assert(!conflict_contains(&conflict, var));
    }

    if (conflict_get_top_level_vars_count(&conflict) == 0) {
      // We have resolved the conflict even lower
      conflict_recompute_level_info(&conflict);
      conflict_level = conflict_get_level(&conflict);
      mcsat_backtrack_to(mcsat, conflict_level);
    }
  }

  if (trace_enabled(trace, "mcsat::conflict")) {
    trace_printf(trace, "current conflict: ");
    conflict_print(&conflict, trace->file);
  }

  // UIP conflict resolution
  assert(conflict_level == 0 || conflict_get_top_level_vars_count(&conflict) == 1);

  if (conflict_level == 0) {
    mcsat->status = STATUS_UNSAT;
  } else {
    // We should still be in conflict, so back out
    assert(conflict.level == mcsat->trail->decision_level);
    mcsat_backtrack_to(mcsat, mcsat->trail->decision_level - 1);

    // Get the literals
    conflict_disjuncts = conflict_get_literals(&conflict);

    if (trace_enabled(trace, "mcsat::conflict")) {
      trace_printf(trace, "conflict_disjuncts:\n");
      uint32_t i;
      for (i = 0; i < conflict_disjuncts->size; ++i) {
        trace_printf(trace, "[%u]: ", i);
        trace_term_ln(trace, mcsat->ctx->terms, conflict_disjuncts->data[i]);
      }
    }

    // Now add the lemma
    mcsat_add_lemma(mcsat, conflict_disjuncts);

    // Use resources based on conflict size
    *restart_resource += mcsat_get_lemma_weight(mcsat, conflict_disjuncts,
        mcsat->heuristic_params.lemma_restart_weight_type);

    // Bump the variables
    mcsat_bump_variables_mset(mcsat, conflict_get_variables_all(&conflict));

    if (trace_enabled(trace, "mcsat::conflict::trail")) {
      trace_printf(trace, "trail: ");
      trail_print(mcsat->trail, trace->file);
    }
  }

  delete_ivector(&reason);
  conflict_destruct(&conflict);
}

/**
 * Decides a variable using one of the plugins. Returns true if a variable
 * has been decided, or a conflict detected.
 */
static
bool mcsat_decide(mcsat_solver_t* mcsat) {

  uint32_t i;
  variable_t var;
  plugin_t* plugin;
  plugin_trail_token_t decision_token;

  ivector_t skipped_variables; // Variables we took from the queue but plugin didn't decide
  init_ivector(&skipped_variables, 0);

  assert(!mcsat->trail->inconsistent);

  bool force_decision = false;
  while (true) {

    // Get an unassigned variable from the queue
    var = variable_null;

    // Random decision:
    double* seed = &mcsat->heuristic_params.random_decision_seed;
    double freq = mcsat->heuristic_params.random_decision_freq;
    if (drand(seed) < freq && !var_queue_is_empty(&mcsat->var_queue)) {
        var = var_queue_random(&mcsat->var_queue, seed);
        if (trail_has_value(mcsat->trail, var)) {
          var = variable_null;
        } else {
          // fprintf(stderr, "random\n");
        }
    }

    // Use the queue
    while (!var_queue_is_empty(&mcsat->var_queue) && var == variable_null) {
      // Get the next variable from the queue
      var = var_queue_pop(&mcsat->var_queue);
      // If already assigned go on
      if (trail_has_value(mcsat->trail, var)) {
        var = variable_null;
        continue;
      }
    }

    if (var != variable_null) {
      // Get the owner that will decide that value of the variable
      i = mcsat->decision_makers[variable_db_get_type_kind(mcsat->var_db, var)];
      assert(i != MCSAT_MAX_PLUGINS);
      // Construct the token
      trail_token_construct(&decision_token, mcsat->plugins[i].plugin_ctx, var);
      // Decide
      if (trace_enabled(mcsat->ctx->trace, "mcsat::decide")) {
        trace_printf(mcsat->ctx->trace, "mcsat_decide(): with %s\n",
            mcsat->plugins[i].plugin_name);
        trace_printf(mcsat->ctx->trace, "mcsat_decide(): variable ");
        variable_db_print_variable(mcsat->var_db, var,
            trace_out(mcsat->ctx->trace));
        trace_printf(mcsat->ctx->trace, "\n");
      }
      plugin = mcsat->plugins[i].plugin;

      // Ask the owner to decide
      mcsat_push_internal(mcsat);
      assert(plugin->decide);
      plugin->decide(plugin, var, (trail_token_t*) &decision_token, force_decision);

      if (decision_token.used == 0) {
        // If not decided, remember and go on
        ivector_push(&skipped_variables, var);
        mcsat_pop_internal(mcsat);
      } else {
        // Decided, we can continue with the search
        (*mcsat->solver_stats.decisions)++;
        // If plugin decided on another variable, put it back
        if (!trail_has_value(mcsat->trail, var)) {
          var_queue_insert(&mcsat->var_queue, var);
        }
        break;
      }
    } else {
      // No variables left to decide
      if (skipped_variables.size == 0) {
        // Didn't skip any, we're done
        break;
      } else {
        // Put the skipped back in the queue, and continue but force next decision
        for (i = 0; i < skipped_variables.size; ++ i) {
          var_queue_insert(&mcsat->var_queue, skipped_variables.data[i]);
        }
        ivector_reset(&skipped_variables);
        force_decision = true;
      }
    }
  }

  // Put any skipped variables back into the queue
  if (skipped_variables.size > 0) {
    // If we skipped some, we had to decided one, we put the skiped scores to
    // the decided score
    assert(var != variable_null);
    double var_score = var_queue_get_activity(&mcsat->var_queue, var);
    for (i = 0; i < skipped_variables.size; ++ i) {
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

void mcsat_solve(mcsat_solver_t* mcsat, const param_t *params) {

  uint32_t restart_resource;
  luby_t luby;

  // If we're already unsat, just return
  if (mcsat->status == STATUS_UNSAT) {
    return;
  }

  // Remember existing terms
  mcsat->terms_size_on_solver_entry = mcsat->terms->nelems;

  // Initialize for search
  mcsat_heuristics_init(mcsat);
  mcsat_notify_plugins(mcsat, MCSAT_SOLVER_START);

  // Initialize the Luby sequence with interval 10
  restart_resource = 0;
  luby_init(&luby, mcsat->heuristic_params.restart_interval);


  for (;;) {

    // Do we restart
    if (trail_is_consistent(mcsat->trail) && restart_resource > luby.restart_threshold) {
      restart_resource = 0;
      luby_next(&luby);
      mcsat_request_restart(mcsat);
    }

    // Process any outstanding requests
    mcsat_process_requests(mcsat);

    // Do propagation
    mcsat_propagate(mcsat);

    // If inconsistent, analyze the conflict
    if (!trail_is_consistent(mcsat->trail)) {
      goto conflict;
    }

    // If any requests, process them and go again
    if (mcsat->pending_requests) {
      continue;
    }

    // Time to make a decision
    if (!mcsat_decide(mcsat)) {
      if (!trail_is_consistent(mcsat->trail)) {
        goto conflict;
      } else {
        mcsat->status = STATUS_SAT;
        return;
      }
    }

    // Decision made, continue with the search
    continue;

  conflict:

    (*mcsat->solver_stats.conflicts)++;
    mcsat_notify_plugins(mcsat, MCSAT_SOLVER_CONFLICT);

    // If at level 0 we're unsat
    if (trail_is_at_base_level(mcsat->trail)) {
      mcsat->status = STATUS_UNSAT;
      return;
    }

    // Analyze the conflicts
    mcsat_analyze_conflicts(mcsat, &restart_resource);

    // Analysis might have discovered 0-level conflict
    if (mcsat->status == STATUS_UNSAT) {
      return;
    }

    var_queue_decay_activities(&mcsat->var_queue);
  }
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

int32_t mcsat_assert_formulas(mcsat_solver_t* mcsat, uint32_t n, const term_t *f) {
  uint32_t i;

  // Preprocess the formulas
  ivector_t assertions;
  init_ivector(&assertions, 0);
  ivector_add(&assertions, f, n);
  for (i = 0; i < assertions.size; ++ i) {
    term_t f = assertions.data[i];
    term_t f_pre = preprocessor_apply(&mcsat->preprocessor, f, &assertions);
    assertions.data[i] = f_pre;
  }

  // Assert individual formulas
  for (i = 0; i < assertions.size; ++ i) {
    // Assert it
    mcsat_assert_formula(mcsat, assertions.data[i]);
    // Add any lemmas that were added
    ivector_add(&assertions, mcsat->plugin_lemmas.data, mcsat->plugin_lemmas.size);
    ivector_reset(&mcsat->plugin_lemmas);
  }

  // Delete the temp
  delete_ivector(&assertions);

  return CTX_NO_ERROR;
}

void mcsat_show_stats(mcsat_solver_t* mcsat, FILE* out) {
  statistics_print(&mcsat->stats, out);
}

void mcsat_build_model(mcsat_solver_t* mcsat, model_t* model) {

  value_table_t* vtbl = model_get_vtbl(model);

  if (trace_enabled(mcsat->ctx->trace, "mcsat")) {
    trace_printf(mcsat->ctx->trace, "mcsat_build_model()\n");
  }

  // Just copy the trail into the model
  uint32_t i;
  ivector_t* trail_elements = &mcsat->trail->elements;
  for (i = 0; i < trail_elements->size; ++ i) {
    variable_t x = trail_elements->data[i];
    term_t x_term = variable_db_get_term(mcsat->var_db, x);
    term_kind_t x_kind = term_kind(mcsat->terms, x_term);

    if (x_kind == UNINTERPRETED_TERM) {

      if (trace_enabled(mcsat->ctx->trace, "mcsat")) {
        trace_printf(mcsat->ctx->trace, "var = ");
        trace_term_ln(mcsat->ctx->trace, mcsat->terms, x_term);
      }

      // Type of the variable
      type_t x_type = term_type(mcsat->terms, x_term);

      // Get mcsat value (have to case to remove const because yices api doesn't care for const)
      mcsat_value_t* x_value_mcsat = (mcsat_value_t*) trail_get_value(mcsat->trail, x);

      if (trace_enabled(mcsat->ctx->trace, "mcsat")) {
        trace_printf(mcsat->ctx->trace, "value = ");
        mcsat_value_print(x_value_mcsat, trace_out(mcsat->ctx->trace));
        trace_printf(mcsat->ctx->trace, "\n");
      }

      // Setup the yices value
      value_t x_value = mcsat_value_to_value(x_value_mcsat, mcsat->types, x_type, vtbl);

      if (trace_enabled(mcsat->ctx->trace, "mcsat")) {
        trace_printf(mcsat->ctx->trace, "value = ");
        vtbl_print_object(trace_out(mcsat->ctx->trace), vtbl, x_value);
        trace_printf(mcsat->ctx->trace, "\n");
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
