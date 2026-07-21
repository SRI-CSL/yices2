/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */


#ifndef MCSAT_L2O_H_
#define MCSAT_L2O_H_

#include "terms/terms.h"
#include "terms/term_manager.h"
#include "utils/int_hash_mmap.h"
#include "io/tracer.h"

#include "mcsat/tracing.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/variable_queue.h"

typedef struct l2o {
  /** Term table */
  term_table_t* terms;

  // TODO ugly hack
  plugin_t *na_plugin;
  plugin_t *bool_plugin;

  /** Assertions */
  ivector_t assertions;

  /** terms with their free variables */
  int_hmmap_t var_member;

  /** Statistics */
  statistics_t stats;

  struct {
    // Number of L2O terms
    statistic_int_t* n_terms;
    // Number of minimization calls
    statistic_int_t* n_runs;
    // Eval runs
    statistic_int_t* n_eval_runs;
  } l2o_stats;

  /** Tracer */
  tracer_t* tracer;

  /** Exception handler */
  jmp_buf* exception;

  /** Scope for backtracking */
  scope_holder_t scope;

} l2o_t;

/** Construct the L2O operator */
void l2o_construct(l2o_t* l2o, term_table_t* terms, jmp_buf* handler, plugin_t* na_plugin, plugin_t *bool_plugin);

/** Destruct the L2O operator */
void l2o_destruct(l2o_t* l2o);

/** Set tracer */
void l2o_set_tracer(l2o_t* l2o, tracer_t* tracer);

/** Set the exception handler */
void l2o_set_exception_handler(l2o_t* l2o, jmp_buf* handler);

/** Store an assertion to l2o::assertions */
void l2o_store_assertion(l2o_t* l2o, term_t assertion);

/** Create the L2O cost function to the conjunction of the stored assertions */
void l2o_run(l2o_t* l2o, mcsat_trail_t* trail, bool use_cached_values, const var_queue_t *queue);

#endif
