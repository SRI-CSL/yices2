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


#ifndef MCSAT_L2O_H_
#define MCSAT_L2O_H_

#include "terms/terms.h"
#include "terms/term_manager.h"
#include "utils/pair_hash_map2.h"
#include "utils/double_hash_map.h"
#include "io/tracer.h"

#include "mcsat/tracing.h"
#include "mcsat/l2o/varset_table.h"
#include "mcsat/utils/scope_holder.h"


// TODO move data structures and internal functions to l2o_internal.h and only keep public functions here. (similar to nra_plugin.h)

typedef enum {
  L2O,
  L2O_CLASSIC,
  /* L2O_CELL_JUMP, */
} l2o_mode_t;

typedef struct {
  /** The l2o mode */
  l2o_mode_t mode;

  /** Term table */
  term_table_t* terms;

  /** Term manager */
  term_manager_t tm;

  /** Assertions */
  ivector_t assertions;

  /** The cost function */
  term_t cost_fx;

  /** Number of L2O terms */
  uint32_t n_terms;

  /** Number of minimization calls */
  uint32_t n_runs;

  /** Map from terms to their L2O version */
  int_hmap_t l2o_map;

  /** Map from vars to L2O vars, handling also Bool-to-Real and Int-to-Real */
  int_hmap_t l2o_var_map;

  /** Table of sets of variables */
  varset_table_t varset_table;
  
  /** Map from a term to the table index of the set of its free variables */
  int_hmap_t freevars_map;

  /** Map from a variable and an index of varset_table to a boolean which is true iff the variable is member of the varset */
  pmap2_t varset_members_cache;

  /** Evaluator cache */
  double_hmap_t eval_cache;

  /** Tracer */
  tracer_t* tracer;

  /** Exception handler */
  jmp_buf* exception;

  /** Scope for backtracking */
  scope_holder_t scope;

  pp_buffer_t pp_buffer;

} l2o_t;

/** Construct the L2O operator */
void l2o_construct(l2o_t* l2o, l2o_mode_t mode, term_table_t* terms, jmp_buf* handler);

/** Destruct the L2O operator */
void l2o_destruct(l2o_t* l2o);

/** Set tracer */
void l2o_set_tracer(l2o_t* l2o, tracer_t* tracer);

/** Set the exception handler */
void l2o_set_exception_handler(l2o_t* l2o, jmp_buf* handler);

/** Store an assertion to l2o.assertions */
void l2o_store_assertion(l2o_t* l2o, term_t assertion);

/** Create the L2O cost function to the conjunction of the stored assertions */
void l2o_run(l2o_t* l2o, mcsat_trail_t* trail, bool use_cached_values);

/** Push L2O */
void l2o_push(l2o_t* l2o);

/** Pop L2O */
void l2o_pop(l2o_t* l2o);

/** Get L2O translation of t */
term_t l2o_get(l2o_t* l2o, term_t t);

#endif
