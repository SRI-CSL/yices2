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



#include "terms/terms.h"
#include "terms/term_manager.h"
#include "utils/int_vectors.h"
#include "utils/int_hash_map.h"
#include "utils/pair_hash_map2.h"
#include "io/tracer.h"
#include "mcsat/utils/scope_holder.h"

#include <setjmp.h>


#include "mcsat/tracing.h"
#include "mcsat/l2o/eval_hash_map.h"
#include "mcsat/l2o/varset_table.h"

#ifndef MCSAT_L2O_H_
#define MCSAT_L2O_H_


//#include "mcsat/l2o/evaluator.h"
#include "utils/index_vectors.h"




typedef struct {
  /** Cached cost */
  double cost;

  /** Number of cached variables and values */
  uint32_t n_var;

  /** Cached variables */
  term_t *v;

  /** Cached values */
  double *x;

  /** Cached map from terms to their evaluation under the assignment v -> x */
  eval_hmap_t eval_map;

} eval_cache_t;

typedef struct {

  /** Map from terms to their evaluation */
  eval_hmap_t eval_map;

  /** eval stack */
  ivector_t eval_stack;

  /** Eval cache */
  eval_cache_t cache;

  /** Tracer */
  tracer_t* tracer;

  pp_buffer_t pp_buffer;

} evaluator_t;



typedef struct {

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

  /** Approximate Evaluator */
  evaluator_t evaluator;

  /** Tracer */
  tracer_t* tracer;

  /** Exception handler */
  jmp_buf* exception;

  /** Scope for backtracking */
  scope_holder_t scope;

  pp_buffer_t pp_buffer;

} l2o_t;

/** Construct the L2O operator */
void l2o_construct(l2o_t* l2o, term_table_t* terms, jmp_buf* handler);

/** Destruct the L2O operator */
void l2o_destruct(l2o_t* l2o);

/** Store an assertion to l2o.assertions */
void l2o_store_assertion(l2o_t* l2o, term_t assertion);

/** Apply the L2O operator to term t */
term_t l2o_apply(l2o_t* l2o, term_t t);

/** Create the L2O cost function to the conjunction of the stored assertions */
void l2o_run(l2o_t* l2o, mcsat_trail_t* trail);

/** Get the varset_table index of the set of free variables in t */
int32_t get_freevars_index(const l2o_t* l2o, term_t t);

/** Get the set of free variables in t */
const int_hset_t* get_freevars(const l2o_t* l2o, term_t t);

/** Get the set of free variables from a term given its varset_table index  */
const int_hset_t* get_freevars_from_index(const l2o_t* l2o, int32_t index);

/** Minimize L2O cost function and set hint to trail */
void l2o_minimize_and_set_hint(l2o_t* l2o, term_t t, mcsat_trail_t* trail);

/** Set tracer */
void l2o_set_tracer(l2o_t* l2o, tracer_t* tracer);

/** Set the exception handler */
void l2o_set_exception_handler(l2o_t* l2o, jmp_buf* handler);

/** Push L2O */
void l2o_push(l2o_t* l2o);

/** Pop L2O */
void l2o_pop(l2o_t* l2o);

/** Get L2O translation of t */
term_t l2o_get(l2o_t* l2o, term_t t);

composite_term_t* get_composite(term_table_t* terms, term_kind_t kind, term_t t);



/** Construct the evaluator operator */
void evaluator_construct(evaluator_t* evaluator);

/** Destruct the evaluator operator */
void evaluator_destruct(evaluator_t* evaluator);

/** Set tracer */
void evaluator_set_tracer(evaluator_t* evaluator, tracer_t* tracer);

// Delete cache cost to force updating the cache after the next evaluation
void evaluator_forget_cache_cost(evaluator_t* evaluator);

// Approximately evaluates term_eval t substituting variables v with double values x. The assignment has to be total.
// TODO: accept partial assignments returning a term
double l2o_evaluate_term_approx(l2o_t *l2o, term_t term, uint32_t n_var, const term_t *v, const double *x);

// Hill climbing algorithm with cost function t (to be minimized), variables v (some of which have fixed values), and starting point x
void hill_climbing(l2o_t *l2o, term_t t, uint32_t n_var, const term_t *v, const bool *v_fixed, double *x);

#endif
