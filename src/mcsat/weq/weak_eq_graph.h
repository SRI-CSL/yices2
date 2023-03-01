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
 
#ifndef WEAK_EQ_GRAPH_H_
#define WEAK_EQ_GRAPH_H_

#include "mcsat/eq/equality_graph.h"
#include "mcsat/plugin.h"
#include "mcsat/utils/scope_holder.h"

#include "utils/int_array_hsets.h"
#include "utils/int_hash_sets.h"

#include "api/yices_api_lock_free.h"


typedef struct weq_graph_s {

  /** The plugin context */
  plugin_context_t* ctx;

  /** Scope holder for the int variables */
  scope_holder_t scope;

  /** pointer to the equality graph */
  eq_graph_t* eq_graph;

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

  /** Value eq_node_id to term (one rep term) */
  int_hmap_t val_id_term_map;

  /** Weak path equalities **/
  ivector_t path_cond;

  /** Weak path indices **/
  ivector_t path_indices1;

  /** Weak path indices **/
  ivector_t path_indices2;

  struct {
    statistic_int_t* array_terms;
    statistic_int_t* select_terms;
    statistic_int_t* array_update1_axioms;
    statistic_int_t* array_update2_axioms;
    statistic_int_t* array_ext_axioms;
  } stats;
  
} weq_graph_t;

/** Construct a new weakly-equivalent graph. */
void weq_graph_construct(weq_graph_t* weq, plugin_context_t* ctx, eq_graph_t* eq);

/** Destruct the graph */
void weq_graph_destruct(weq_graph_t* weq);

/** Push the context */
void weq_graph_push(weq_graph_t* weq);

/** Pop the context */
void weq_graph_pop(weq_graph_t* weq);

/** add array term */
void weq_graph_add_array_term(weq_graph_t* weq, term_t arr);

/** add array equality term */
void weq_graph_add_array_eq_term(weq_graph_t* weq, term_t arr_eq);

/** add array select term */
void weq_graph_add_select_term(weq_graph_t* weq, term_t sel);

/** add diff fun */
void weq_graph_add_diff_fun(weq_graph_t* weq, term_t diff_fun);

/** Contains diff fun */
bool weq_graph_has_diff_fun(weq_graph_t* weq, term_t diff_fun);

/** Clear weq cache */
void weq_graph_clear(weq_graph_t* weq);

/** Return array update index lemma term */
term_t weq_graph_get_array_update_idx_lemma(weq_graph_t* weq, term_t update_term);

/** Check for array conflicts */
void weq_graph_check_array_conflict(weq_graph_t* weq, ivector_t* conflict);

#endif /* WEAK_EQ_GRAPH_H_ */
