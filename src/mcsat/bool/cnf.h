/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#ifndef CNF_H_
#define CNF_H_

#include "mcsat/plugin.h"
#include "mcsat/variable_db.h"
#include "mcsat/bool/clause_db.h"
#include "mcsat/utils/int_lset.h"

#include "utils/int_hash_map.h"

/**
 * The CNF manager keeps the definitional CNF transformation. It converts
 * the given Boolean term recursively by creating a variable for the (positive)
 * sub-term and defining it by clausifying var_t <=> t.
 */
typedef struct {

  /** The clause database */
  clause_db_t* clause_db;

  /** The mcsat context */
  plugin_context_t* ctx;

  /** Map from converted variables to the list of their clauses */
  int_lset_t converted;

  /** Current variable being converted */
  variable_t variable;

} cnf_t;


/** Construct the CNF manager */
void cnf_construct(cnf_t* cnf, plugin_context_t* ctx, clause_db_t* clause_db);

/** Destruct the CNF manager */
void cnf_destruct(cnf_t* cnf);

/**
 * Add clauses for the given term to the clause database. All clauses
 * are added to the given vector. Clauses are added as definitions for the
 * internal (positive) nodes, and all the necessary variables are added to
 * the variable database.
 */
mcsat_literal_t cnf_convert(cnf_t* cnf, term_t t, ivector_t* t_clauses);

/**
 * Add the clause for the given lemma to the clause database. The clause will
 * be added to the given vector.
 */
void cnf_convert_lemma(cnf_t* cnf, const ivector_t* lemma, ivector_t* clauses);

/**
 * Mark all the clauses that are definitions for the variables in gc_vars.
 */
void cnf_gc_mark(cnf_t* cnf, gc_info_t* gc_clauses, const gc_info_t* gc_vars);

/**
 * Collect all the clauses that are definitions and marked in gc_clauses.
 */
void cnf_gc_sweep(cnf_t* cnf, const gc_info_t* gc_clauses, int_mset_t* vars_undefined);

#endif /* CNF_H_ */
