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

#ifndef __SIMPLEX_H
#define __SIMPLEX_H

#include "solvers/simplex/simplex_types.h"




/*********************
 *  MAIN OPERATIONS  *
 ********************/

/*
 * Initialize a simplex solver
 * - core = the attached smt-core object
 * - gates = the gate manager for core
 * - egraph = the attached egraph (or NULL)
 *
 * Default settings:
 * - no row saving, no jump buffer (exceptions cause abort)
 */
extern void init_simplex_solver(simplex_solver_t *solver, smt_core_t *core,
                                gate_manager_t *gates, egraph_t *egraph);


/*
 * Attach a jump buffer for exceptions
 */
extern void simplex_solver_init_jmpbuf(simplex_solver_t *solver, jmp_buf *buffer);


/*
 * Enable row saving (to support push/pop/multiple checks)
 * - must be done before any assertions
 */
static inline void simplex_enable_row_saving(simplex_solver_t *solver) {
  solver->save_rows = true;
}


/*
 * Delete: free all allocated memory
 */
extern void delete_simplex_solver(simplex_solver_t *solver);


/*
 * Get the internalization interface descriptor
 */
extern arith_interface_t *simplex_arith_interface(simplex_solver_t *solver);


/*
 * Get the solver descriptors
 */
extern th_ctrl_interface_t *simplex_ctrl_interface(simplex_solver_t *solver);
extern th_smt_interface_t *simplex_smt_interface(simplex_solver_t *solver);



/*
 * Get the egraph interface descriptors
 */
extern th_egraph_interface_t *simplex_egraph_interface(simplex_solver_t *solver);
extern arith_egraph_interface_t *simplex_arith_egraph_interface(simplex_solver_t *solver);


/*
 * Set the random seed
 */
extern void simplex_set_random_seed(simplex_solver_t *solver, uint32_t x);



/****************************
 *  PARAMETERS AND OPTIONS  *
 ***************************/

/*
 * Set the option flag: x is a bit mask
 */
static inline void simplex_set_options(simplex_solver_t *solver, uint32_t x) {
  solver->options = x;
}

static inline void simplex_enable_options(simplex_solver_t *solver, uint32_t x) {
  solver->options |= x;
}

static inline void simplex_disable_options(simplex_solver_t *solver, uint32_t x) {
  solver->options &= ~x;
}


/*
 * Check whether option(s) defined by x are enabled/disabled
 */
static inline bool simplex_option_enabled(simplex_solver_t *solver, uint32_t x) {
  return (solver->options & x) != 0;
}

static inline bool simplex_option_disabled(simplex_solver_t *solver, uint32_t x) {
  return (solver->options & x) == 0;
}


/*
 * Set the Bland-rule threshold
 */
static inline void simplex_set_bland_threshold(simplex_solver_t *solver, uint32_t n) {
  solver->bland_threshold = n;
}


/*
 * Set the propagation threshold = row size
 */
static inline void simplex_set_prop_threshold(simplex_solver_t *solver, uint32_t n) {
  solver->prop_row_size = n;
}



/*
 * Set the integer-check period
 */
static inline void simplex_set_integer_check_period(simplex_solver_t *solver, int32_t n) {
  assert(n > 0);
  solver->check_period = n;
}


/*
 * Enable/disable specific options
 */
static inline void simplex_enable_eager_lemmas(simplex_solver_t *solver) {
  simplex_enable_options(solver, SIMPLEX_EAGER_LEMMAS);
}

static inline void simplex_disable_eager_lemmas(simplex_solver_t *solver) {
  simplex_disable_options(solver, SIMPLEX_EAGER_LEMMAS);
}

static inline void simplex_enable_propagation(simplex_solver_t *solver) {
  simplex_enable_options(solver, SIMPLEX_PROPAGATION);
}

static inline void simplex_disable_propagation(simplex_solver_t *solver) {
  simplex_disable_options(solver, SIMPLEX_PROPAGATION);
}

static inline void simplex_enable_periodic_icheck(simplex_solver_t *solver) {
  simplex_enable_options(solver, SIMPLEX_ICHECK);
}

static inline void simplex_disable_periodic_icheck(simplex_solver_t *solver) {
  simplex_disable_options(solver, SIMPLEX_ICHECK);
}

static inline void simplex_enable_adjust_model(simplex_solver_t *solver) {
  simplex_enable_options(solver, SIMPLEX_ADJUST_MODEL);
}

static inline void simplex_disable_adjust_model(simplex_solver_t *solver) {
  simplex_disable_options(solver, SIMPLEX_ADJUST_MODEL);
}


/*
 * Enable/disable the equality propagator
 * - the default is to disable
 * - the call to enable_eqprop allocates and initialize the propagator
 * - the call to disable_eqprop deletes the propagator if any
 */
extern void simplex_enable_eqprop(simplex_solver_t *solver);

extern void simplex_disable_eqprop(simplex_solver_t *solver);


/*******************************
 *  INTERNALIZATION FUNCTIONS  *
 ******************************/

/*
 * These functions are used by the context to create atoms and
 * variables in the solver. We export them for testing, but the
 * context calls them via the arith_interface_t descriptor.
 */

/*
 * Create a new theory variable
 * - is_int indicates whether the variable should be an integer
 */
extern thvar_t simplex_create_var(simplex_solver_t *solver, bool is_int);


/*
 * Create a variable that represents constant q
 */
extern thvar_t simplex_create_const(simplex_solver_t *solver, rational_t *q);


/*
 * Create a theory variable equal to p
 * - map defines a mapping from terms of p to simplex variables:
 *   p is of the form a_0 t_0 + ... + a_n t_n where t_0, ..., t_n are arithmetic terms
 *   map[i] is the simplex variable that's the internalization of t_i
 *   (except that map[0] = null_thvar if t_0 is const_idx)
 * - the function creates a simplex variable y that represents
 *   a_0 map[0] + ... + a_n map[n]
 */
extern thvar_t simplex_create_poly(simplex_solver_t *solver, polynomial_t *p, thvar_t *map);


/*
 * Product internalization: always fails with exception FORMULA_NOT_LINEAR
 */
extern thvar_t simplex_create_pprod(simplex_solver_t *solver, pprod_t *p, thvar_t *map);


/*
 * Create the atom x == 0 or x >= 0
 * - this attach the atom to the smt_core
 */
extern literal_t simplex_create_eq_atom(simplex_solver_t *solver, thvar_t x);
extern literal_t simplex_create_ge_atom(simplex_solver_t *solver, thvar_t x);


/*
 * Create the atom p == 0 or p >= 0
 * - p and map are as in create_poly
 */
extern literal_t simplex_create_poly_eq_atom(simplex_solver_t *solver, polynomial_t *p, thvar_t *map);
extern literal_t simplex_create_poly_ge_atom(simplex_solver_t *solver, polynomial_t *p, thvar_t *map);


/*
 * Create the atom x - y == 0
 * - x and y are two theory variables
 */
extern literal_t simplex_create_vareq_atom(simplex_solver_t *solver, thvar_t x, thvar_t y);


/*
 * Assert a top-level constraint (either x == 0 or x != 0 or x >= 0 or x < 0)
 * - tt indicates whether the constraint or its negation must be asserted
 *   tt == true  --> assert x == 0 (or x >= 0)
 *   tt == false --> assert x != 0 (or x < 0)
 */
extern void simplex_assert_eq_axiom(simplex_solver_t *solver, thvar_t x, bool tt);
extern void simplex_assert_ge_axiom(simplex_solver_t *solver, thvar_t x, bool tt);


/*
 * Assert a top-level constraint (either p == 0 or p != 0 or p >= 0 or p < 0)
 * - p and map are as in create_poly
 * - tt indicates whether the constraint or its negation must be asserted
 *   tt == true  --> assert p == 0 or p >= 0
 *   tt == false --> assert p != 0 or p < 0
 */
extern void simplex_assert_poly_eq_axiom(simplex_solver_t *solver, polynomial_t *p, thvar_t *map, bool tt);
extern void simplex_assert_poly_ge_axiom(simplex_solver_t *solver, polynomial_t *p, thvar_t *map, bool tt);


/*
 * If tt == true --> assert (x - y == 0)
 * If tt == false --> assert (x - y != 0)
 */
extern void simplex_assert_vareq_axiom(simplex_solver_t *solver, thvar_t x, thvar_t y, bool tt);


/*
 * Assert (c ==> x == y)
 */
extern void simplex_assert_cond_vareq_axiom(simplex_solver_t *solver, literal_t c, thvar_t x, thvar_t y);



/***************************
 *  SMT/CONTROL FUNCTIONS  *
 **************************/

/*
 * The core or egraph invokes these functions via the smt or ctrl interface
 * descriptors. We export them for testing.
 */

/*
 * Prepare for search, after internalization
 * - build the initial tableau, eliminates variables with no atom attached
 *   (and remove rows) if that's possible
 * - if an inconsistency is detected then record an empty conflict in the core
 */
extern void simplex_start_search(simplex_solver_t *solver);

/*
 * Stop the search: sets flag solver->interrupted to true and
 * stops the diophantine solver if it's active.
 * - the solver->interrupted flag is set to false by start_search
 * - currently, the interrupted flag is checked in every iteration
 *   of the make feasible procedure
 */
extern void simplex_stop_search(simplex_solver_t *solver);

/*
 * Assert atom attached to literal l
 * - the atom is identified by its index in the solver's atom table, which is stored
 *   into a (void *) pointer (cf. arith_atomtable.h).
 * This function is called when l is assigned to true by the core
 * - atom is the arithmetic atom attached to a boolean variable v = var_of(l)
 * - if l is positive (i.e., pos_lit(v)), assert the atom
 * - if l is negative (i.e., neg_lit(v)), assert its negation
 * If the atom is redundant, nothing is done, otherwise a new bound
 * with explanation l is pushed into the propagation queue
 * (for equality atom, two new bounds).
 * Always return true.
 */
extern bool simplex_assert_atom(simplex_solver_t *solver, void *atom, literal_t l);

/*
 * Perform one round of propagation:
 * - process all asserted bounds in the assertion queue
 * - check for consistency
 * - propagate implied bounds
 * - return true if no conflict was detected
 * - return false if a conflict was detected, in that case the conflict
 *   clause is stored in the core
 */
extern bool simplex_propagate(simplex_solver_t *solver);


/*
 * Support for theory-branching heuristic
 * - evaluate atom attached to l in the current simplex assignment
 * - the result is either l or (not l)
 * - if atom is true, return pos_lit(var_of(l))
 * - if atom is false, return neg_lit(var_of(l))
 */
extern literal_t simplex_select_polarity(simplex_solver_t *solver, void *atom, literal_t l);


/*
 * Final check
 */
extern fcheck_code_t simplex_final_check(simplex_solver_t *solver);


/*
 * Expand explanation expl into a conjunction of literals
 * - expl is the antecedent for l
 * - the explanation literals are stored in *v
 */
extern void simplex_expand_explanation(simplex_solver_t *solver, literal_t l, aprop_header_t *expl, ivector_t *v);

/*
 * Start a new decision level
 */
extern void simplex_increase_decision_level(simplex_solver_t *solver);

/*
 * Backtrack to back_level
 * - keep the current assignment
 * - remove all bounds asserted or implied at levels > back_level
 */
extern void simplex_backtrack(simplex_solver_t *solver, uint32_t back_level);

/*
 * Push/pop/reset
 */
extern void simplex_push(simplex_solver_t *solver);
extern void simplex_pop(simplex_solver_t *solver);
extern void simplex_reset(simplex_solver_t *solver);



/*
 * Model construction
 */
extern void simplex_build_model(simplex_solver_t *solver);
extern bool simplex_value_in_model(simplex_solver_t *solver, int32_t x, arithval_in_model_t* res);
extern void simplex_free_model(simplex_solver_t *solver);



/*********************
 *  GET STATISTICS   *
 ********************/

/*
 * Fill in the internal statistics structure
 * - most counters are setup/incremented during the search
 * - this function sets the other counters
 */
extern void simplex_collect_statistics(simplex_solver_t *solver);


/*
 * Statistics on problem size (at the start of search)
 * - these are set on a call to simplex_start_search
 */
static inline uint32_t simplex_num_init_vars(simplex_solver_t *solver) {
  return solver->stats.num_init_vars;
}

static inline uint32_t simplex_num_init_rows(simplex_solver_t *solver) {
  return solver->stats.num_init_rows;
}

static inline uint32_t simplex_num_init_atoms(simplex_solver_t *solver) {
  return solver->stats.num_atoms;
}


/*
 * Problem size
 */
static inline uint32_t simplex_num_vars(simplex_solver_t *solver) {
  return solver->vtbl.nvars;
}

static inline uint32_t simplex_num_rows(simplex_solver_t *solver) {
  return solver->matrix.nrows;
}

static inline uint32_t simplex_num_atoms(simplex_solver_t *solver) {
  return solver->atbl.natoms;
}


/*
 * Statistics on search
 */
static inline uint32_t simplex_num_pivots(simplex_solver_t *solver) {
  return solver->stats.num_pivots;
}

static inline uint32_t simplex_num_make_feasible(simplex_solver_t *solver) {
  return solver->stats.num_make_feasible;
}

static inline uint32_t simplex_num_conflicts(simplex_solver_t *solver) {
  return solver->stats.num_conflicts;
}

static inline uint32_t simplex_num_interface_lemmas(simplex_solver_t *solver) {
  return solver->stats.num_interface_lemmas;
}


/*
 * Statistics for integer/mixed integer problems
 */
static inline uint32_t simplex_num_integer_vars(simplex_solver_t *solver) {
  return num_integer_vars(&solver->vtbl);
}

static inline uint32_t simplex_num_make_integer_feasible(simplex_solver_t *solver) {
  return solver->stats.num_make_intfeasible;
}

static inline uint32_t simplex_num_branch_and_bound(simplex_solver_t *solver) {
  return solver->stats.num_branch_atoms;
}

static inline uint32_t simplex_num_gomory_cuts(simplex_solver_t *solver) {
  return solver->stats.num_gomory_cuts;
}

static inline uint32_t simplex_num_bound_conflicts(simplex_solver_t *solver) {
  return solver->stats.num_bound_conflicts;
}

static inline uint32_t simplex_num_bound_recheck_conflicts(simplex_solver_t *solver) {
  return solver->stats.num_bound_recheck_conflicts;
}

static inline uint32_t simplex_num_itest_conflicts(simplex_solver_t *solver) {
  return solver->stats.num_itest_conflicts;
}

static inline uint32_t simplex_num_itest_bound_conflicts(simplex_solver_t *solver) {
  return solver->stats.num_itest_bound_conflicts;
}

static inline uint32_t simplex_num_itest_recheck_conflicts(simplex_solver_t *solver) {
  return solver->stats.num_itest_recheck_conflicts;
}

static inline uint32_t simplex_num_dioph_gcd_conflicts(simplex_solver_t *solver) {
  return solver->stats.num_dioph_gcd_conflicts;
}

static inline uint32_t simplex_num_dioph_checks(simplex_solver_t *solver) {
  return solver->stats.num_dioph_checks;
}

static inline uint32_t simplex_num_dioph_conflicts(simplex_solver_t *solver) {
  return solver->stats.num_dioph_conflicts;
}

static inline uint32_t simplex_num_dioph_bound_conflicts(simplex_solver_t *solver) {
  return solver->stats.num_dioph_bound_conflicts;
}

static inline uint32_t simplex_num_dioph_recheck_conflicts(simplex_solver_t *solver) {
  return solver->stats.num_dioph_recheck_conflicts;
}





/********************************
 *  EGRAPH INTERFACE FUNCTIONS  *
 *******************************/

/*
 * These functions record egraph assertions in the simplex queue. Assertions
 * are processed when simplex_propagate is called.
 */

/*
 * Assert that x1 and x2 are equal
 * - id = edge index to be used in a subsequent call to egraph_explain_term_eq
 * - x1 and x2 are two variables attached to two egraph terms t1 and t2
 * - this function is called when t1 and t2 become equal in the egraph
 */
extern void simplex_assert_var_eq(simplex_solver_t *solver, thvar_t x1, thvar_t x2, int32_t id);


/*
 * Assert that x1 and x2 are distinct
 * - x1 and x2 are two variables attached to two egraph terms t1 and t2
 * - this function is called when t1 and t2 become distinct in the egraph
 */
extern void simplex_assert_var_diseq(simplex_solver_t *solver, thvar_t x1, thvar_t x2, composite_t *hint);


/*
 * Assert that all variables a[0] ... a[n-1] are pairwise distinct
 * - they are attached to egraph terms t[0] ... t[n-1]
 * - the function is called when (distinct t[0] ... t[n-1]) is asserted in the egraph
 */
extern void simplex_assert_var_distinct(simplex_solver_t *solver, uint32_t n, thvar_t *a, composite_t *hint);


/*
 * Check whether x1 and x2 are distinct at the base level
 */
extern bool simplex_check_disequality(simplex_solver_t *solver, thvar_t x1, thvar_t x2);



/*
 * Construct an internal model and check for its consistency with the egraph
 * - generate interface equalities for conflicts between model and egraph
 * - return the number of interface equalities created
 * - max_eq = bound on the number of interface equalities allowed
 */
extern uint32_t simplex_reconcile_model(simplex_solver_t *solver, uint32_t max_eq);



/*
 * Select polarity when branching on decision literal l
 * - l is attached to an egraph equality atom (eq u1 u2)
 * - x1 and x2 are the theory variables attached to u1 and u2, respectively
 * - return l is x1 and x2 have the same value in the current tableau
 *   return (not l) otherwise
 */
extern literal_t simplex_select_eq_polarity(simplex_solver_t *solver, thvar_t x1, thvar_t x2, literal_t l);




#endif /* __SIMPLEX_H */
