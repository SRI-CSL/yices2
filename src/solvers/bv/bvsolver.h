/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#ifndef __BVSOLVER_H
#define __BVSOLVER_H

#include <stdbool.h>

#include "solvers/bv/bvsolver_types.h"



/*********************
 *  MAIN OPERATIONS  *
 ********************/

/*
 * Initialize a bit-vector solver
 * - core = the attached smt core
 * - egraph = the attached egraph (or NULL)
 */
extern void init_bv_solver(bv_solver_t *solver, smt_core_t *core, egraph_t *egraph);


/*
 * Attach a jump buffer for exception handling
 */
extern void bv_solver_init_jmpbuf(bv_solver_t *solver, jmp_buf *buffer);


/*
 * Delete solver
 */
extern void delete_bv_solver(bv_solver_t *solver);


/*
 * Get the solver's interface descriptors
 */
// internalization interface (used by the context)
extern bv_interface_t *bv_solver_bv_interface(bv_solver_t *solver);

// control and smt interfaces (used by the core and egraph)
extern th_ctrl_interface_t *bv_solver_ctrl_interface(bv_solver_t *solver);
extern th_smt_interface_t *bv_solver_smt_interface(bv_solver_t *solver);

// egraph-specific interfaces
extern th_egraph_interface_t *bv_solver_egraph_interface(bv_solver_t *solver);
extern bv_egraph_interface_t *bv_solver_bv_egraph_interface(bv_solver_t *solver);



/*
 * FOR TESTING: convert the constraints to CNF
 * - return false if there's a conflict
 */
extern bool bv_solver_bitblast(bv_solver_t *solver);
extern bool bv_solver_compile(bv_solver_t *solver);



/*******************************
 *  INTERNALIZATION FUNCTIONS  *
 ******************************/

/*
 * These functions are used by the context to create atoms and variables
 * in the bit-vector solver. We export them for testing. They are normally
 * called via the bvsolver_interface_t descriptor.
 */

/*
 * Create a new variable of n bits
 */
extern thvar_t bv_solver_create_var(bv_solver_t *solver, uint32_t n);

/*
 * Create a variable equal to constant c
 */
extern thvar_t bv_solver_create_const(bv_solver_t *solver, bvconst_term_t *c);
extern thvar_t bv_solver_create_const64(bv_solver_t *solver, bvconst64_term_t *c);


/*
 * Internalize the polynomial p
 * - map defines how terms of p are replaced by variables of solver:
 *   if p is of the form a_0 t_0 + ... + a_n t_n
 *   then map contains n+1 elements variables, and map[i] is the internalization of t_i
 * - exception: if t_0 is const_idx then map[0] = null_thvar
 */
extern thvar_t bv_solver_create_bvpoly(bv_solver_t *solver, bvpoly_t *p, thvar_t *map);
extern thvar_t bv_solver_create_bvpoly64(bv_solver_t *solver, bvpoly64_t *p, thvar_t *map);


/*
 * Internalize the power-product p = t_0^d_0 * ... * t_n^d_n
 * - map[i] stores the theory variable equal to the internalization of t_i
 */
extern thvar_t bv_solver_create_pprod(bv_solver_t *solver, pprod_t *p, thvar_t *map);


/*
 * Internalize the bit array a[0 ... n-1]
 * - each element a[i] is a literal in the core
 */
extern thvar_t bv_solver_create_bvarray(bv_solver_t *solver, literal_t *a, uint32_t n);


/*
 * Internalize the if-then-else term (ite c x y)
 * - c is a literal in the core
 * - x and y are two previously created theory variables
 */
extern thvar_t bv_solver_create_ite(bv_solver_t *solver, literal_t c, thvar_t x, thvar_t y);


/*
 * Internalize the binary operations
 */
extern thvar_t bv_solver_create_bvdiv(bv_solver_t *solver, thvar_t x, thvar_t y);
extern thvar_t bv_solver_create_bvrem(bv_solver_t *solver, thvar_t x, thvar_t y);
extern thvar_t bv_solver_create_bvsdiv(bv_solver_t *solver, thvar_t x, thvar_t y);
extern thvar_t bv_solver_create_bvsrem(bv_solver_t *solver, thvar_t x, thvar_t y);
extern thvar_t bv_solver_create_bvsmod(bv_solver_t *solver, thvar_t x, thvar_t y);

extern thvar_t bv_solver_create_bvshl(bv_solver_t *solver, thvar_t x, thvar_t y);
extern thvar_t bv_solver_create_bvlshr(bv_solver_t *solver, thvar_t x, thvar_t y);
extern thvar_t bv_solver_create_bvashr(bv_solver_t *solver, thvar_t x, thvar_t y);


/*
 * Return the i-th bit of theory variable x as a literal
 */
extern literal_t bv_solver_select_bit(bv_solver_t *solver, thvar_t x, uint32_t i);


/*
 * Create atoms and return the corresponding core literal
 * Three types of atoms are supported
 *  (eq x y): equality
 *  (ge x y):  (x >= y) with x and y interpreted as unsigned integers
 *  (sge x y): (x >= y) with x and y interpreted as signed integers
 */
extern literal_t bv_solver_create_eq_atom(bv_solver_t *solver, thvar_t x, thvar_t y);
extern literal_t bv_solver_create_ge_atom(bv_solver_t *solver, thvar_t x, thvar_t y);
extern literal_t bv_solver_create_sge_atom(bv_solver_t *solver, thvar_t x, thvar_t y);


/*
 * Assertion of top-level axioms
 * - tt indicates whether the axiom or its negation must be asserted
 *   tt = true --> assert (eq x y) or (ge x y) or (sge x y)
 *   tt = fasle --> assert (not (eq x y)) or (not (ge x y)) or (not (sge x y))
 */
extern void bv_solver_assert_eq_axiom(bv_solver_t *solver, thvar_t x, thvar_t y, bool tt);
extern void bv_solver_assert_ge_axiom(bv_solver_t *solver, thvar_t x, thvar_t y, bool tt);
extern void bv_solver_assert_sge_axiom(bv_solver_t *solver, thvar_t x, thvar_t y, bool tt);


/*
 * Assert that bit i of x is equal to tt
 */
extern void bv_solver_set_bit(bv_solver_t *solver, thvar_t x, uint32_t i, bool tt);


/*
 * Attach egraph term t to variable x
 */
extern void bv_solver_attach_eterm(bv_solver_t *solver, thvar_t x, eterm_t t);


/*
 * Get the egraph term attached to x
 * - return null_eterm if x has no term attached
 */
extern eterm_t bv_solver_eterm_of_var(bv_solver_t *solver, thvar_t x);



/*
 * Get the variables that x is compiled to
 * - return null_thvar if x is not compiled to anything
 */
extern thvar_t bv_solver_var_compiles_to(bv_solver_t *solver, thvar_t x);



/****************
 *  STATISTICS  *
 ***************/

/*
 * Number of variables and atoms
 */
static inline uint32_t bv_solver_num_vars(bv_solver_t *solver) {
  return solver->vtbl.nvars;
}

static inline uint32_t bv_solver_num_atoms(bv_solver_t *solver) {
  return solver->atbl.natoms;
}


/*
 * Number of nodes in the DAG
 */
static inline uint32_t bv_solver_dag_size(bv_solver_t *solver) {
  return (solver->compiler != NULL) ? solver->compiler->dag.nelems : 0;
}

static inline uint32_t bv_solver_num_leaf_nodes(bv_solver_t *solver) {
  return (solver->compiler != NULL) ? bvc_num_complex_nodes(&solver->compiler->dag) : 0;
}

static inline uint32_t bv_solver_num_elem_nodes(bv_solver_t *solver) {
  return (solver->compiler != NULL) ? bvc_num_elem_nodes(&solver->compiler->dag) : 0;
}

static inline uint32_t bv_solver_num_complex_nodes(bv_solver_t *solver) {
  return (solver->compiler != NULL) ? bvc_num_complex_nodes(&solver->compiler->dag) : 0;
}


/*
 * Atoms per type
 */
static inline uint32_t bv_solver_num_eq_atoms(bv_solver_t *solver) {
  return solver->stats.eq_atoms;
}

static inline uint32_t bv_solver_num_ge_atoms(bv_solver_t *solver) {
  return solver->stats.ge_atoms;
}

static inline uint32_t bv_solver_num_sge_atoms(bv_solver_t *solver) {
  return solver->stats.sge_atoms;
}


/*
 * Search statistics: these counters are all zero unless the solver
 * is attached to the egraph
 */
static inline uint32_t bv_solver_on_the_fly_atoms(bv_solver_t *solver) {
  return solver->stats.on_the_fly_atoms; // equality atoms created after bitblasting
}

static inline uint32_t bv_solver_equiv_lemmas(bv_solver_t *solver) {
  return solver->stats.equiv_lemmas;
}

static inline uint32_t bv_solver_interface_lemmas(bv_solver_t *solver) {
  return solver->stats.interface_lemmas;
}



/************************
 *  MODEL CONSTRUCTION  *
 ***********************/

/*
 * Build model: assign a concrete bitvector value to all variables
 * - when this is called, the context has determined that the
 *   constraints are SAT (so a model does exist)
 */
extern void bv_solver_build_model(bv_solver_t *solver);


/*
 * Copy the value assigned to x in the model into buffer c
 * - return true if the value is available
 * - return false if the solver has no model
 */
extern bool bv_solver_value_in_model(bv_solver_t *solver, thvar_t x, bvconstant_t *c);


/*
 * Delete whatever is used to store the model
 */
extern void bv_solver_free_model(bv_solver_t *solver);



/********************************
 *  EGRAPH INTERFACE FUNCTIONS  *
 *******************************/

/*
 * Assert that x1 and x2 are equal:
 * - id = edge index to be used in a subsequent call to egraph_explain_term_eq
 * - turn this into an axiom if possible
 * - otherwise push the equality into a queue for processing on the next
 *   call to propagate.
 */
extern void bv_solver_assert_var_eq(bv_solver_t *solver, thvar_t x1, thvar_t x2, int32_t id);


/*
 * Assert that x1 and x2 are distinct
 * - hint = egraph hint for the disequality
 * - turn this into an axiom if possible
 * - otherwise push the equality into a queue for processing on the next
 *   call to propagate.
 */
extern void bv_solver_assert_var_diseq(bv_solver_t *solver, thvar_t x1, thvar_t x2, composite_t *hint);

/*
 * Assert that a[0,...n-1] are all distinct
 * - hint = hint for egraph explanation
 * - this gets converted into n * (n-1) pairwise disequalities
 */
extern void bv_solver_assert_var_distinct(bv_solver_t *solver, uint32_t n, thvar_t *a, composite_t *hint);


/*
 * Check whether x1 and x2 are distinct at the base level
 */
extern bool bv_solver_check_disequality(bv_solver_t *solver, thvar_t x1, thvar_t x2);


/*
 * Generate interface equalities for conflicts between model and egraph
 * - return the number of interface equalities created
 * - max_eq = bound on the number of interface equalities allowed
 */
extern uint32_t bv_solver_reconcile_model(bv_solver_t *solver, uint32_t max_eq);




/***************************
 *  SMT/CONTROL FUNCTIONS  *
 **************************/

/*
 * The core or egraph invokes these functions via the smt or ctrl interface
 * descriptors. We export them for testing.
 */

/*
 * Prepare for search, after internalization
 */
extern void bv_solver_start_search(bv_solver_t *solver);

/*
 * Assert atom attached to literal l
 * This function is called when l is assigned to true by the core
 * - atom is the arithmetic atom attached to a boolean variable v = var_of(l)
 * - if l is positive (i.e., pos_lit(v)), assert the atom
 * - if l is negative (i.e., neg_lit(v)), assert its negation
 * Return false if that causes a conflict, true otherwise.
 */
extern bool bv_solver_assert_atom(bv_solver_t *solver, void *atom, literal_t l);

/*
 * Perform one round of propagation:
 * - return true if no conflict was detected
 * - return false if a conflict was detected, in that case the conflict
 *   clause is stored in the core
 */
extern bool bv_solver_propagate(bv_solver_t *solver);


/*
 * Support for theory-branching heuristic
 * - evaluate atom attached to l in the current simplex assignment
 * - the result is either l or (not l)
 * - if atom is true, return pos_lit(var_of(l))
 * - if atom is false, return neg_lit(var_of(l))
 */
extern literal_t bv_solver_select_polarity(bv_solver_t *solver, void *atom, literal_t l);


/*
 * Final check
 */
extern fcheck_code_t bv_solver_final_check(bv_solver_t *solver);


/*
 * Start a new decision level
 */
extern void bv_solver_increase_decision_level(bv_solver_t *solver);

/*
 * Backtrack to back_level
 */
extern void bv_solver_backtrack(bv_solver_t *solver, uint32_t back_level);


/*
 * Push/pop/reset
 */
extern void bv_solver_push(bv_solver_t *solver);
extern void bv_solver_pop(bv_solver_t *solver);
extern void bv_solver_reset(bv_solver_t *solver);




#endif /* __BVSOLVER_H */
