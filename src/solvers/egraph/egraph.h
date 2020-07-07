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

#ifndef __EGRAPH_H
#define __EGRAPH_H

#include <assert.h>

#include "solvers/egraph/egraph_explanations.h"
#include "solvers/egraph/egraph_types.h"
#include "solvers/egraph/egraph_utils.h"



/*************************
 *  EGRAPH CONSTRUCTION  *
 ************************/

/*
 * To build an operational egraph
 * - first call init_egraph
 * - then attach whatever theory solvers are needed (in any order)
 * - initialize the core with the egraph interfaces
 * - then attach the core to the egraph (this must be done last).
 */

/*
 * Initialize: allocate internal tables and data structures
 * - ttbl = attached type table
 * - all have default sizes, defined in egraph_types.h
 * - no core is attached yet.
 */
extern void init_egraph(egraph_t *egraph, type_table_t *ttbl);

/*
 * Attach an arithmetic solver
 * - solver = pointer to the solver object
 * - ctrl, smt, eg, arith_eg = interface descriptors
 */
extern void egraph_attach_arithsolver(egraph_t *egraph,
                                      void *solver,
                                      th_ctrl_interface_t *ctrl,
                                      th_smt_interface_t *smt,
                                      th_egraph_interface_t *eg,
                                      arith_egraph_interface_t *arith_eg);

/*
 * Attach a bitvector solver
 * - solver = pointer to the solver object
 * - ctrl, smt, eg, bv_eg = interface descriptors
 */
extern void egraph_attach_bvsolver(egraph_t *egraph,
                                   void *solver,
                                   th_ctrl_interface_t *ctrl,
                                   th_smt_interface_t *smt,
                                   th_egraph_interface_t *eg,
                                   bv_egraph_interface_t *bv_eg);

/*
 * Attach a function/array subsolver
 * - solver = pointer to the subsolver object
 * - ctrl, eg, fun_eg = interface descriptors
 */
extern void egraph_attach_funsolver(egraph_t *egraph,
                                    void *solver,
                                    th_ctrl_interface_t *ctrl,
                                    th_egraph_interface_t *eg,
                                    fun_egraph_interface_t *fun_eg);

/*
 * Attach a quant subsolver
 * - solver = pointer to the subsolver object
 * - ctrl, eg, quant_eg  = interface descriptors
 */
void egraph_attach_quantsolver(egraph_t *egraph,
                               void *solver,
                               th_ctrl_interface_t *ctrl,
                               th_egraph_interface_t *eg,
                               quant_egraph_interface_t *quant_eg);


/*
 * Get the egraph control and smt interface descriptors
 */
extern th_ctrl_interface_t *egraph_ctrl_interface(egraph_t *egraph);
extern th_smt_interface_t *egraph_smt_interface(egraph_t *egraph);


/*
 * Attach a core solver:
 * - the core must be initialized with the egraph, and the interface
 *   descriptors returned by the two functions above
 * - until the core is attached, the egraph can't be used
 * - the internal egraph boolean constant is constructed at this point
 */
extern void egraph_attach_core(egraph_t *egraph, smt_core_t *core);

/*
 * Delete all tables and internal structures
 */
extern void delete_egraph(egraph_t *egraph);



/*************************
 *   TERM CONSTRUCTORS   *
 ************************/

/*
 * Non-boolean and non-tuple terms
 * -------------------------------
 * All term constructors take a type parameter that must be a type
 * defined in the type table attached to the egraph. Hash consing
 * is used for composite terms. A theory variable is created and
 * attached to new terms depending on their type and on whether the
 * relevant satellite solver is present.
 *
 * It's also possible to create a fresh variable in the egraph and
 * attach it to an existing theory variable in the bitvector, arithmetic,
 * or array solver.
 *
 *
 * Boolean terms and tuples
 * ------------------------
 * For boolean and tuple terms, the type and theory variable are set
 * automatically by the egraph. For boolean terms, an egraph atom may
 * be created too and added to the core.
 *
 * To add a boolean variable to the egraph, create a bvar_t v in the
 * core first then use bvar2term.
 *
 * IMPORTANT: Make sure the terms are type correct.  The egraph
 * assumes that all terms and classes are correctly constructed and
 * type correct but it does not check.  It uses etype[c1] and
 * etype[c2] when merging two classes, so they must be compatible.
 */


/*
 * BOOLEAN TERMS AND TUPLES
 */

/*
 * Tuples: (type = tau, etype = TUPLE, theory variable = itself)
 * - the term's body is (tuple a[0], .., a[n-1])
 */
extern eterm_t egraph_make_tuple(egraph_t *egraph, uint32_t n, occ_t *a, type_t tau);

/*
 * Atoms (type = BOOL, etype = BOOL,  theory variable = a fresh boolean variable)
 * - all return pos_occ(theory_variable)
 * - make_pred builds an uninterpreted predicate (f a[0] ... a[n])
 * - make_distinct rewrites (distinct a[0] ... a[n-1]) to a conjunction of
 *   disequalities if the distinct limit is reached.
 */
extern literal_t egraph_make_pred(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a);
extern literal_t egraph_make_eq(egraph_t *egraph, occ_t t1, occ_t t2);
extern literal_t egraph_make_distinct(egraph_t *egraph, uint32_t n, occ_t *a);


/*
 * Same thing for boolean if-then-else and or terms
 *
 * WARNING: The egraph is not complete for boolean reasoning, so
 * clauses must be added in the core if these terms are used.
 */
extern literal_t egraph_make_boolean_ite(egraph_t *egraph, occ_t c, occ_t t1, occ_t t2);
extern literal_t egraph_make_or(egraph_t *egraph, uint32_t n, occ_t *a);




/*
 * Simpler version of make_eq to be used by theory solvers.
 * This function does not check for possible simplifications.
 * In  particular, the function does not call the theory solver's
 * check_diseq (to avoid circularities).
 *
 * - t1 and t2 must be distinct.
 */
extern literal_t egraph_make_simple_eq(egraph_t *egraph, occ_t t1, occ_t t2);


/*
 * Check whether (eq t1 t2) exists and if it does return the corresponding literal.
 * - return null_literal if (eq t1 t2) does not exist
 * - return false_literal if (eq t1 t2) does exist but is not attached to an atom
 *   (and thus not attached to a boolean variable). This may happen after a call to
 *   egraph_assert_diseq_axiom(egraph, t1, t2).
 */
extern literal_t egraph_find_eq(egraph_t *egraph, occ_t t1, occ_t t2);



/*
 * OTHER TERM CONSTRUCTORS
 */

/*
 * - the type tau of the term to create is given as a parameter to the constructor
 * - a new theory variable is created if required (i.e., if the type
 *   is arithmetic, bitvector or function and the corresponding
 *   satellite solver exists).
 * - the term is activated
 *
 * Additional processing for make_variable and make_apply:
 * - if tau is a scalar type, then an instance of the scalar axiom is
 *   created (i.e., the clause (or (= t const!0) ... (= t const!k)) where
 *   k+1 = cardinality of tau.
 *
 * - if tau is a tuple type, then an instance of the skolemization axiom
 *   for tau is created. For example, if tau is (tuple (tuple int bool) int)
 *   Then we'll assert t = (make-tuple v z)
 *               where v = (make_tuple x y)
 *               and x, y, z are fresh skolem constants of the right type.
 *
 *   This is the skolemization of the axiom EXSTS x y z: t = (make-tuple (make-tuple x y) z).
 */
extern eterm_t egraph_make_constant(egraph_t *egraph, type_t tau, int32_t id);
extern eterm_t egraph_make_variable(egraph_t *egraph, type_t tau);
extern eterm_t egraph_make_apply(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a, type_t tau);
extern eterm_t egraph_make_ite(egraph_t *egraph, occ_t c, occ_t t1, occ_t t2, type_t tau);
extern eterm_t egraph_make_update(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a, occ_t v, type_t tau);

/*
 * Constructor for constant (lambda ... t):
 * - tau = result type of (lambda ... t): must be a function type
 */
extern eterm_t egraph_make_lambda(egraph_t *egraph, occ_t t, type_t tau);


/*
 * SKOLEM TERM
 */

/*
 * Generate a skolem constant of type tau
 * - if tau is (tuple tau_1 ... tau_n) this recursively
 *   generate n skolem constants x1 ... x_n of type tau_1 ... tau_n then
 *   return the term (mk_tuple x1 ... x_n)
 * - if tau is any other type, this creates a fresh variable of type tau.
 */
extern eterm_t egraph_skolem_term(egraph_t *egraph, type_t tau);



/*
 * CHECK WHETHER A GIVEN TERM EXIST
 *
 * All functions return true if a composite term with the given
 * definition already exists in the egraph. If the function
 * egraph_xxx_exists return true, a subsequent call to egraph_make_xxx
 * with identical argument will return the existing term.
 */
extern bool egraph_apply_exists(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a);
extern bool egraph_ite_exists(egraph_t *egraph, occ_t c, occ_t t1, occ_t t2);
extern bool egraph_update_exists(egraph_t *egraph, occ_t f, uint32_t n, occ_t *a, occ_t v);
extern bool egraph_tuple_exists(egraph_t *egraph, uint32_t n, occ_t *a);
extern bool egraph_eq_exists(egraph_t *egraph, occ_t t1, occ_t t2);
extern bool egraph_distinct_exists(egraph_t *egraph, uint32_t n, occ_t *a);
extern bool egraph_or_exists(egraph_t *egraph, uint32_t n, occ_t *a);

extern bool egraph_lambda_exists(egraph_t *egraph, occ_t t, type_t tau);



/***********************
 *  THEORY VARIABLES   *
 **********************/

/*
 * Return a term t equal to boolean variable v
 * - search for an egraph atom of the form <t, v>
 * - if there is one return t
 * - otherwise, create a fresh term t (egraph variable of type BOOL)
 *   and construct the atom <t, v>
 * - if v already has a non-egraph atom attached,
 *   create a fresh v', assert v' == v in the core then
 *   attach t to v'
 */
extern eterm_t egraph_bvar2term(egraph_t *egraph, bvar_t v);

/*
 * Variant: convert a literal to a term occurrence
 */
static inline occ_t egraph_literal2occ(egraph_t *egraph, literal_t l) {
  return mk_occ(egraph_bvar2term(egraph, var_of(l)), sign_of_lit(l));
}

/*
 * Convert a term occurrence t to a literal
 * - t must have a boolean variable v attached
 */
static inline literal_t egraph_occ2literal(egraph_t *egraph, occ_t t) {
  assert(egraph_occ_is_bool(egraph, t));
  return mk_lit(egraph_term_base_thvar(egraph, term_of_occ(t)), polarity_of_occ(t));
}

/*
 * Get a tuple term u such that u == t
 * - return null_eterm if there is none. t must have TUPLE type
 */
extern eterm_t egraph_get_tuple_in_class(egraph_t *egraph, eterm_t t);


/*
 * Return a term t of type tau and attach theory variable v to t
 * - t is a fresh egraph variable
 * - v must not be attached to another term t'
 * - there must be a theory solver for the type tau
 */
extern eterm_t egraph_thvar2term(egraph_t *egraph, thvar_t v, type_t tau);




/******************************************
 *  EQUALITY/DISTINCT/DISEQUALITY CHECKS  *
 *****************************************/

/*
 * Check whether t1 and t2 are equal in egraph
 */
static inline bool egraph_check_eq(egraph_t *egraph, occ_t t1, occ_t t2) {
  return egraph_equal_occ(egraph, t1, t2);
}

/*
 * Check whether t1 and t2 are known to be distinct
 * Returns true in the following cases:
 * 1) t1 and (not t2) are equal
 * 2) there are distinct constants a1 and a2 with t1 == a1 and t2 == a2
 * 3) there's a term v = (eq u1 u2), such that v == false, and
 *     t1 == u1, t2 == u2 or t1 == u2, t2 == u1
 * 4) there's a term v = (distinct u_1 ... u_n) such that v == true,
 *    and t1 == u_i and t2 == u_j with i /= j
 */
extern bool egraph_check_diseq(egraph_t *egraph, occ_t t1, occ_t t2);


/*
 * Check whether t1 and t2 are distinct via the theory solver
 * Return true if t1 and t2 are attached to two theory variables x1 and x2
 * and the corresponding theory solver knows that x1 and x2 are distinct
 */
extern bool egraph_check_theory_diseq(egraph_t *egraph, occ_t t1, occ_t t2);


/*
 * Check whether d = (distinct u_1 ... u_n) is false.
 * Returns true if u_i == u_j for i/=j
 */
extern bool egraph_check_distinct_false(egraph_t *egraph, composite_t *d);


/*
 * Check whether d = (distinct u_1 ... u_n) is true.
 */
extern bool egraph_check_distinct_true(egraph_t *egraph, composite_t *d);


/*
 * Check whether d = (distinct u_1 ... u_n) is true.
 * Incomplete but cheap version:
 * - return true if u_1 ... u_n are equal to n distinct constants
 * or if an asserted predicate (distinct t_1 ... t_m) implies d
 */
extern bool egraph_fast_check_distinct_true(egraph_t *egraph, composite_t *d);





/*******************************************
 *  DIRECT CALLS TO THE CONTROL FUNCTIONS  *
 ******************************************/

/*
 * The following functions are the egraph control and smt interfaces.
 * They are intended only for testing.
 */
extern void egraph_start_search(egraph_t *egraph);
extern void egraph_increase_decision_level(egraph_t *egraph);
extern void egraph_push(egraph_t *egraph);
extern void egraph_pop(egraph_t *egraph);
extern void egraph_reset(egraph_t *egraph);
extern void egraph_backtrack(egraph_t *egraph, uint32_t back_level);
extern bool egraph_propagate(egraph_t *egraph);
extern fcheck_code_t egraph_final_check(egraph_t *egraph);

extern bool egraph_assert_atom(egraph_t *egraph, void *atom, literal_t l);
extern void egraph_expand_explanation(egraph_t *egraph, literal_t l, void *expl, ivector_t *v);




/***********************
 *  DIRECT ASSERTIONS  *
 **********************/

/*
 * Assert (t == true) with explanation l
 * - term_of(t) must be a boolean term
 * - this does not do any propagation: it just pushes the equality
 *  (t == true) into the propagation queue.
 * call propagate to check consistency.
 */
extern void egraph_assert_term(egraph_t *egraph, occ_t t, literal_t l);

/*
 * Assert (t1 == t2) with explanation l
 * - call propagate to check consistency
 */
extern void egraph_assert_eq(egraph_t *egraph, occ_t t1, occ_t t2, literal_t l);


/*
 * Axioms must not be asserted if decision_level > base_level
 * All assert operations just push an equality in the propagation queue
 * Propagate must be used to check consistency.
 */

/*
 * Axiom (t == true)
 */
extern void egraph_assert_axiom(egraph_t *egraph, occ_t t);

/*
 * Axiom (t1 == t2)
 */
extern void egraph_assert_eq_axiom(egraph_t *egraph, occ_t t1, occ_t t2);

/*
 * Axiom (t1 != t2)
 */
extern void egraph_assert_diseq_axiom(egraph_t *egraph, occ_t t1, occ_t t2);

/*
 * Axiom (distinct t[0] ... t[n-1])
 * - n must be >= 3
 */
extern void egraph_assert_distinct_axiom(egraph_t *egraph, uint32_t n, occ_t *t);

/*
 * Axiom not (distinct t[0] ... t[n-1])
 * - n must be >= 3
 */
extern void egraph_assert_notdistinct_axiom(egraph_t *egraph, uint32_t n, occ_t *t);


/*
 * Axiom (f t[0] ... t[n-1]) where f is a boolean function
 * - this is equivalent to make_pred + add_unit_clause but it saves the
 *   extra boolean variable.
 */
extern void egraph_assert_pred_axiom(egraph_t *egraph, occ_t f, uint32_t n, occ_t *t);


/*
 * Axiom not (f t[0] ... t[n-1]) where f is a boolean function
 */
extern void egraph_assert_notpred_axiom(egraph_t *egraph, occ_t f, uint32_t n, occ_t *t);




/****************************************
 *  PROPAGATION FROM SATELLITE SOLVERS  *
 ***************************************/

/*
 * Add equality (t1 == t2) to the propagation queue with explanation expl
 * - id = code to identify the satellite solver
 *   valid codes are EXPL_ARITH_PROPAGATION, EXPL_BV_PROPAGATION, EXPL_FUN_PROPAGATION
 * - expl = any data that the solver needs to expand the explanation if needed
 */
extern void egraph_propagate_equality(egraph_t *egraph, eterm_t t1, eterm_t t2, expl_tag_t id, void *expl);




/***********************************
 *  SUPPORT FOR THE ARRAY SOLVER   *
 **********************************/

/*
 * Get the lambda tag to function type tau
 */
extern int32_t egraph_get_lambda_tag(egraph_t *egraph, type_t tau);

/*
 * Collect all composite terms of the form (apply g ....)
 * where g is in the same class as f
 * - only the congruence roots are collected
 * - they are added to the pointer vector v (cf. ptr_vectors)
 */
extern void egraph_collect_applications(egraph_t *egraph, eterm_t f, pvector_t *v);


/*
 * Given a composite term c = (apply f i_1 ... i_n), search for a term
 * congruent to c with the function f replaced by g.
 * - return the composite congruent to (apply g i_1 ... i_n) if the term exists
 * - return NULL_COMPOSITE otherwise
 */
extern composite_t *egraph_find_modified_application(egraph_t *egraph, eterm_t g, composite_t *c);


#if 0

// NOT USED
/*
 * Return a randomly chosen class label of type tau
 */
extern elabel_t egraph_get_label_for_type(egraph_t *egraph, type_t tau);

#endif


/*
 * Fill in array a with at most n distinct class labels of type tau.
 * If there are fewer than n classes of type tau, then the array is
 * partially filled (in a[0 ... k-1]).
 * - n must be positive
 * - return k = the number of labels actually stored in a (k <= n)
 */
extern uint32_t egraph_get_labels_for_type(egraph_t *egraph, type_t tau, elabel_t *a, uint32_t n);


#if 0

// NOT USED
/*
 * Number of classes of type tau in the egraph
 */
extern uint32_t egraph_num_classes_of_type(egraph_t *egraph, type_t tau);

#endif

/*
 * Partition the (apply ...) composites into equivalence classes
 * - only composites that are present in the congruence table are considered
 *   (i.e., the roots of the congruence classes)
 * - two terms (apply f t_1 ... t_n) and (apply g u_1 ... u_m)
 *   are in the same partition if their arguments are equal in the egraph
 *   (i.e., if n = m and t_1 == u_1 and ... and t_n == u_m)
 * The resulting partition is stored in the egraph's internal ppar_t structure.
 * The classes that contain at least 2 elements are stored in pp->classes
 * (cf. ptr_partitions.h).
 */
extern void egraph_build_arg_partition(egraph_t *egraph);


/*
 * Get a pointer to the egraph's partition structure
 * - NULL if the partition is not allocated
 * - it's allocated on the first call to egraph_build_arg_partition
 */
static inline ppart_t *egraph_app_partition(egraph_t *egraph) {
  return egraph->app_partition;
}


/*
 * Reset the partition structure
 */
static inline void egraph_reset_app_partition(egraph_t *egraph) {
  assert(egraph->app_partition != NULL);
  reset_ptr_partition(egraph->app_partition);
}






/**************************
 *   MODEL CONSTRUCTION   *
 *************************/

/*
 * Build a model: map classes to concrete values
 * - vtbl = table where the concrete values must be constructed
 */
extern void egraph_build_model(egraph_t *egraph, value_table_t *vtbl);


/*
 * Return the value of term occurrence t in the egraph model
 * - vtbl = table where concrete values must be constructed (that's the
 *   same table as is passed to the egraph_build_model function).
 */
extern value_t egraph_get_value(egraph_t *egraph, value_table_t *vtbl, occ_t t);


/*
 * Free internal structures used by the model
 */
extern void egraph_free_model(egraph_t *egraph);



/****************
 *  STATISTICS  *
 ***************/

/*
 * On problem size
 */

// egraph_num_terms and egraph_num_classes are defined in egraph_utils.h

static inline uint32_t egraph_num_atoms(egraph_t *egraph) {
  return egraph->natoms;
}

static inline uint32_t egraph_num_distincts(egraph_t *egraph) {
  return egraph->ndistincts;
}

/*
 * Search statistics
 */
static inline uint32_t egraph_num_eq_props(egraph_t *egraph) {
  return egraph->stats.eq_props;
}

static inline uint32_t egraph_num_bool_props(egraph_t *egraph) {
  return egraph->stats.th_props; // from egraph to core
}

static inline uint32_t egraph_num_conflicts(egraph_t *egraph) {
  return egraph->stats.th_conflicts;
}

static inline uint32_t egraph_num_nd_lemmas(egraph_t *egraph) {
  return egraph->stats.nd_lemmas; // not distinct lemmas
}

static inline uint32_t egraph_num_aux_eqs(egraph_t *egraph) {
  return egraph->stats.aux_eqs;
}

static inline uint32_t egraph_num_boolack_lemmas(egraph_t *egraph) {
  return egraph->stats.boolack_lemmas; // Boolean Ackermann lemmas
}

static inline uint32_t egraph_num_ack_lemmas(egraph_t *egraph) {
  return egraph->stats.ack_lemmas; // non-Boolean Ackermann lemmas
}

static inline uint32_t egraph_all_ackermann(egraph_t *egraph) {
  return egraph_num_boolack_lemmas(egraph) + egraph_num_ack_lemmas(egraph);
}

static inline uint32_t egraph_num_final_checks(egraph_t *egraph) {
  return egraph->stats.final_checks;
}

static inline uint32_t egraph_num_interface_eqs(egraph_t *egraph) {
  return egraph->stats.interface_eqs; // interface equalities or lemmas created by final check
}



#endif /* __EGRAPH_H */
