/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*************************
 *  EGRAPH EXPLANATIONS  *
 ************************/

#ifndef __EGRAPH_EXPLANATIONS_H
#define __EGRAPH_EXPLANATIONS_H

#include <stdint.h>
#include <stdbool.h>

#include "solvers/egraph/egraph_types.h"


/*
 * ANTECEDENT DATA FOR PROPAGATION QUEUE
 */

/*
 * Construct an antecedent for (distinct t_1 ... t_n) == false
 * - c = composite term = (distinct t_1 ... t_n)
 * - x = class label
 * - k = edge id in egraph->stack, where the antecedent will be stored
 * x must be the label of two children t_i and t_j of c (with i/=j)
 */
extern void gen_distinct_simpl_antecedent(egraph_t *egraph, composite_t *c, elabel_t x, int32_t k);

/*
 * Antecedent for (distinct t_1 ... t_n) == (distinct u_1 ... u_n)
 * - build a permutation v[1 ... n] of u_1 ... u_n such that t_i == v[i]
 * - k = index where the antecedent must be stored
 * Side effect: uses egraph->imap
 */
extern void gen_distinct_congruence_antecedent(egraph_t *egraph, composite_t *c1, composite_t *c2, int32_t k);

/*
 * Construct an antecedent for (or t_1 ... t_n) == (or u_1 ... u_m),
 * when these two terms are congruent.
 * - c1 = composite term = (or t_1 ... t_n)
 * - c2 = composite term = (or u_1 ... u_m)
 * - k = edge id in egraph->stack, where the antecedent will be stored
 * Side effect: uses egraph->imap
 */
extern void gen_or_congruence_antecedent(egraph_t *egraph, composite_t *c1, composite_t *c2, int32_t k);

/*
 * Antecedent for non-distinct propagation:
 * - d = (distinct u_1 ... u_n) == false
 * - t1 is u_m and t2 is u_l, with m != l
 * - (u_i != u_j) holds for all i<j, except m,l
 * them this implies (u_m == u_l)
 *
 * The antecedent is an array of a 1 + n * (n+1)/2 composite pointers
 * - a[0] = (distinct u_1 ... u_n)
 * - a[1] = antecedent for (u_1 != u_2)
 * - a[2] = antecedent for (u_1 != u_3), etc.
 * for (u_l == u_m), we set a[p] = NULL. We don't need to store t1 and t2.
 *
 * WARNING: This can be big! Don't use ndprop if n is too large.
 */
extern void gen_ndprop_antecedent(egraph_t *egraph, composite_t *d, occ_t t1, occ_t t2, int32_t k);




/*
 * ANALYZE EGRAPH/EDGES: BUILD LITERAL VECTOR TO EXPLAIN ATOMS
 */

/*
 * Build a conjunction of literals that implies (t1 == t2)
 * add these literals to v. v is not reset.
 * _ id = edge index to ensure causality of short cuts
 * - t1 and t2 must be have the same label
 * - id = egde that merges t1 and t2
 */
extern void egraph_explain_equality(egraph_t *egraph, occ_t t1, occ_t t2, int32_t id, ivector_t *v);



/*
 * HELPER FUNCTIONS FOR THE SATELLITE SOLVERS
 */

/*
 * Build an explanation for the equality between t1 and t2
 * - t1 and t2 must be terms attached to theory variables x1 and x2 in a satellite solver.
 * - the equality x1 == x2 must have been propagated to the satellite solver via
 *   the satellite's assert_equality function.
 * - id = egde that caused t1 and t2's classes to be merged (passed to the satellite
 *   solver's assert_equality)
 * - explanation literals are added to vector v
 */
static inline void egraph_explain_term_eq(egraph_t *egraph, eterm_t t1, eterm_t t2, int32_t id, ivector_t *v) {
  egraph_explain_equality(egraph, pos_occ(t1), pos_occ(t2), id, v);
}


/*
 * Disequality pre-explanation objects.  These must be used if the
 * egraph propagates (x1 != x2) to a satellite solver and the solver
 * uses this disequality as antecedent in further propagation. The
 * explanation for (x1 != x2) can be constructed in two steps:
 *
 * 1) eager step: call egraph_store_diseq_pre_expl
 *    This must be done when (x1 != x2) is received from the egraph
 *    to store sufficient data into a diseq_pre_expl_t object.
 *
 * 2) lazy step: expand the pre-expl data into a set of literals.
 *    Can be done lazily, only when the explanation is needed.
 */

/*
 * Eager step: build a pre-explanation for (x1 != x2)
 * - t1 must be the egraph term attached to theory variable x1
 * - t2 must be the egraph term attached to theory variable x2
 * - hint must be the composite passed by the egraph in the call
 *   to assert_disequality or assert_distinct
 * - p: pointer to a pre-explanation structure to fill in
 */
extern void egraph_store_diseq_pre_expl(egraph_t *egraph, eterm_t t1, eterm_t t2, composite_t *hint, diseq_pre_expl_t *p);

/*
 * Lazy step: expand a pre-explanation into an array of literals
 * - p: pre-explanation structured set by the previous function
 * - v: vector where literals will be added.
 */
extern void egraph_expand_diseq_pre_expl(egraph_t *egraph, diseq_pre_expl_t *p, ivector_t *v);






/*
 * CHECK FOR INCONSISTENCY: GENERATE EXPLANATION VECTOR IF ONE IS FOUND
 */

/*
 * Check whether adding edge i of the form (t1 == t2) results in a conflict
 * - if so returns true and construct a conflict explanation
 * - the conflict is stored as a vector of literals in v.
 * - if a conflict is detected, v is reset first
 */
extern bool egraph_inconsistent_edge(egraph_t *egraph, occ_t t1, occ_t t2, int32_t i, ivector_t *v);


/*
 * Check whether asserting d = (distinct t1 ... t_m) is inconsistent,
 * i.e., whether two subterms t_i and t_j are equal
 * - if so construct an explanation for the conflict and store it in v
 * - if there's a conflict, v is reset first.
 */
extern bool egraph_inconsistent_distinct(egraph_t *egraph, composite_t *d, ivector_t *v);


/*
 * Check whether assertion not d, where d is (distinct t_1 ... t_m) causes a conflict,
 * i.e., whether (t_i != t_j) holds for all i < j.
 * - if so construct an explanation and store it in v (reset v first)
 * Warning: can be expensive if n is large
 */
extern bool egraph_inconsistent_not_distinct(egraph_t *egraph, composite_t *d, ivector_t *v);



/*
 * SUPPORT FOR EGRAPH/THEORY SOLVER RECONCILIATION
 */

/*
 * Return an edge that's a candidate for interface lemma and is an antecedent of edge i
 * - source must be the index of the EXPL_RECONCILE edge that triggered a conflict
 * - i must be the index of the conflict edge
 */
extern int32_t egraph_get_reconcile_edge(egraph_t *egraph, int32_t source, int32_t i);



#endif /* __EGRAPH_EXPLANATIONS_H */
