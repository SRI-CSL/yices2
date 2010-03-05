/*
 * Print theory-generated clauses
 */

#ifndef __THEORY_TRACER_H
#define __THEORY_TRACER_H

#include <stdint.h>
#include <stdio.h>

#include "smt_core.h"
#include "context.h"
#include "matrices.h"


/*
 * Initialize internal variables:
 * - ctx = context (must be initialized so that tracer can determine
 *   which solvers are being used)
 * - file = trace file where all data is dumped
 * If file can't be opened, the function calls abort()
 */
extern void start_theory_tracer(context_t *ctx, char *file);

/*
 * Close the trace file
 */
extern void end_theory_tracer(void);

/*
 * Get the trace file (it's open after start_theory_tracer)
 * - return NULL if the file is not open
 */
extern FILE *trace_theory_file(void);


/*
 * Print a conflict clause:
 * - a must be an array of literals, terminated by null_literal
 */
extern void trace_theory_conflict(literal_t *a);


/*
 * Print a lemma
 * - a must be an array of n literals
 */
extern void trace_theory_lemma(uint32_t n, literal_t *a);


/*
 * Print a theory implication
 * - a = antecedent = array of n literals
 * - l = implied literal
 */
extern void trace_theory_propagation(uint32_t n, literal_t *a, literal_t l);


/*
 * Print a derived bound (x >= b) or (x <= b) with antecedent v
 * - v must be a vector of bound indices
 */
extern void trace_simplex_derived_lb(int32_t x, xrational_t *b, ivector_t *v);
extern void trace_simplex_derived_ub(int32_t x, xrational_t *b, ivector_t *v);


/*
 * Print a simplex conflict (found in make_feasible)
 * - row = row where the conflict was detected (in the tableau)
 * - a = conflict as an array of literals (terminated by null_literal)
 */
extern void trace_simplex_conflict(row_t *row, literal_t *a);


/*
 * Conflict between assertion l and bound k
 * - a = resulting conflict as an array of literals terminated by null_literal
 */
extern void trace_simplex_assertion_conflict(int32_t k, literal_t l, literal_t *a);



/*
 * Print a conflict between a derived bound (x >= b) or (x <= b)
 * and an existing bound k
 * - v = antecedents for the derived bound = vector of bound indices
 * - a = resulting conflict as a null-terminated array of literals
 */
extern void trace_simplex_derived_lb_conflict(int32_t k, int32_t x, xrational_t *b, ivector_t *v, literal_t *a);
extern void trace_simplex_derived_ub_conflict(int32_t k, int32_t x, xrational_t *b, ivector_t *v, literal_t *a);



/*
 * Print a GCD conflict
 * - row = row where the conflict was detected
 * - a = conflict explanation as an array of literals (terminated by null_literal)
 */
extern void trace_simplex_gcd_conflict(row_t *row, literal_t *a);


/*
 * Print a dsolver conflict
 * - v = array of unsat row indices
 * - a = conflict explanation as an array of literals (terminated by null_literal)
 */
extern void trace_simplex_dsolver_conflict(ivector_t *v, literal_t *a);


/*
 * Conflict between a bound k and an equality (x1 == x2) propagated from the egraph
 * - a = conflict clause as a null-terminated array of literals
 */
extern void trace_simplex_egraph_eq_conflict(int32_t k, int32_t x1, int32_t x2, literal_t *a);


/*
 * Print a derived lower or upper bound in simplex
 * - row = row from which the bound was derived
 * - x = simplex variable
 * - a = bound
 */
extern void trace_simplex_implied_lb(row_t *row, int32_t x, xrational_t *a); // x >= a
extern void trace_simplex_implied_ub(row_t *row, int32_t x, xrational_t *a); // x <= a


/*
 * Print the period and phase for variable x (as implied by x's general solution 
 * found by the diophantine system solver)
 */
extern void trace_dsolver_var_phase_and_period(int32_t x, rational_t *period, rational_t *phase);


/*
 * Print implication k ==> l where k is a bound index
 */
extern void trace_simplex_implied_literal(int32_t k, literal_t l);


/*
 * Multiple simplex implications form a derived bound
 * - row = row from which the bound was derived
 * - v = bounds from which the bound was derived
 * - w = vector encoding the implied bounds: each index in w is an 
 *   assertion id (i.e., atom id + sign)
 */
extern void trace_simplex_multiprops(row_t *row, ivector_t *v, ivector_t *w);


/*
 * Print the tableau in the trace file
 */
extern void trace_tableau(void);


#endif /* __THEORY_TRACER_H */
