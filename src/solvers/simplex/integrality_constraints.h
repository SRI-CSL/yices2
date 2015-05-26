/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * An integrality constraint asserts that a sum of rational
 * monomials must be an integer. The sum is of the form
 *
 *   a_0/b_0 + a_1/b_1 x_1 + ... + a_n/b_n x_n 
 *
 * where the coefficients ai/bi are not integer. This sum
 * is extracted from a row of the tableau, when the basic
 * variable in this row is an integer variable but doesn't
 * have an integer value.
 *
 * Some of the variables x_i may be fixed. This means that the solver
 * contains bounds l_i <= x_i <= u_i where l_i and u_i are equal.
 * The fixed variables may be integer or rational variables. The
 * non-fixed variables must all be integer variables.
 *
 * We split the set of variables as follows:
 *   x_1, ...., x_k: not-fixed, integer vaaraibles.
 *   x_k+1 ... x_n: fixed variables
 *
 *
 * Feasibility test
 * ----------------
 * We want to check whether an integrality constraint is feasible.
 * This is a generalization of the GCD test:
 *
 * We write the constraint as
 *
 *    a_1/b_1 x_1 + ... + a_k/b_k x_k + fixed terms
 *
 * We compute G = gcd(a_1/b_1, ..., a_k/b_k).  We use
 *
 *    L = lcm(b_1,...,b_k) and D = gcd(a_1,...,a_k)
 *
 * then G is D/L. Then the term (a_1/b_1 x_1 + ... + a_k/b_k x_k) 
 * is an integer multiple of D/L.
 *
 * The question is now: is there an integer t such 
 * that (D/L t + fixed terms) is an integer?
 * 
 * Simplification: We can remove any fixed term of the form a_j/b_j x_j 
 * if D/L divides a_j/b_j and x_j is an integer variable.
 *
 * After this, we compute the sum of fixed terms = A/B,
 * and we use the property:
 *
 *   (\exists t: D/L t + A/B in Z) iff L is a multiple of B.
 *
 * This holds provided the fraction D/L and A/B are reduced
 * (i.e., gcd(D, L) = 1 and gcd(A, B) = 1).
 *
 * If the constraint is not feasible, we want to provide an
 * explanation = set of variables that show up in the fixed terms.
 *
 * Period and phase computation
 * ----------------------------
 * If the constraint is feasible, we can try to learn some information
 * on the variables x_1, ..., x_k. 
 *
 * The constraint is feasible. So there's an integer k such that
 *
 *    a_1/b_1 x_1 + ... + a_k/b_k x_k + fixed terms = k
 *
 * We can rewrite this as
 *
 *    a_1/b_1 x_1 = k - a_2/b_2 x_2 ... - a_k/b_k x_k - fixed terms.
 *
 * As before, we can compute
 *
 *    G = gcd(1, a_2/b_2, ... , a_k/b_k) = 1/lcm(1, b_2, ..., b_k),
 *
 * and the term (k - a_2/b_2 x_2 ... - a_k/b_k x_k) is a multiple of G.
 * So we learn that
 *
 *      a_1/b_1 x_1  = a multiple of G - fixed terms.
 *
 * Then we get
 *
 *      x_1 = a multiple of (G * b_1/a_1) - b_1/a_1 * fixed_terms.
 *
 * We can eliminate the fixed term a_j/b_j x_j if x_j is an integer and a_j/b_j
 * is a multiple of (G * b_1/a_1).
 *
 * We call P := (G * b_1/a_1)    the period of x_1 
 *     and Q := - (b_1/a_1 * fixed_terms)  the phase.
 *
 * To normalize, we reduce Q modulo P.
 *
 * From P and Q, it may be possible to strengthen the bounds on x_1 in
 * the simplex solver. For example, if we know x_1 = multiple of 5 + 3
 * and x_1 >= 1 then we can infer x_1 >= 3. To explain this inferred
 * bound, we keep track of the fixed terms that contribute to the
 * phase Q.
 */

#ifndef __INTEGRALITY_CONSTRAINTS_H
#define __INTEGRALITY_CONSTRAINTS_H

#include <stdint.h>
#include <stdbool.h>

#include "terms/polynomials.h"
#include "terms/rationals.h"
#include "utils/int_vectors.h"


/*
 * Constraint descriptor
 * - two arrays of monomials: non-fixed and fixed part
 * - for the fixed terms, we keep the value of each variable
 *   x_i and its type
 * - we also store the constant term separate from the fixed terms
 *
 * - sum = non-fixed part represented as an array of monomials
 *   sum_size = size of the array
 *   sum_nterms = number of terms in the sum
 *
 * - fixed_sum = fixed part (also an array of monomials)
 *   the i-th monomial is of the form a/b * x:
 *   fixed_val[i] = value of fixed variable x
 *   is_int[i] = true if x is an integer variable/false otherwise.
 *   fixed_size = size of arrays fixed_sum/fixed_val/is_int
 *   fixed_nterms = number of terms in fixed_sum
 */
typedef struct int_constraint_s {
  // non-fixed sum
  monomial_t *sum; 
  uint32_t sum_nterms;
  uint32_t sum_size;
  // fixed sum + extra data
  monomial_t *fixed_sum;
  rational_t *fixed_val;
  uint8_t *is_int;
  uint32_t fixed_nterms;
  uint32_t fixed_size;
  // constant term in fixed sum
  rational_t constant;

  // auxiliary rationals
  rational_t num_gcd;        // gcd of numerators
  rational_t den_lcm;        // lcm of denominators
  rational_t gcd;            // gcd := num_gcd/den_lcm
  rational_t fixed_constant; // sum of the fixed terms
  rational_t period;
  rational_t phase;
  rational_t q0;
  rational_t q1;
} int_constraint_t;

// max size and default size for both sum and fixed sum
#define INT_CONSTRAINT_MAX_SIZE (UINT32_MAX/sizeof(monomial_t))
#define INT_CONSTRAINT_DEF_SIZE 10

/*
 * Initialize a constraint descriptor:
 * - both arrays are empty
 */
extern void init_int_constraint(int_constraint_t *cnstr);

/*
 * Reset: remove all monomials
 */
extern void reset_int_constraint(int_constraint_t *cnstr);

/*
 * Delete the constraint
 */
extern void delete_int_constraint(int_constraint_t *cnstr);


/*
 * Add a monomial to the non-fixed part:
 * - a = rational coefficient
 * - x = integer variable
 * - x must not occur already
 * The coefficient must not be an integer
 */
extern void int_constraint_add_mono(int_constraint_t *cnstr, const rational_t *a, int32_t x);

/*
 * Add a monomial to the fixed part:
 * - a = rational coefficient
 * - x = variable
 * - is_int = true if x is an integer variable
 * - val = value of x
 * If x is an integer, the coefficient must not be an integer
 */
extern void int_constraint_add_fixed_mono(int_constraint_t *cnstr, const rational_t *a, int32_t x, bool is_int, const rational_t *val);

/*
 * Add the constant term a
 */
extern void int_constraint_add_constant(int_constraint_t *cnstr, const rational_t *a);

/*
 * Check feasibility of the constraint
 * - return true if feasible
 * - return false if not
 * - in both case, a subset of fixed variables is added to v
 *   these are the fixed variables that were used to compute
 *   the sum of fixed values.
 *
 * If the result is false, then v is an explanation.
 */
extern bool int_constraint_is_feasible(int_constraint_t *cnstr, ivector_t *v);


/*
 * Number of non-fixed terms
 */
static inline uint32_t int_constraint_num_terms(int_constraint_t *cnstr) {
  return cnstr->sum_nterms;
}

/*
 * Get the i-th non-fixed variable of cnstr
 * - i must be less than cnstr->sum_nterms
 */
extern int32_t int_constraint_get_var(int_constraint_t *cnstr, uint32_t i);

/*
 * Compute period and phase of the i-th non-fixed variable of cnstr
 * - i must be between 0 and cnstr->sum_nterms.
 * - store the explanation in vector v = set of fixed variables that
 *   contribute to the phase
 * - period and phase are stored in cnstr->period and cnstr->phase
 */
extern void int_constraint_period_of_var(int_constraint_t *cnstr, uint32_t i, ivector_t *v);

/*
 * Period/phase
 */
static inline rational_t *int_constraint_period(int_constraint_t *cnstr) {
  return &cnstr->period;
}

static inline rational_t *int_constraint_phase(int_constraint_t *cnstr) {
  return &cnstr->phase;
}

#endif /* __INTEGRALITY_CONSTRAINTS_H */
