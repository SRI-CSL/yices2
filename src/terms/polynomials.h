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

/*
 * POLYNOMIALS
 */

/*
 * Polynomials represented as arrays of monomials.
 * Each monomial is a pair <coeff, variable>.
 * - coeff is a rational number
 * - variable is a 32bit signed integer.
 * This module provides a more compact representation
 * than arith_buffers.
 */

#ifndef __POLYNOMIALS_H
#define __POLYNOMIALS_H

#include <stdint.h>
#include <stdbool.h>

#include "terms/polynomial_common.h"
#include "terms/rationals.h"
#include "utils/int_vectors.h"
#include "utils/memalloc.h"


/*
 * Polynomial object:
 * - mono = array of pairs <coeff, variable>
 * - nterms = number of monomials
 *   the polynomial is mono[0] + ... + mono[nterms - 1]
 * Polynomials are stored in a normalized form:
 * - the coefficients are non-zero
 * - the monomials are sorted
 * - mono[nterms].var contains the end-marker max_idx
 *
 * Normalization
 * -------------
 * By default, normalization sorts the monomials in increasing
 * variable index and remove all monomials with zero coefficients.
 * This is sufficient for linear polynomials.
 *
 * It's also possible to use another ordering, defined by a variable
 * comparison function. This ordering must ensure that the constant
 * term if any is stored in mono[0] (with var = const_idx). It must
 * also ensure that the end marker is last.
 */

// monomial
typedef struct {
  int32_t var;
  rational_t coeff;
} monomial_t;

// polynomial
typedef struct {
  uint32_t nterms;
  monomial_t mono[0];
} polynomial_t;


/*
 * Maximal size of a monomial array = maximal number of terms in a polynomial
 * This makes sure no arithmetic overflow occurs when computing
 *   sizeof(polynomial) + (n+1) * sizeof(monomial_t)
 * where n = number of terms in poly->mono
 */
#define MAX_POLY_SIZE (((UINT32_MAX-sizeof(polynomial_t))/sizeof(monomial_t))-1)


/*
 * Seed used in the hash function.
 */
#define HASH_POLY_SEED ((uint32_t) 0x923a7a2f)



/*
 * ARRAYS OF MONOMIALS AND NORMALIZATION
 */

/*
 * Allocation of monomial arrays:
 * - allocation: n = size of array = number of monomials
 * - realloc: n = current size, new_size = new_size
 * we must have n < MAX_POLY_SIZE, and new_size < MAX_POLY_SIZE.
 * These functions initialize all the rational coefficients (to zero).
 */
extern monomial_t *alloc_monarray(uint32_t n);
extern monomial_t *realloc_monarray(monomial_t *a, uint32_t n, uint32_t new_size);


/*
 * Clear all the coefficients in a[0] to a[n-1]
 */
extern void clear_monarray(monomial_t *a, uint32_t n);


/*
 * Sort the monomials of a in increasing variable order.
 * - a must be terminated by the end-marker max_idx
 * - n = number of monomials in a excluding the end marker
 * (so a must contain at least n+1 monomials and a[n].var
 *  must be equal to max_idx)
 */
extern void sort_monarray(monomial_t *a, uint32_t n);


/*
 * Sort array a in an order defined by cmp.
 * - a must be terminated by the end-marker max_idx
 * - n = number of monomials in a excluding the end marker
 *  (i.e., a[n].var must be max_idx).
 * - data = generic pointer passed as first argument to the cmp function.
 */
extern void sort_monarray2(monomial_t *a, uint32_t n, void *data, var_cmp_fun_t cmp);


/*
 * Normalize a: merge monomials with the same variable and remove
 * monomials with a zero coefficient.
 * - a must be sorted first (using either sort_monarray or sort_monarray2)
 * - n = number of monomials in a (excluding end marker)
 * - result = size of a after normalization.
 */
extern uint32_t normalize_monarray(monomial_t *a, uint32_t n);


/*
 * Hash code
 * - a must be normalized (and terminated by the end marker)
 * - n = number of terms in a (not counting the end marker)
 *
 * This hash code is consistent with function hash_polynomial:
 * If h = hash_monarray(p) and p has n monomials,
 * then  hash_polynomial(monarray_get_poly(p, n)) = h.
 * (i.e., the code is not changed when p is converted to
 * a polynomial_t object).
 */
extern uint32_t hash_monarray(monomial_t *a, uint32_t n);


/*
 * Copy the constant term of p into c
 * - p must be normalized
 */
extern void monarray_constant(monomial_t *p, rational_t *c);


/*
 * Negate all the coefficients in p
 * - p must be terminated by max_idx
 */
extern void in_place_negate_monarray(monomial_t *p);


/*
 * Copy p into q:
 * - p must be terminated by the end marked
 * - q must be large enough to store the result (including end marker)
 * return the number of monomials in q (excluding the end marker).
 *
 * If p has n monomials + the end marker, then q must be large enough
 * for n+1 monomials. The n monomials of p and the end marked are copied
 * into q[0 ... n]. The function returns n.
 */
extern uint32_t copy_monarray(monomial_t *q, monomial_t *p);



/*
 * COMPARISON
 */

/*
 * Check whether p1 and p2 are equal:
 * - both must be normalized
 */
extern bool equal_monarrays(monomial_t *p1, monomial_t *p2);


/*
 * Check whether p1 and p2 cannot be equal.
 * - if this returns true, then p1(x) != p2(x) for any x
 * - the function just checks whether (p1 - p2) is a non-zero
 *   constant, so it's not complete.
 * - p1 and p2 must be normalized
 */
extern bool disequal_monarrays(monomial_t *p1, monomial_t *p2);


/*
 * Check whether p1 and p2 are opposite
 * - both must be normalized
 */
extern bool opposite_monarrays(monomial_t *p1, monomial_t *p2);


/*
 * INTEGER-ARITHMETIC OPERATIONS
 */

/*
 * Compute the period and phase of polynomial p:
 * Let p be b_0 + a_1 x_1 + ... + a_n x_n where x_1 ... x_n are
 * integer variables and b_0, a_1, ..., a_n are rationals.
 * The period Q and phase R are rationals such that
 *     FORALL x_1, ..., x_n: EXISTS y: p(x_1 ... x_n) = Q y + R
 * This is computed via
 *   Q := gcd(a_1, ..., a_n) and
 *   R := remainder of b_0 modulo Q.
 *
 * Input: p must be normalized and terminated by the end marker
 * - period and phase must be initialized rationals
 * Output: the results are copied into *period and *phase
 * - if p is a constant polynomial then period is set to 0
 *   and phase is equal to p.
 */
extern void monarray_period_and_phase(monomial_t *p, rational_t *period, rational_t *phase);


/*
 * Compute factor := gcd of all coefficients in p
 * - all the coefficients must be integers
 * - p must be normalized
 * - if p is zero, then factor is set to 0
 */
extern void monarray_common_factor(monomial_t *p, rational_t *factor);


/*
 * Compute period = gcd of all non-constant coefficients in p
 * - all the coefficients must be integer (except the constant if there's one)
 * - p must be normalized.
 * - if p is constant then period is set to 0
 */
extern void monarray_gcd(monomial_t *p, rational_t *gcd);



/*
 * SUPPORT FOR SIMPLIFYING IF-THEN-ELSE
 */

/*
 * 1) If p and q are two polynomials and c is a boolean term, we
 *    may want to rewrite (ite c p q) to r + (ite c p' q') where
 *    r is the common part of p and q (i.e., r is the sum of
 *    all monomials that occur in both p and q).
 *
 * 2) Then if p' and q' can be factored into (a.p'') and (a.q''),
 *    respectively, then we way further rewrite
 *     (ite c p' q') to  a.(ite c p'' q'').
 *
 * This leads to the full simplification:
 *
 *      (ite c p q) --> r + a.u
 *
 * where
 *       r is the common part of p and q,
 *       p = r + a p''
 *       q = r + a q''
 *       u = (ite c p'' q'')
 *
 * Function monarray_pair_common_part computes r.
 * Function monarray_pair_common_gcd computes a (if p and q are integer
 * polynomials).
 *
 * Warning: p and q must be sorted in increasing variable order (i.e., linear
 * polynomials).
 */

/*
 * Extract the common part of p and q:
 * - p and q must both be normalized
 * - the set of variables x_1, ..., x_k such that
 *   x_i occurs with the same coefficient in p and q is added to vector v.
 * - these variables are in increasing order
 */
extern void monarray_pair_common_part(monomial_t *p, monomial_t *q, ivector_t *v);


/*
 * Compute the GCD of all coefficients in p and q that are not
 * in the common part of p and q.
 * - p and q must be normalized and have integer coefficients
 * - the result is returned in factor.
 * - if p = q, then the result is 0
 */
extern void monarray_pair_non_common_gcd(monomial_t *p, monomial_t *q, rational_t *factor);



/*
 * POLYNOMIAL OBJECTS
 */

/*
 * Allocate a polynomial of n terms
 * - n+1 monomials are allocated
 * - the last monomial is set to the end-marker
 * - the rational coefficients are initialized to 0
 * - the variable indices in poly->mono are not initialized
 */
extern polynomial_t *alloc_raw_polynomial(uint32_t n);


/*
 * Create a polynomial_t object from a.
 * - n = number of monomials in a (excluding end marker)
 * - a must be normalized.
 * SIDE EFFECT: a is reset to zero (all coefficients are cleared).
 */
extern polynomial_t *monarray_get_poly(monomial_t *a, uint32_t n);


/*
 * Create a polynomial_t object from a, without side effects
 * - n = number of monomials in a (excluding end marker)
 * - a must be normalized.
 * This function makes a copy of all coefficients (so it has no side effects).
 * This may be somewhat expensive if the coefficients are large GMP numbers.
 */
extern polynomial_t *monarray_copy_to_poly(monomial_t *a, uint32_t n);


/*
 * Deletion of polynomial objects.
 */
static inline void free_polynomial(polynomial_t *p) {
  clear_monarray(p->mono, p->nterms);
  safe_free(p);
}


/*
 * Hash code for polynomial p
 * - p must be normalized.
 */
extern uint32_t hash_polynomial(polynomial_t *p);


/*
 * Get the main variable of p (i.e., the last variable in
 * in p's monomial array).
 * returns null_idx if p is zero,
 * returns const_idx if p is a constant polynomial.
 */
extern int32_t polynomial_main_var(polynomial_t *p);


/*
 * Check whether p1 - p2 is a nonzero constant
 */
static inline bool disequal_polynomials(polynomial_t *p1, polynomial_t *p2) {
  return disequal_monarrays(p1->mono, p2->mono);
}


/*
 * Check whether p1 == p2
 */
static inline bool equal_polynomials(polynomial_t *p1, polynomial_t *p2) {
  return p1->nterms == p2->nterms && equal_monarrays(p1->mono, p2->mono);
}


/*
 * Check whether p is zero
 * - p must be normalized
 */
static inline bool polynomial_is_zero(polynomial_t *p) {
  return p->nterms == 0;
}


/*
 * Check whether p is constant.
 * - p must be normalized
 */
extern bool polynomial_is_constant(polynomial_t *p);


/*
 * Check whether p is constant and nonzero
 * - p must be normalized
 */
extern bool polynomial_is_nonzero(polynomial_t *p);


/*
 * Check whether p is constant and positive, negative, etc.
 * These checks are incomplete (but cheap). They always return
 * false if p is non-constant.
 */
extern bool polynomial_is_pos(polynomial_t *p);
extern bool polynomial_is_neg(polynomial_t *p);
extern bool polynomial_is_nonneg(polynomial_t *p);
extern bool polynomial_is_nonpos(polynomial_t *p);


/*
 * Check whether p == k + x for non-zero k and variable x
 */
extern bool polynomial_is_const_plus_var(polynomial_t *p, int32_t x);


/*
 * Check whether p == x for variable x
 */
extern bool polynomial_is_var(polynomial_t *p, int32_t x);


/*
 * Check if all coefficients are integer and less than mod
 */
extern bool polynomial_is_ff_poly(const polynomial_t *p, const rational_t *mod);

#endif /* __POLYNOMIALS_H */
