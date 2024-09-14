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
 * MISCELLANEOUS COMPUTATIONS ON TERMS
 */

/*
 * terms.h and terms.c implement basic term construction functions.
 *
 * We put helper functions here to support rewriting and simplification,
 */

#ifndef __TERM_UTILS_H
#define __TERM_UTILS_H

#include <stdbool.h>
#include <stdint.h>

#include "terms/bv64_interval_abstraction.h"
#include "terms/bv_constants.h"
#include "terms/bvfactor_buffers.h"
#include "terms/bvpoly_buffers.h"
#include "terms/terms.h"



/*
 * FINITE DOMAINS
 */

/*
 * Special if-then-else terms can have a finite number of constant values
 * - the set of possible values is stored in a domain record and
 *   attached in the 'extra' field of the special-ite term descriptor.
 * - a domain record is an array of term indices, sorted in increasing
 *   order.
 */
typedef struct finite_domain_s {
  uint32_t nelems; // number of elements in the set
  term_t data[0];  // actual array of elements (real size = nelems)
} finite_domain_t;


#define MAX_FINITE_DOMAIN_SIZE ((UINT32_MAX-sizeof(finite_domain_t))/sizeof(term_t))


/*
 * Get the finite domain of term t
 * - t must have type_kind = ITE_SPECIAL
 * - the function computes the domain and store it in t's descriptor
 *   if it's not already done
 */
extern finite_domain_t *special_ite_get_finite_domain(term_table_t *tbl, term_t t);


/*
 * Check whether u belongs to the finite domain of term t
 * - t must be a special if-then-else
 * - build the domain and attach it to t's descriptor if needed
 */
extern bool term_is_in_finite_domain(term_table_t *tbl, term_t t, term_t u);


/*
 * Check whether t and u have disjoint finite domains
 * - both t and u must be special if-then-else
 * - the domains of t and u are computed if needed.
 */
extern bool terms_have_disjoint_finite_domains(term_table_t *tbl, term_t t, term_t u);


/*
 * Check whether all elements in t's domain are non-negative
 * - t must be a special if-then-else of arithmetic type
 * - the domain of t is computed if required
 */
extern bool term_has_nonneg_finite_domain(term_table_t *tbl, term_t t);


/*
 * Check whether all elements in t's domain are non-positive
 * - t must be a special if-then-else of arithmetic type
 * - the domain of t is computed if required
 */
extern bool term_has_nonpos_finite_domain(term_table_t *tbl, term_t t);


/*
 * Check whether all elements in t's domain are negative
 * - t must be a special if-then-else term of arithmetic type
 * - the domain of t is computed if required
 */
extern bool term_has_negative_finite_domain(term_table_t *tbl, term_t t);


/*
 * Check whether all elements in t's domain are non-zero
 * - t must be a special if-then-else term of arithmetic type
 * - the domain of t is computed if required
 */
static inline bool term_has_nonzero_finite_domain(term_table_t *tbl, term_t t) {
  assert(is_arithmetic_term(tbl, t));
  return !term_is_in_finite_domain(tbl, t, zero_term);
}


/*
 * Compute the lower and upper bound of t's domain
 * - t must be a special if-then-else term of arithmetic type
 * - the domain of t is computed if needed
 * - the lower bound is stored in *lb and the upper bound is stored in *ub
 *   (both are ARITH_CONSTANT terms)
 */
extern void term_finite_domain_bounds(term_table_t *tbl, term_t t, term_t *lb, term_t *ub);


/*
 * DISEQUALITY CHECKS
 */

/*
 * Check whether two terms x and y can never be equal.
 * This is incomplete and can detect disequalities in simple cases.
 * - if the function returns true, then x and y can't be equal in any interpretation
 * - if it returns false, we don't know.
 */
extern bool disequal_terms(term_table_t *tbl, term_t x, term_t y, bool check_ite);


/*
 * Special cases:
 * - two bitvector terms
 * - two arithmetic terms
 */
extern bool disequal_bitvector_terms(term_table_t *tbl, term_t x, term_t y);
extern bool disequal_arith_terms(term_table_t *tbl, term_t x, term_t y, bool check_ite);
extern bool disequal_arith_ff_terms(term_table_t *tbl, term_t x, term_t y, bool check_ite);

/*
 * Check whether a[i] can't equal b[i] for all i in 0 .. n-1
 */
extern bool disequal_term_arrays(term_table_t *tbl, uint32_t n, const term_t *a, const term_t *b, bool check_ite);


/*
 * Check whether all the elements of a are disequal
 * this can be expensive: quadratic cost,
 * but should fail quickly on most examples
 */
extern bool pairwise_disequal_terms(term_table_t *tbl, uint32_t n, const term_t *a, bool check_ite);


/*
 * INTEGRALITY CHECK
 */

/*
 * Check whether t can't be an integer.
 * This is incomplete.
 * - returns true if t is a non-integer rational
 */
extern bool arith_term_is_not_integer(term_table_t *tbl, term_t t);


/*
 * BOUNDS ON ARITHMETIC TERMS
 */

/*
 * Check whether t is non-negative. This is incomplete and
 * deals only with simple cases.
 * - return true if the checks can determine that t >= 0
 * - return false otherwise
 */
extern bool arith_term_is_nonneg(term_table_t *tbl, term_t t, bool check_ite);


/*
 * Check whether t is negative or null. This is incomplete and
 * deals only with simple cases.
 * - return true if the checks can determine that t <= 0
 * - return false otherwise
 */
extern bool arith_term_is_nonpos(term_table_t *tbl, term_t t, bool check_ite);


/*
 * Check whether t is negative (incomplete)
 * - return true if the checks succeed and determine that t < 0
 * - return false otherwise
 */
extern bool arith_term_is_negative(term_table_t *tbl, term_t t, bool check_ite);


/*
 * Check whether t is non-zero (incomplete)
 * - return true if the checks succeed and determine that t != 0
 * - return false otherwise
 */
extern bool arith_term_is_nonzero(term_table_t *tbl, term_t t, bool check_ite);


/*
 * Check whether t is a non-zero finite field term (incomplete)
 * - return true if the checks succeed and determine that t != 0
 * - return false otherwise
 */
extern bool arith_ff_term_is_nonzero(term_table_t *tbl, term_t t, bool check_ite);


/*
 * BOUNDS ON BITVECTOR TERMS
 */

/*
 * Compute an upper/lower bound on a bitvector term t
 * - the result is stored in c
 * - there are two cases, depending on whether t is interpreted
 *   as a signed (2's complement) or as an unsigned number.
 */
extern void upper_bound_unsigned(term_table_t *tbl, term_t t, bvconstant_t *c);
extern void lower_bound_unsigned(term_table_t *tbl, term_t t, bvconstant_t *c);
extern void upper_bound_signed(term_table_t *tbl, term_t t, bvconstant_t *c);
extern void lower_bound_signed(term_table_t *tbl, term_t t, bvconstant_t *c);


/*
 * Same thing for a bitvector term of 1 to 64 bits
 * - return the bound as an unsigned 64-bit integer
 *   (padded with 0s if the bitsize is less than 64)
 * Even for signed bounds, the result is not sign extended to 64 bits.
 */
extern uint64_t upper_bound_unsigned64(term_table_t *tbl, term_t t);
extern uint64_t lower_bound_unsigned64(term_table_t *tbl, term_t t);
extern uint64_t upper_bound_signed64(term_table_t *tbl, term_t t);
extern uint64_t lower_bound_signed64(term_table_t *tbl, term_t t);


/*
 * Special cases of bitvector terms.  These functions check whether t
 * is one of the following bit-vector constants:
 * - zero: 0b0000...00  (smallest unsigned value)
 * - one:0b0000...01
 * - minus one: 0b1111...11 (largest unsigned value)
 * - smallest negative value: 0b1000...00
 * - largest positive value: 0b0111...11
 */
extern bool bvterm_is_zero(term_table_t *tbl, term_t t);
extern bool bvterm_is_one(term_table_t  *tbl, term_t t);
extern bool bvterm_is_minus_one(term_table_t *tbl, term_t t);
extern bool bvterm_is_min_signed(term_table_t *tbl, term_t t);
extern bool bvterm_is_max_signed(term_table_t *tbl, term_t t);

static inline bool bvterm_is_min_unsigned(term_table_t *tbl, term_t t) {
  return bvterm_is_zero(tbl, t);
}

static inline bool bvterm_is_max_unsigned(term_table_t *tbl, term_t t) {
  return bvterm_is_minus_one(tbl, t);
}


/*
 * SIMPLIFICATION OF BIT-VECTOR TERMS
 */

/*
 * Get bit i of term t:
 * - return NULL_TERM if the bit can't be determined
 * - return true or false if t is a bitvector constant
 * - return b_i if t is (bv-array b_0 .. b_i ...)
 *
 * t must be a bitvector term of size >= i
 */
extern term_t extract_bit(term_table_t *tbl, term_t t, uint32_t i);


/*
 * Try to simplify (bv-eq t1 t2) to a boolean term
 * - if t1 and t2 can be rewritten as arrays of bits
 *   [b0 .. b_n] and [c_0 ... c_n], respectively,
 *   then the function checks whether
 *      (and (b0 == c0) ... (b_n == c_n))
 *   simplifies to a single boolean term.
 * - return NULL_TERM if no simplification is found
 *
 * NOTE: this function does not deal with the simpler cases where both
 * t1 and t2 are constant, or t1 == t2. Check whether t1 == t2 and
 * call disequal_bivector_terms(tbl, t1, t2) first before calling this
 * function.
 */
extern term_t simplify_bveq(term_table_t *tbl, term_t t1, term_t t2);


/*
 * Try to simplify (bv-eq t1 t2) to a conjunction of terms
 * - if t1 and t2 can be rewritten as arrays of bits
 *   [b_0 ... b_n] and [c_0 ... c_n], respectively,
 *   then the function checks whether each
 *   equality (b_i == c_i)  simplifies to a single Boolean term e_i
 * - if all of them do, then the function
 *   returns true and stores e_0, ... e_n into vector v
 *
 * As above: t1 and t2 must not be equal, and disequal_bitvector_terms(tbl, t1, t2)
 * must be false.
 *
 * NOTE: v may be modified event if the function returns false
 */
extern bool bveq_flattens(term_table_t *tbl, term_t t1, term_t t2, ivector_t *v);



/*
 * ARITHMETIC SIMPLIFICATIONS
 */

/*
 * Check whether t is equal to x or (bv-not x) for some term x
 * - t must be a bit-vector array (BV_ARRAY)
 * - the function returns true if t is equal to x or (bv-not x)
 *   it returns the term x in *x
 *   if t is equal to x, the negated flag is set to false
 *   if t is equal to (bv-not x), the negated flag is set to true
 * - the function returns false if t is not of the right form and leaves *x and *negated unchanged
 */
extern bool bvarray_convertible_to_term(term_table_t *tbl, term_t t, term_t *x, bool *negated);

/*
 * Add or subtract t to/from buffer b
 * - try to convert t to a bitvector polynomial first
 * - t must be a bitvector term
 * - b->bitsize must be equal to t's bitsize
 */
extern void add_bvterm_to_buffer(term_table_t *tbl, term_t t, bvpoly_buffer_t *b);
extern void sub_bvterm_from_buffer(term_table_t *tbl, term_t t, bvpoly_buffer_t *b);


/*
 * Add or subtract a * t to/from buffer b
 */
extern void addmul_bvterm64_to_buffer(term_table_t *tbl, term_t t, uint64_t a, bvpoly_buffer_t *b);
extern void submul_bvterm64_from_buffer(term_table_t *tbl, term_t t, uint64_t a, bvpoly_buffer_t *b);

extern void addmul_bvterm_to_buffer(term_table_t *tbl, term_t t, uint32_t *a, bvpoly_buffer_t *b);
extern void submul_bvterm_from_buffer(term_table_t *tbl, term_t t, uint32_t *a, bvpoly_buffer_t *b);



/*
 * FACTORING OF BIT-VECTOR PRODUCTS
 */

/*
 * Check whether t is a product
 * - this returns true if t is (bvshl x y) since (bvshl x y) = x * (bvshl 1 y)
 *   or if t is a power-product
 *   of if t is a polynomial with a single monomial = a * power-product for
 *   some constant a that's not 0 and not 1.
 * - return false otherwise (including if t is not a bit-vector term).
 */
extern bool term_is_bvprod(term_table_t *tbl, term_t t);

/*
 * Compute a factorization of t
 * - t must be a bitvector term
 * - this writes t to the form a * power-product * 2^exp
 *   by converting (bvshl x y)  to x * 2^y
 *   and so forth
 * - the result is returned in buffer b
 * - b must be initialized
 */
extern void factor_bvterm(term_table_t *tbl, term_t t, bvfactor_buffer_t *b);

/*
 * Add factors of (a * t) to buffer b
 * - t must be a bitvector term
 * - b and t must have the same bitsize
 * - if t has 64bits or less, a is given as a 64bit constant
 * - if t has more than 64bits, a iis given as an array of 32bit words
 */
extern void factor_mul_bvterm64(term_table_t *tbl, uint64_t a, term_t t, bvfactor_buffer_t *b);
extern void factor_mul_bvterm(term_table_t *tbl, uint32_t *a, term_t t,  bvfactor_buffer_t *b);

/*
 * Compute the factorization of all monomials in p
 * - b must be an array of n buffers where n >= p->nterms
 * - the factoring of p->mono[i] is stored in b[i]
 */
extern void factor_bvpoly64_monomials(term_table_t *tbl, bvpoly64_t *p, bvfactor_buffer_t *b);
extern void factor_bvpoly_monomials(term_table_t *tbl, bvpoly_t *p, bvfactor_buffer_t *b);


/*
 * FACTORS TO TERMS
 */

/*
 * Construct a term t from buffer b:
 * - if b contains C * product * 2^exponent
 *   then this constructs two auxiliary terms:
 *    p := product
 *    e := exponent
 *   and returns C * bvshl(p, e)
 * - to build the terms, we need an auxiliary bvpoly_buffer_t aux
 */
extern term_t bvfactor_buffer_to_term(term_table_t *tbl, bvpoly_buffer_t *aux, bvfactor_buffer_t *b);

/*
 * Construct a term t from an array of n buffers b[0 ... n-1]
 * - this constructs a sum of n terms t_0 .... t_n-1
 *   where t_i is the conversion of b[i] to a term.
 */
extern term_t bvfactor_buffer_array_to_term(term_table_t *tbl, bvpoly_buffer_t *aux, bvfactor_buffer_t *b, uint32_t n);


/*
 * INTERVAL ABSTRACTION FOR BITVECTORS
 */

/*
 * Interval for bitvector t
 * - t must have no more than 64bits
 * - the result is stored in the interval descriptor a
 * - a contains lower/upper bounds, number of bits, sign bit 
 *   (cf. bv64_interval_abstraction.h)
 */
extern void bv64_abstract_term(term_table_t *tbl, term_t t, bv64_abs_t *a);


/*
 * Abstraction of polynomial or power product
 * - nbits = number of bits (must be between 1 amnd 64)
 * - the result is stored in the interval descriptor a
 */
extern void bv64_abs_poly(term_table_t *tbl, bvpoly64_t *p, uint32_t nbits, bv64_abs_t *a);
extern void bv64_abs_pprod(term_table_t *tbl, pprod_t *p, uint32_t nbits, bv64_abs_t *a);
extern void bv64_abs_buffer(term_table_t *tbl, bvarith64_buffer_t *p, uint32_t nbits, bv64_abs_t *a);



/*
 * EXPERIMENTAL CHECKS FOR SUBSUMPTIONS
 */

/*
 * Check whether two Boolean terms t1 and t2
 * are incompatible (i.e., (t1 and t2) is false.
 * - this does very simple checks for now
 */
extern bool incompatible_boolean_terms(term_table_t *tbl, term_t t1, term_t t2);

/*
 * Special cases: t1 and t2 are arithmetic or bitvector literals
 */
extern bool incompatible_arithmetic_literals(term_table_t *tbl, term_t t1, term_t t2);
extern bool incompatible_bitvector_literals(term_table_t *tbl, term_t t1, term_t t2);

/*
 * Check whether t1 subsumes t2 (i.e., t1 => t2)
 */
extern bool term_subsumes_term(term_table_t *tbl, term_t t1, term_t t2);

/*
 * Check whether t1 subsumes all elements of a[0 ... n-1]
 */
extern bool term_subsumes_array(term_table_t *tbl, term_t t1, uint32_t n, term_t *a);




/*
 * EQUALITY DECOMPOSITION
 */

/*
 * Check whether t is equivalent to (x == a) where x is a term and a is a constant
 * - if so stores the term and constant in *x and *a, and returns true.
 * - otherwise returns false, and leave *x and *a unchanged.
 *
 * The following cases are handled:
 * - t is (eq a x) where x and a have uninterpreted types
 * - t is (arith-bineq x a) or (arith-eq0 x)
 * - t is (bveq x a)
 */
extern bool is_term_eq_const(term_table_t *tbl, term_t t, term_t *x, term_t *a);

/*
 * Variant: check whether t is equivalent to (x == a) where x is an uninterpreted
 * term and a is a constant.
 */
extern bool is_unint_eq_const(term_table_t *tbl, term_t t, term_t *x, term_t *a);


/*
 * UNIT-TYPE REPRESENTATIVES
 */

/*
 * Return the term representative for unit type tau.
 * - search the table of unit-types first
 * - create a new term if there's no entry for tau in that table.
 */
extern term_t get_unit_type_rep(term_table_t *table, type_t tau);



/*
 * VARIABLES
 */

/*
 * Clone variable v:
 * - v must be a variable
 * - return a fresh variable with the same type as v
 * - if v has a basename, then the clone also gets that name
 */
extern term_t clone_variable(term_table_t *table, term_t v);


/*
 * Convert variable v to an uninterpreted term
 * - v must be a variable
 * - create a fresh uninterpreted term with the same type as v
 * - if v has a basename, then the clone also gets that name
 */
extern term_t variable_to_unint(term_table_t *table, term_t v);


#endif /* __TERM_UTILS_H */
