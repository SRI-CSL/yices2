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
 * Support for exploring terms via the API
 * - this hides the low-level details of term representation
 *   (in terms.h) and provides a more uniform set of functions
 *   for recursively visiting terms.
 * - the terms are divided into five classes:
 *   1) atomic terms (no children)
 *      this includes constant of atomic types +
 *      variables and uninterpreted terms
 *   2) composite terms:
 *      all terms of the form (term-constructor, num-children, list of children)
 *   3) projections:
 *      terms of the from (proj-operator, index, child)
 *      this includes tuple projection and bit-extract
 *   4) sums: of the form a_0 t_0 + ... + a_n t_n
 *      - the a_i's are arithmetic or bitvector constants
 *      - the t_i's are terms
 *   5) products: of the form t_0^d_0 x ... x t_n^d_n
 *      - the t_i's are terms
 *      - the d_i's are positive exponents
 *
 * NOTE: (not t) is classified as a composite term.
 */

#ifndef __TERM_EXPLORER_H
#define __TERM_EXPLORER_H

#include <gmp.h>

#include "terms/terms.h"
#include "yices_types.h"

/*
 * Check the class of term t
 * - t must be a valid term in table
 */
extern bool term_is_atomic(term_table_t *table, term_t t);
extern bool term_is_composite(term_table_t *table, term_t t);
extern bool term_is_projection(term_table_t *table, term_t t);
extern bool term_is_sum(term_table_t *table, term_t t);
extern bool term_is_bvsum(term_table_t *table, term_t t);
extern bool term_is_product(term_table_t *table, term_t t);

/*
 * Constructor code for term t
 * - t must be valid in table
 * - the constructor codes are defined in yices_types.h
 */
extern term_constructor_t term_constructor(term_table_t *table, term_t t);

/*
 * Number of children of t (this is no more than YICES_MAX_ARITY)
 * - for a sum, this returns the number of summands
 * - for a product, this returns the number of factors
 */
extern uint32_t term_num_children(term_table_t *table, term_t t);

/*
 * i-th child of term t:
 * - t must be a valid term in table
 * - t must be a composite term
 * - if n is term_num_children(table, t) then i must be in [0 ... n-1]
 */
extern term_t term_child(term_table_t *table, term_t t, uint32_t i);


/*
 * All children of t:
 * - t must be a valid term in table
 * - t must be a composite term
 *.- the children of t are added to vector v
 */
extern void get_term_children(term_table_t *table, term_t t, ivector_t *v);


/*
 * Components of a projection
 * - t must be a valid term in table and it must be either a SELECT_TERM
 *   or a BIT_TERM
 */
extern int32_t proj_term_index(term_table_t *table, term_t t);
extern term_t proj_term_arg(term_table_t *table, term_t t);

/*
 * Components of an arithmetic sum
 * - t must be a valid ARITH_POLY term in table
 * - i must be an index in [0 ... n-1] where n = term_num_children(table, t)
 * - the component is a pair (coeff, child): coeff is copied into q
 * - q must be initialized
 */
extern void sum_term_component(term_table_t *table, term_t t, uint32_t i, mpq_t q, term_t *child);

/*
 * Components of a bitvector sum
 * - t must be a valid BV_POLY or BV64_POLY term in table
 * - i must be an index in [0 ... n-1] where n = term_num_children(table, t)
 * - the component is a pair (coeff, child):
 *   coeff is a bitvector constant
 *   child is a bitvector term 
 * The coeff is returned in array a
 * - a must be large enough to store nbits integers, where nbits = number of bits in t
 *   a[0] = lower order bit of the constant
 *   a[nbits-1] = higher order bit
 */
extern void bvsum_term_component(term_table_t *table, term_t t, uint32_t i, int32_t a[], term_t *child);  


/*
 * Components of a power-product
 * - t must be a valid POWER_PRODUCT term in table
 * - i must be an index in [0 .. n-1] where n = term_num_children(table, t)
 * - the component is a pair (child, exponent)
 *   child is a term (arithmetic or bitvector term)
 *   exponent is a positive integer
 */
extern void product_term_component(term_table_t *table, term_t t, uint32_t i, term_t *child, uint32_t *exp);


/*
 * Value of constant terms
 * - t must be a constant term of appropriate type
 * - generic_const_value(table, t) works for any constant 
 *   term t of scalar or uninterpreted type
 */
extern bool bool_const_value(term_table_t *table, term_t t);
extern void arith_const_value(term_table_t *table, term_t t, mpq_t q);
extern void arith_ff_const_value(term_table_t *table, term_t t, mpq_t q);
extern void bv_const_value(term_table_t *table, term_t t, int32_t a[]);
extern int32_t generic_const_value(term_table_t *table, term_t t);


#endif /* __TERM_EXPLORER_H */

