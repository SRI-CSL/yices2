/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BUFFERS FOR OPERATIONS ON POLYNOMIALS
 */

/*
 * Polynomials are represented as sums of pairs <coeff, pp>
 * - the coeff is a rational number.
 * - pp is a power product (cf. power_products.h)
 *
 * In normal form, polynomials have the following properties:
 * - the coefficients are all non zero
 * - the monomials are stored in deg-lex order: lower degree
 *   monomials appear first; monomials of equal degree are
 *   sorted in lexicographic order.
 */

#ifndef __ARITH_BUFFERS_H
#define __ARITH_BUFFERS_H

#include <stdint.h>

#include "terms/rationals.h"
#include "utils/object_stores.h"
#include "terms/pprod_table.h"
#include "terms/polynomials.h"


/*
 * An arithmetic buffer stores a polynomial as a list of monomials
 * - list = list of pairs <coeff, pp> sorted in increasing order
 * - some of the coefficients may be zero.
 * - zero coefficients are removed by the normalize operation
 * - the list contains an end marker (with pp = end_pp),
 *   which is always the last element in the list.
 * - nterms = number of monomials in the list, excluding end marker.
 */

// element in a list of monomials
typedef struct mlist_s {
  struct mlist_s *next;
  rational_t coeff;
  pprod_t *prod;
} mlist_t;

// buffer
typedef struct arith_buffer_s {
  uint32_t nterms;        // length of the list (excluding the end marker)
  mlist_t *list;          // start of the list
  object_store_t *store;  // for allocation of list elements
  pprod_table_t *ptbl;    // for creation of power products
} arith_buffer_t;


/*
 * Block size of an arith_buffer store
 */
#define MLIST_BANK_SIZE 64



/***********************
 * BUFFER  OPERATIONS  *
 **********************/

/*
 * Initialize store s for list elements
 */
extern void init_mlist_store(object_store_t *s);


/*
 * Delete store s: free all attached memory and clear all rationals.
 * Must not be called unless all buffers with store s are deleted.
 */
extern void delete_mlist_store(object_store_t *s);

/*
 * Initialize buffer b to the zero polynomial
 * - ptbl = attached power product table
 * - s = attached store
 */
extern void init_arith_buffer(arith_buffer_t *b, pprod_table_t *ptbl, object_store_t *s);


/*
 * Delete b and free all attached memory
 */
extern void delete_arith_buffer(arith_buffer_t *b);


/*
 * Normalize: remove any zero monomials from b
 */
extern void arith_buffer_normalize(arith_buffer_t *b);



/*************
 *  QUERIES  *
 ************/

/*
 * Size = number of terms.
 */
static inline uint32_t arith_buffer_size(arith_buffer_t *b) {
  return b->nterms;
}


/*
 * Check whether b is zero
 * - b must be normalized
 */
static inline bool arith_buffer_is_zero(arith_buffer_t *b) {
  return b->nterms == 0;
}


/*
 * Check whether b is constant
 * - b must be normalized
 */
extern bool arith_buffer_is_constant(arith_buffer_t *b);


/*
 * Check whether b is constant and nonzero
 * - b must be normalized
 */
extern bool arith_buffer_is_nonzero(arith_buffer_t *b);


/*
 * Check whether b is constant and positive, negative, etc.
 * - b must be normalized
 */
extern bool arith_buffer_is_pos(arith_buffer_t *b);
extern bool arith_buffer_is_neg(arith_buffer_t *b);
extern bool arith_buffer_is_nonneg(arith_buffer_t *b);
extern bool arith_buffer_is_nonpos(arith_buffer_t *b);


/*
 * Check whether b is of the form a * X - a * Y
 * for a non-zero rational a and two products X and Y.
 * If so return X in *r1 and Y in *r2
 */
extern bool arith_buffer_is_equality(arith_buffer_t *b, pprod_t **r1, pprod_t **r2);


/*
 * Check whether b is of the form 1 * X for a non-null power-product X
 * If so return X in *r
 */
extern bool arith_buffer_is_product(arith_buffer_t *b, pprod_t **r);


/*
 * Get degree of polynomial in buffer b.
 * - b must be normalized
 * - returns 0 if b is zero
 */
extern uint32_t arith_buffer_degree(arith_buffer_t *b);


/*
 * Degree of variable x in b
 * - return largest d such that x^d occurs in b
 * - return 0 if x does not occur in b
 */
extern uint32_t arith_buffer_var_degree(arith_buffer_t *b, int32_t x);


/*
 * Main term = maximal power product of b in the deg-lex ordering.
 * - b must be normalized and non zero
 */
extern pprod_t *arith_buffer_main_term(arith_buffer_t *b);


/*
 * Main monomial = monomial whose pp is the main term
 * - b must be normalized and non zero
 * - this returns the last element in b's monomial list
 */
extern mlist_t *arith_buffer_main_mono(arith_buffer_t *b);


/*
 * Return the monomial of b whose pp is equal to r
 * - return NULL if r does not occur in b
 */
extern mlist_t *arith_buffer_get_mono(arith_buffer_t *b, pprod_t *r);


/*
 * Copy the constant monomial of b
 * - return NULL if b does not have a constant monomial
 */
extern mlist_t *arith_buffer_get_constant_mono(arith_buffer_t *b);


/*
 * Check whether b1 and b2 are equal
 * - both must be normalized and use the same ptbl
 */
extern bool arith_buffer_equal(arith_buffer_t *b1, arith_buffer_t *b2);



/******************************
 *  POLYNOMIAL CONSTRUCTION   *
 *****************************/

/*
 * All operations update the first argument b.
 * They do not ensure that b is normalized.
 *
 * Some operations have a power product r as argument.
 * The power product r must be defined in b's internal
 * power-product table (i.e., either r is empty_pp, or
 * r is a tagged variable, or r occurs in b->ptbl).
 *
 * Some operations use one or two other buffers b1 and b2.  In such
 * cases, b, b1, and b2 must all have the same power-product table.
 */

/*
 * Reset b to the zero polynomial
 */
extern void arith_buffer_reset(arith_buffer_t *b);


/*
 * Set b to the constant 1
 */
extern void arith_buffer_set_one(arith_buffer_t *b);


/*
 * Multiply b by -1
 */
extern void arith_buffer_negate(arith_buffer_t *b);


/*
 * Multiply b by constant a
 */
extern void arith_buffer_mul_const(arith_buffer_t *b, rational_t *a);


/*
 * Divide b by constant a
 * - a must be non-zero
 */
extern void arith_buffer_div_const(arith_buffer_t *b, rational_t *a);


/*
 * Multiply b by power product r
 */
extern void arith_buffer_mul_pp(arith_buffer_t *b, pprod_t *r);


/*
 * Multiply b by (- r)
 */
extern void arith_buffer_mul_negpp(arith_buffer_t *b, pprod_t *r);


/*
 * Multiply b by a * r
 */
extern void arith_buffer_mul_mono(arith_buffer_t *b, rational_t *a, pprod_t *r);



/*
 * Add constant a to b
 */
extern void arith_buffer_add_const(arith_buffer_t *b, rational_t *a);


/*
 * Add constant (-a) to b
 */
extern void arith_buffer_sub_const(arith_buffer_t *b, rational_t *a);


/*
 * Add r to b
 */
extern void arith_buffer_add_pp(arith_buffer_t *b, pprod_t *r);


/*
 * Add -r to b
 */
extern void arith_buffer_sub_pp(arith_buffer_t *b, pprod_t *r);


/*
 * Add a * r to b
 */
extern void arith_buffer_add_mono(arith_buffer_t *b, rational_t *a, pprod_t *r);


/*
 * Add -a * r to b
 */
extern void arith_buffer_sub_mono(arith_buffer_t *b, rational_t *a, pprod_t *r);


/*
 * Add b1 to b
 */
extern void arith_buffer_add_buffer(arith_buffer_t *b, arith_buffer_t *b1);


/*
 * Add (-b1) to b
 */
extern void arith_buffer_sub_buffer(arith_buffer_t *b, arith_buffer_t *b1);


/*
 * Multiply b by b1
 * - b1 must be different from b
 */
extern void arith_buffer_mul_buffer(arith_buffer_t *b, arith_buffer_t *b1);


/*
 * Compute the square of b
 */
extern void arith_buffer_square(arith_buffer_t *b);


/*
 * Add a * b1 to b
 */
extern void arith_buffer_add_const_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a);


/*
 * Add (-a) * b1 to b
 */
extern void arith_buffer_sub_const_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a);


/*
 * Add r * b1 to b
 */
extern void arith_buffer_add_pp_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, pprod_t *r);


/*
 * Add - r * b1 to b
 */
extern void arith_buffer_sub_pp_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, pprod_t *r);


/*
 * Add a * r * b1 to b
 */
extern void arith_buffer_add_mono_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a, pprod_t *r);

/*
 * Add -a * r * b1 to b
 */
extern void arith_buffer_sub_mono_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a, pprod_t *r);


/*
 * Add b1 * b2 to b
 * - b1 and b2 must be distinct from b (but b1 may be equal to b2)
 */
extern void arith_buffer_add_buffer_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, arith_buffer_t *b2);


/*
 * Add - b1 * b2 to b
 * - b1 and b2 must be distinct from b (but b1 may be equal to b2)
 */
extern void arith_buffer_sub_buffer_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, arith_buffer_t *b2);





/*************************************
 *  OPERATIONS WITH MONOMIAL ARRAYS  *
 ************************************/

/*
 * A monomial array contains a monomials of the form (coeff, index)
 * where indices are signed integers. Operations between buffers and
 * monomial arrays require to convert the integer indices used by
 * monomials to power products used by buffers.
 *
 * All operations below take three arguments:
 * - b is an arithmetic buffer
 * - poly is an array of monomials
 * - pp is an array of power products
 *   if poly[i] is a monomial a_i x_i then pp[i] must be the conversion
 *   of x_i to a power product.
 *
 * All operations are in place operations on the first argument b
 * (i.e., all modify the buffer). There are two requirements
 * on mono and pp:
 * - poly must be terminated by and end-marker (var = max_idx).
 * - pp must be sorted in the deg-lex ordering and have at least
 *   as many elements as length of mono - 1.
 * In particular, if poly contains a constant monomial (with x_i = const_idx),
 * then that monomial must comes first (i.e., i must be 0) and pp[0] must
 * be empty_pp.
 */

/*
 * Add poly to buffer b
 */
extern void arith_buffer_add_monarray(arith_buffer_t *b, monomial_t *poly, pprod_t **pp);


/*
 * Subtract poly from buffer b
 */
extern void arith_buffer_sub_monarray(arith_buffer_t *b, monomial_t *poly, pprod_t **pp);


/*
 * Add a * poly to buffer b
 */
extern void arith_buffer_add_const_times_monarray(arith_buffer_t *b, monomial_t *poly, pprod_t **pp, rational_t *a);


/*
 * Subtract a * poly from b
 */
extern void arith_buffer_sub_const_times_monarray(arith_buffer_t *b, monomial_t *poly, pprod_t **pp, rational_t *a);


/*
 * Add a * r * poly to b
 */
extern void arith_buffer_add_mono_times_monarray(arith_buffer_t *b, monomial_t *poly, pprod_t **pp, rational_t *a, pprod_t *r);


/*
 * Add -a * r * poly to b
 */
extern void arith_buffer_sub_mono_times_monarray(arith_buffer_t *b, monomial_t *poly, pprod_t **pp, rational_t *a, pprod_t *r);


/*
 * Multiply b by poly
 */
extern void arith_buffer_mul_monarray(arith_buffer_t *b, monomial_t *poly, pprod_t **pp);


/*
 * Multiply b by  p ^ d
 * - pp = power products for the variables of p
 * - use aux as an auxiliary buffer (aux must be distinct from b)
 * - store the result in b (normalized)
 */
extern void arith_buffer_mul_monarray_power(arith_buffer_t *b, monomial_t *poly, pprod_t **pp, uint32_t d, arith_buffer_t *aux);



/*******************************************************************
 *  SUPPORT FOR HASH CONSING AND CONVERSION TO POLYNOMIAL OBJECTS  *
 ******************************************************************/

/*
 * The conversion of a buffer b to a polynomial object requires two steps:
 * 1) convert all the power-products in b to integer indices.
 *    This must map empty_pp to const_idx and end_pp to max_idx.
 * 2) build a polynomial from the coefficients of b and the integer indices
 *
 * The operations below use a buffer b and an integer array v.
 * The array v stores the conversion from power-products to integer indices:
 * If b contains a_0 r_0 + ... + a_n r_n then v must have (n+2) elements
 * and the integer index for power product r_i is v[i], and the last element
 * of v must be max_idx.
 *
 * The pair (b, v) defines then a polynomial P(b, v) = a_1 v[1] + ... + a_n v[n],
 */

/*
 * Hash code for P(b, v).
 * This function is consistent with hash_polynomial defined in polynomials.c:
 * If P(b, v) = p0 then hash_arith_buffer(b, v) = hash_polynomial(p0).
 */
extern uint32_t hash_arith_buffer(arith_buffer_t *b, int32_t *v);


/*
 * Check where P(b, v) is equal to p
 */
extern bool arith_buffer_equal_poly(arith_buffer_t *b, int32_t *v, polynomial_t *p);


/*
 * Build P(b, v) (i.e., convert b to a polynomial then reset b).
 * SIDE EFFECT: b is reset to the zero polynomial.
 */
extern polynomial_t *arith_buffer_get_poly(arith_buffer_t *b, int32_t *v);





/****************
 *  SHORT CUTS  *
 ***************/

/*
 * All operations that take a power product r have a variant that takes a single
 * variable x as argument.
 */

/*
 * Multiply b by x
 */
static inline void arith_buffer_mul_var(arith_buffer_t *b, int32_t x) {
  arith_buffer_mul_pp(b, var_pp(x));
}


/*
 * Multiply b by (- x)
 */
static inline void arith_buffer_mul_negvar(arith_buffer_t *b, int32_t x) {
  arith_buffer_mul_negpp(b, var_pp(x));
}


/*
 * Multiply b by a * x
 */
static inline void arith_buffer_mul_varmono(arith_buffer_t *b, rational_t *a, int32_t x) {
  arith_buffer_mul_mono(b, a, var_pp(x));
}


/*
 * Add x to b
 */
static inline void arith_buffer_add_var(arith_buffer_t *b, int32_t x) {
  arith_buffer_add_pp(b, var_pp(x));
}


/*
 * Add -x to b
 */
static inline void arith_buffer_sub_var(arith_buffer_t *b, int32_t x) {
  arith_buffer_sub_pp(b, var_pp(x));
}


/*
 * Add a * x to b
 */
static inline void arith_buffer_add_varmono(arith_buffer_t *b, rational_t *a, int32_t x) {
  arith_buffer_add_mono(b, a, var_pp(x));
}


/*
 * Add -a * x to b
 */
static inline void arith_buffer_sub_varmono(arith_buffer_t *b, rational_t *a, int32_t x) {
  arith_buffer_sub_mono(b, a, var_pp(x));
}


/*
 * Add x * b1 to b
 */
static inline void arith_buffer_add_var_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, int32_t x) {
  arith_buffer_add_pp_times_buffer(b, b1, var_pp(x));
}


/*
 * Add - x * b1 to b
 */
static inline void arith_buffer_sub_var_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, int32_t x) {
  arith_buffer_sub_pp_times_buffer(b, b1, var_pp(x));
}


/*
 * Add a * x * b1 to b
 */
static inline void
arith_buffer_add_varmono_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a, int32_t x) {
  arith_buffer_add_mono_times_buffer(b, b1, a, var_pp(x));
}


/*
 * Add -a * x * b1 to b
 */
static inline void
arith_buffer_sub_varmono_times_buffer(arith_buffer_t *b, arith_buffer_t *b1, rational_t *a, int32_t x) {
  arith_buffer_sub_mono_times_buffer(b, b1, a, var_pp(x));
}



#endif /* __ARITH_BUFFERS_H */
