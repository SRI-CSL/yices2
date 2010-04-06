/*
 * BIT-VECTOR POLYNOMIALS
 */

/*
 * Polynomials with bit-vector coefficients
 * represented as arrays of monomials.
 * Each monomial is a pair <coeff, variable>
 * - coeff is a bit-vector constant, stored as
 *   an array of 32bit words (cf. bv_constants).
 * - variable is a 32bit integer.
 *
 * More polynomial operations are defined in
 * bvarith_buffers.c.
 */

#ifndef __BV_POLYNOMIALS_H
#define __BV_POLYNOMIALS_H

#include <stdint.h>
#include <stdbool.h>

#include "bv_constants.h"
#include "polynomial_common.h"

/*
 * Polynomial structure:
 * - bitsize = number of bits
 * - width = coefficient size in words = ceil(bitsize/32)
 * - nterms = number of monomials
 * - mono = array of (nterms + 1) monomials
 * Polynomials are normalized:
 * - the coefficients are non zero.
 * - the monomials are sorted.
 * - mono[nterms].var contains the end marker max_idx
 */

// monomial
typedef struct {
  int32_t var;
  uint32_t *coeff;
} bvmono_t;

// polynomial
typedef struct {
  int32_t nterms;
  uint32_t bitsize;
  uint32_t width;
  bvmono_t mono[0]; // actual size = nterms + 1
} bvpoly_t;


/*
 * Maximal number of terms in a polynomial
 */
#define MAX_BVPOLY_SIZE (((UINT32_MAX-sizeof(bvpoly_t))/sizeof(bvmono_t))-1)


/*
 * Allocate a bit-vector polynomial
 * - n = number of terms (excluding the end marker)
 * - n must be less than MAXBV_POLY_SIZE
 * - size = bitsize (must be positive and no more than YICES_MAX_BVSIZE)
 * The coefficients and variables are not initialized,
 * except the end marker.
 */ 
extern bvpoly_t *alloc_bvpoly(uint32_t n, uint32_t size);


/*
 * Free p and all the coefficents
 */
extern void free_bvpoly(bvpoly_t *p);


/*
 * Return the main variable of p (i.e., last variable)
 * - return null_idx if p is zero
 * - return const_idx is p is a constant
 */
extern int32_t bvpoly_main_var(bvpoly_t *p);


/*
 * Check whether p1 and p2 are equal
 */
extern bool equal_bvpoly(bvpoly_t *p1, bvpoly_t *p2);


/*
 * Check for simple disequality: return true if (p1 - p2) is a non-zero constant
 * bitvector.
 */
extern bool disequal_bvpoly(bvpoly_t *p1, bvpoly_t *p2);


#endif /* __BV_POLYNOMIALS_H */
