/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BIT-VECTOR POLYNOMIALS WITH 64BIT COEFFICIENTS
 */

/*
 * Polynomials with small bit-vector coefficients
 * represented as arrays of monomials. This can be
 * used for bit-vector polynomials with bitsize between
 * 1 and 64.
 *
 * Each monomial is a pair <coeff, variable>
 * - coeff is a bit-vector constant, stored as a 64bit integer.
 * - variable is a 32bit integer.
 *
 * Most operations require the polynomial object to be normalized:
 * - the monomials must be sorted and all the coefficients must
 *   be non-zero and reduced modulo 2^bitsize.
 * - the last monomials must be an end marker (var = max_idx)
 *
 * Most related operations are defined in bvarith64_buffers.c.
 */

#ifndef __BV64_POLYNOMIALS_H
#define __BV64_POLYNOMIALS_H

#include <stdint.h>
#include <stdbool.h>

#include "terms/polynomial_common.h"
#include "utils/memalloc.h"

/*
 * Polynomial structure:
 * - bitsize = number of bits (must be between 1 and 64)
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
  uint64_t coeff;
} bvmono64_t;

// polynomial
typedef struct {
  uint32_t nterms;
  uint32_t bitsize;
  bvmono64_t mono[0]; // actual size = nterms + 1
} bvpoly64_t;


/*
 * Maximal number of terms in a polynomial
 */
#define MAX_BVPOLY64_SIZE (((UINT32_MAX-sizeof(bvpoly64_t))/sizeof(bvmono64_t))-1)


/*
 * Seed used in the hash function
 */
#define HASH_BVPOLY64_SEED ((uint32_t) 0xfe4dea20)


/*
 * Allocate a bit-vector polynomial
 * - n = number of terms (excluding the end marker)
 * - n must be less than MAX_BVPOLY64_SIZE
 * - size = bitsize (must be positive and no more than 64)
 * The coefficients and variables are not initialized,
 * except the end marker.
 */
extern bvpoly64_t *alloc_bvpoly64(uint32_t n, uint32_t size);


/*
 * Free p
 */
static inline void free_bvpoly64(bvpoly64_t *p) {
  safe_free(p);
}


/*
 * Hash code of p
 */
extern uint32_t hash_bvpoly64(bvpoly64_t *p);


/*
 * Return the main variable of p (i.e., last variable)
 * - return null_idx if p is zero
 * - return const_idx is p is a constant
 */
extern int32_t bvpoly64_main_var(bvpoly64_t *p);


/*
 * Check whether p1 and p2 are equal
 * - p1 and p2 must be normalized
 */
extern bool equal_bvpoly64(bvpoly64_t *p1, bvpoly64_t *p2);


/*
 * Check for simple disequality: return true if (p1 - p2) is a non-zero
 * constant bitvector.
 * - p1 and p2 must have the same bitsize and must be normalized
 */
extern bool disequal_bvpoly64(bvpoly64_t *p1, bvpoly64_t *p2);


/*
 * Check whether p is equal to k + x for a non-zero constant k and a variable x
 */
extern bool bvpoly64_is_const_plus_var(bvpoly64_t *p, int32_t x);




#endif /* __BV64_POLYNOMIALS_H */
