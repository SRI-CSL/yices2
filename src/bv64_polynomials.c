/*
 * BIT-VECTOR POLYNOMIALS WITH 64BIT COEFFICIENTS
 */

#include <assert.h>

#include "bv64_polynomials.h"
#include "bv64_constants.h"


/*
 * Allocate a bit-vector polynomial
 * - n = number of terms (excluding the end marker)
 * - n must be less than MAX_BVPOLY64_SIZE
 * - size = bitsize (must be positive and no more than 64)
 * The coefficients and variables are not initialized,
 * except the end marker.
 */ 
bvpoly64_t *alloc_bvpoly64(uint32_t n, uint32_t size) {
  bvpoly64_t *tmp;

  assert(0 < size && size <= 64);

  if (n >= MAX_BVPOLY64_SIZE) {
    out_of_memory();
  }

  tmp = (bvpoly64_t *) safe_malloc(sizeof(bvpoly64_t) + (n+1) * sizeof(bvmono64_t));
  tmp->nterms = n;
  tmp->bitsize = size;

  tmp->mono[n].var = max_idx;
  tmp->mono[n].coeff = 0;

  return tmp;
}


/*
 * Return the main variable of p (i.e., last variable)
 * - return null_idx if p is zero
 * - return const_idx is p is a constant
 */
int32_t bvpoly64_main_var(bvpoly64_t *p) {
  uint32_t n;

  n = p->nterms;
  if (n == 0) {
    return null_idx;
  }
  return p->mono[n-1].var;
}


/*
 * Check whether p1 and p2 are equal
 */
bool equal_bvpoly64(bvpoly64_t *p1, bvpoly64_t *p2) {
  bvmono64_t *b1, *b2;

  if (p1->nterms != p2->nterms || p1->bitsize != p2->bitsize) {
    return false;
  }

  b1 = p1->mono;
  b2 = p2->mono;
  while (b1->var == b2->var) {
    if (b1->var == max_idx) return true;
    if (b1->coeff != b2->coeff) return false;
    b1 ++;
    b2 ++;
  }

  return false;
}


/*
 * Check for simple disequality: return true if (p1 - p2) is a non-zero 
 * constant bitvector.
 * - p1 and p2 must have the same bitsize
 */
bool disequal_bvpoly64(bvpoly64_t *p1, bvpoly64_t *p2) {
  bvmono64_t *b1, *b2;

  assert(p1->bitsize == p2->bitsize);

  b1 = p1->mono;
  b2 = p2->mono;

  if (b1->var != const_idx && b2->var != const_idx) {
    // the constant terms are equal (both are zero)
    return false;
  }

  if (b1->var == const_idx && b2->var == const_idx &&
      b1->coeff == b2->coeff) {
    // equal constant terms
    return false;
  }

  // skip the constants and check that the remaining terms are equal
  if (b1->var == const_idx) b1 ++;
  if (b2->var == const_idx) b2 ++;

  while (b1->var == b2->var) {
    if (b1->var == max_idx) return true;
    if (b1->coeff != b2->coeff) return false;
    b1 ++;
    b2 ++;
  }

  return false;
}




