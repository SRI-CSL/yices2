/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BIT-VECTOR POLYNOMIALS
 */

#include <assert.h>

#include "terms/bv_constants.h"
#include "terms/bv_polynomials.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"
#include "yices_limits.h"


/*
 * Allocate a bit-vector polynomial
 * - n = number of terms (excluding the end marker)
 * - size = bitsize. size must positive and no more than YICES_MAX_BVSIZE
 * The coefficients and variables are not initialized, except the end marker.
 */
bvpoly_t *alloc_bvpoly(uint32_t n, uint32_t size) {
  bvpoly_t *tmp;

  assert(0 < size && size <= YICES_MAX_BVSIZE);

  if (n >= MAX_BVPOLY_SIZE) {
    out_of_memory();
  }

  tmp = (bvpoly_t *) safe_malloc(sizeof(bvpoly_t) + (n+1) * sizeof(bvmono_t));
  tmp->nterms = n;
  tmp->bitsize = size;
  tmp->width = (size + 31) >> 5;  // ceiling(size/32)

  // initialize the end marker
  tmp->mono[n].var = max_idx;
  tmp->mono[n].coeff = NULL;

  return tmp;
}


/*
 * Free p and all the coefficients
 */
void free_bvpoly(bvpoly_t *p) {
  uint32_t i, n, k;

  n = p->nterms;
  k = p->width;
  for (i=0; i<n; i++) {
    bvconst_free(p->mono[i].coeff, k);
  }
  safe_free(p);
}



/*
 * Hash code of p
 */
uint32_t hash_bvpoly(bvpoly_t *p) {
  bvmono_t *mono;
  uint32_t h, k, n;

  h = HASH_BVPOLY_SEED + p->nterms;
  k = p->width;
  n = p->bitsize;
  mono = p->mono;
  while (mono->var < max_idx) {
    h = jenkins_hash_array(mono->coeff, k, h);
    h = jenkins_hash_mix3(mono->var, n, h);
    mono ++;
  }

  return h;
}




/*
 * Main variable of p = last variable
 * - return null_idx if p is zero
 * - return const_idx if p is a constant
 */
int32_t bvpoly_main_var(bvpoly_t *p) {
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
bool equal_bvpoly(bvpoly_t *p1, bvpoly_t *p2) {
  bvmono_t *b1, *b2;
  uint32_t k;

  if (p1->nterms != p2->nterms || p1->bitsize != p2->bitsize) {
    return false;
  }

  k = p1->width;
  b1 = p1->mono;
  b2 = p2->mono;
  while (b1->var == b2->var) {
    if (b1->var == max_idx) return true;
    if (bvconst_neq(b1->coeff, b2->coeff, k)) return false;
    b1 ++;
    b2 ++;
  }

  return false;
}


/*
 * Check for simple disequality:
 * - return true if (p1 - p2) is a non-zero constant bitvector.
 * - p1 and p2 must have the same bitsize
 */
bool disequal_bvpoly(bvpoly_t *p1, bvpoly_t *p2) {
  bvmono_t *b1, *b2;
  uint32_t k;

  assert(p1->bitsize == p2->bitsize);

  k = p1->width;
  b1 = p1->mono;
  b2 = p2->mono;

  if (b1->var != const_idx && b2->var != const_idx) {
    // the constant terms are both zero
    return false;
  }

  if (b1->var == const_idx && b2->var == const_idx &&
      bvconst_eq(b1->coeff, b2->coeff, k)) {
    // the constant terms are equal
    return false;
  }

  // skip the constant terms
  if (b1->var == const_idx) b1 ++;
  if (b2->var == const_idx) b2 ++;

  // check that the remaining terms are equal
  while (b1->var == b2->var) {
    if (b1->var == max_idx) return true;
    if (bvconst_neq(b1->coeff, b2->coeff, k)) return false;
    b1 ++;
    b2 ++;
  }

  return false;
}


/*
 * Check whether p is equal to k + x for a non-zero constant k and a variable x
 * - p must be normalized
 */
bool bvpoly_is_const_plus_var(bvpoly_t *p, int32_t x) {
  return p->nterms == 2 && p->mono[0].var == const_idx && p->mono[1].var == x &&
    bvconst_is_one(p->mono[1].coeff, p->width);
}

