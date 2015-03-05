/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Buffer for construction of bitvector polynomials
 * - simpler than the bvarith_buffer and bvarith64_buffer
 */

#ifndef __BVPOLY_BUFFERS_H
#define __BVPOLY_BUFFERS_H

#include <stdint.h>
#include <stdbool.h>

#include "terms/bv64_polynomials.h"
#include "terms/bv_polynomials.h"


/*
 * Buffer:
 * - the polynomial under construction is stored in an
 *   array of variables and an array of coefficients.
 * - the variables are in var[0 ... nterms-1]
 * - the coefficients are bitvector constants of identical
 *   size (i.e., number of bits).
 * - if size is small (64 bits or less), the coefficients
 *   are stored as uint64_t integers c[0 ... nterms-1]
 * - if size if more than 64 bits, the coefficients are
 *   stored in arrays of 32bit words (cf. bv_constants.h).
 *   The array pointers are p[0...nterms-1]
 *
 * Index array:
 * - if variable x is present in the polynomial, i.e., var[i] = x
 *   then index[x] = i
 * - otherwise index[x] = -1
 * - const_idx = 0 is used to denote constants
 *
 * Other components:
 * - nterms = number of terms in the polynomial
 * - bitsize = number of bits in each coefficient
 * - width = ceil (bitsize /32) = number of words needed to
 *   store the coefficients
 * - i_size = size of the index array
 * - m_size = size of the vars and coefficient arrays
 * - w_size = size of all the arrays p[0 ... m_size -1]
 * - if w_size = 0, p is NULL
 */
typedef struct bvpoly_buffer_s {
  int32_t *index;
  int32_t *var;
  uint64_t *c;
  uint32_t **p;
  uint32_t nterms;
  uint32_t bitsize;
  uint32_t width;
  uint32_t i_size;
  uint32_t m_size;
  uint32_t w_size;
} bvpoly_buffer_t;


/*
 * Default and maximal sizes for the buffer components
 */
// for m_size
#define DEF_BVPOLYBUFFER_SIZE 10
#define MAX_BVPOLYBUFFER_SIZE (UINT32_MAX/8)

// for i_size
#define DEF_BVPOLYBUFFER_ISIZE 100
#define MAX_BVPOLYBUFFER_ISIZE (UINT32_MAX/4)



/***********************
 *  CREATION/DELETION  *
 **********************/

/*
 * Initialize buffer
 * - i_size and m_size are initialized to the default
 * - bitsize is set to 0
 * - w_size is 0
 */
extern void init_bvpoly_buffer(bvpoly_buffer_t *buffer);

/*
 * Reset and prepare to construct a polynomial with
 * the given bitsize
 * - bitsize must be positive
 */
extern void reset_bvpoly_buffer(bvpoly_buffer_t *buffer, uint32_t bitsize);

/*
 * Delete: free memory
 */
extern void delete_bvpoly_buffer(bvpoly_buffer_t *buffer);




/***************************
 *  ADDITION OF MONOMIALS  *
 **************************/

/*
 * There are two versions depending on the coefficient size
 *
 * Operations are
 * - add_monomial:    add        a * x
 * - sub_monomial:    subtract   a * x
 * - addmul_monomial: add        a * b * x
 * - submul_monomial: subtract   a * b * x
 *
 * - add_var:         add        1 * x
 * - sub_var:         subtract   1 * x
 *
 * The word-size and bit size are taken from the buffer's internal
 * width and bitsize. That must be set before all operations by
 * calling reset_bvpoly_buffer.
 *
 * In all cases, x must be an integer between 0 and max_idx-1
 *
 */
// small coefficients (no more than 64 bits)
extern void bvpoly_buffer_add_mono64(bvpoly_buffer_t *buffer, int32_t x, uint64_t a);
extern void bvpoly_buffer_sub_mono64(bvpoly_buffer_t *buffer, int32_t x, uint64_t a);
extern void bvpoly_buffer_addmul_mono64(bvpoly_buffer_t *buffer, int32_t x, uint64_t a, uint64_t b);
extern void bvpoly_buffer_submul_mono64(bvpoly_buffer_t *buffer, int32_t x, uint64_t a, uint64_t b);

// large coefficients (more than 64 bits) a = array of words
extern void bvpoly_buffer_add_monomial(bvpoly_buffer_t *buffer, int32_t x, uint32_t *a);
extern void bvpoly_buffer_sub_monomial(bvpoly_buffer_t *buffer, int32_t x, uint32_t *a);
extern void bvpoly_buffer_addmul_monomial(bvpoly_buffer_t *buffer, int32_t x, uint32_t *a, uint32_t *b);
extern void bvpoly_buffer_submul_monomial(bvpoly_buffer_t *buffer, int32_t x, uint32_t *a, uint32_t *b);

// no coefficients
extern void bvpoly_buffer_add_var(bvpoly_buffer_t *buffer, int32_t x);
extern void bvpoly_buffer_sub_var(bvpoly_buffer_t *buffer, int32_t x);


// add/subtract constants
static inline void bvpoly_buffer_add_const64(bvpoly_buffer_t *buffer, uint64_t a) {
  bvpoly_buffer_add_mono64(buffer, const_idx, a);
}

static inline void bvpoly_buffer_sub_const64(bvpoly_buffer_t *buffer, uint64_t a) {
  bvpoly_buffer_sub_mono64(buffer, const_idx, a);
}

static inline void bvpoly_buffer_add_constant(bvpoly_buffer_t *buffer, uint32_t *a) {
  bvpoly_buffer_add_monomial(buffer, const_idx, a);
}

static inline void bvpoly_buffer_sub_constant(bvpoly_buffer_t *buffer, uint32_t *a) {
  bvpoly_buffer_sub_monomial(buffer, const_idx, a);
}

static inline void bvpoly_buffer_add_one(bvpoly_buffer_t *buffer) {
  bvpoly_buffer_add_var(buffer, const_idx);
}

static inline void bvpoly_buffer_sub_one(bvpoly_buffer_t *buffer) {
  bvpoly_buffer_sub_var(buffer, const_idx);
}

// add/subtract a * b
static inline void bvpoly_buffer_addmul_const64(bvpoly_buffer_t *buffer, uint64_t a, uint64_t b) {
  bvpoly_buffer_addmul_mono64(buffer, const_idx, a, b);
}

static inline void bvpoly_buffer_submul_const64(bvpoly_buffer_t *buffer, uint64_t a, uint64_t b) {
  bvpoly_buffer_submul_mono64(buffer, const_idx, a, b);
}

static inline void bvpoly_buffer_addmul_constant(bvpoly_buffer_t *buffer, uint32_t *a, uint32_t *b) {
  bvpoly_buffer_addmul_monomial(buffer, const_idx, a, b);
}

static inline void bvpoly_buffer_submul_constant(bvpoly_buffer_t *buffer, uint32_t *a, uint32_t *b) {
  bvpoly_buffer_submul_monomial(buffer, const_idx, a, b);
}




/*****************************
 *  ADDITION OF POLYNOMIALS  *
 ****************************/

/*
 * Operations:
 * - add_poly:           add      p
 * - sub_poly:           subtract p
 * - addmul_poly:        add      a * p
 * - submul_poly:        subtract a * p
 *
 * Each operation exists in two versions (for bvpoly64 and bvpoly).
 * The bitsize of p must match the buffer's bitsize.
 */
extern void bvpoly_buffer_add_poly64(bvpoly_buffer_t *buffer, bvpoly64_t *p);
extern void bvpoly_buffer_sub_poly64(bvpoly_buffer_t *buffer, bvpoly64_t *p);
extern void bvpoly_buffer_addmul_poly64(bvpoly_buffer_t *buffer, bvpoly64_t *p, uint64_t a);
extern void bvpoly_buffer_submul_poly64(bvpoly_buffer_t *buffer, bvpoly64_t *p, uint64_t a);

extern void bvpoly_buffer_add_poly(bvpoly_buffer_t *buffer, bvpoly_t *p);
extern void bvpoly_buffer_sub_poly(bvpoly_buffer_t *buffer, bvpoly_t *p);
extern void bvpoly_buffer_addmul_poly(bvpoly_buffer_t *buffer, bvpoly_t *p, uint32_t *a);
extern void bvpoly_buffer_submul_poly(bvpoly_buffer_t *buffer, bvpoly_t *p, uint32_t *a);



/*******************
 *  SUBSTITUTIONS  *
 ******************/

/*
 * Replace variable x by polynomial p in buffer.
 * There are two versions: one for 64bit or less, one for more than 64bits.
 * - x must be a variable (i.e., x != const_idx)
 * - x must not occur in p
 */
extern void bvpoly_buffer_subst_poly64(bvpoly_buffer_t *buffer, int32_t x, bvpoly64_t *p);
extern void bvpoly_buffer_subst_poly(bvpoly_buffer_t *buffer, int32_t x, bvpoly_t *p);



/*******************
 *  NORMALIZATION  *
 ******************/

/*
 * Normalize buffer:
 * - normalize all the coefficients (reduce them modulo 2^n where n = bitsize)
 * - sort the terms in increasing order of variables
 *   (the constant term comes first if any)
 * - remove all terms with a zero coefficient
 */
extern void normalize_bvpoly_buffer(bvpoly_buffer_t *buffer);




/*************************************
 *  ACCESS TO THE BUFFER COMPONENTS  *
 ************************************/

/*
 * Number of terms, bitsize and width
 */
static inline uint32_t bvpoly_buffer_num_terms(bvpoly_buffer_t *b) {
  return b->nterms;
}

static inline uint32_t bvpoly_buffer_bitsize(bvpoly_buffer_t *b) {
  return b->bitsize;
}

static inline uint32_t bvpoly_buffer_width(bvpoly_buffer_t *b) {
  return b->width;
}

/*
 * Components of monomial i
 */
static inline int32_t bvpoly_buffer_var(bvpoly_buffer_t *b, uint32_t i) {
  assert(i < b->nterms);
  return b->var[i];
}

static inline uint64_t bvpoly_buffer_coeff64(bvpoly_buffer_t *b, uint32_t i) {
  assert(i < b->nterms && b->bitsize <= 64);
  return b->c[i];
}

static inline uint32_t *bvpoly_buffer_coeff(bvpoly_buffer_t *b, uint32_t i) {
  assert(i < b->nterms && b->bitsize > 64);
  return b->p[i];
}


/*
 * Check whether b is a constant polynomial
 * - b must be normalized
 */
static inline bool bvpoly_buffer_is_zero(bvpoly_buffer_t *b) {
  return b->nterms == 0;
}

static inline bool bvpoly_buffer_is_constant(bvpoly_buffer_t *b) {
  return b->nterms == 0 || (b->nterms == 1 && b->var[0] == const_idx);
}


/*******************************
 *  CONVERSION TO POLYNOMIALS  *
 ******************************/

/*
 * Convert b to a bvpoly64 object
 * - b must be normalized and have bitsize <= 64
 * - the resulting object can be deleted using safe_free (or free_bvpoly64)
 */
extern bvpoly64_t *bvpoly_buffer_getpoly64(bvpoly_buffer_t *b);


/*
 * Convert b to a bvpoly object
 * - b must be normalized and have bitsize > 64
 * - the resulting bvpoly can be deleted using free_bvpoly
 */
extern bvpoly_t *bvpoly_buffer_getpoly(bvpoly_buffer_t *b);



/*********************************
 *  COMPARISON WITH POLYNOMIALS  *
 ********************************/

/*
 * Check whether b equals p
 * - b must be normalized
 */
extern bool bvpoly_buffer_equal_poly64(bvpoly_buffer_t *b, bvpoly64_t *p);


/*
 * Same thing for a bvpoly
 * - b must be normalized
 */
extern bool bvpoly_buffer_equal_poly(bvpoly_buffer_t *b, bvpoly_t *p);



/*
 * Hash function1
 * - b must be normalized and have bitsize <= 64
 * - if b is equal to a bvpoly64 p then
 *   hash_bvpoly64(p) == bvpoly_buffer_hash64(b)
 */
extern uint32_t bvpoly_buffer_hash64(bvpoly_buffer_t *b);


/*
 * Hash function2:
 * - b must be normalized and have bitsize > 64
 * - if b is equal to a bvpoly p then
 *   hash_bvpoly(p) == bvpoly_buffer_hash(b)
 */
extern uint32_t bvpoly_buffer_hash(bvpoly_buffer_t *b);


#endif /* __BVPOLY_BUFFERS_H */
