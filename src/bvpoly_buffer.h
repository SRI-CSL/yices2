/*
 * Buffer for construction of bitvector polynomials
 * - simpler than the bvarith_buffer defined in bvarith_expr.h
 * - independent of any variable manager
 */

#ifndef __BVPOLY_BUFFER_H
#define __BVPOLY_BUFFER_H

#include <stdint.h>
#include <stdbool.h>

#include "bitvectors.h"
#include "bvarith_expr.h"
#include "egraph_base_types.h"

/*
 * Buffer:
 * - the polynomial under construction is stored in as
 *   array of variables and an array of coefficients.
 * - the variables are in var[0 ... nterms-1]
 * - the coefficients are bitvector constants of identical
 *   size (i.e., number of bits).
 * - if size is small (64 bits or less), the coefficients
 *   are stored as uint64_t integers c[0 ... nterms-1]
 * - if size if more than 64 bits, the coefficients are 
 *   stored in arrays of 32bit words (cf. bv_constants.h).
 *   The array pointers are p[0...nterms-1]
 * - sign = a sign bit for each coeffcient (0 ... nterms-1)
 *   sign bit = 1 means negated
 *   The sign bit is set after normalization. 
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
  thvar_t *var;
  uint64_t *c;
  uint32_t **p;
  byte_t *sign;
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
#define DEF_BVPOLYBUFFER_SIZE 10
#define MAX_BVPOLYBUFFER_SIZE MAX_BVPOLY_SIZE

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
 * Operations are
 * - add_monomial:    add        a * x
 * - sub_monomial:    subtract   a * x
 * - add_var:         add        1 * x
 * - sub_var:         subtract   1 * x
 * - addmul_monomial: add        a * b * x
 * - submul_monomial: subtract   a * b * x
 *
 * The word-size and bit size are taken from the buffer's internal 
 * width and bitsize. That must be set before all operations by
 * calling reset_bvpoly_buffer.
 *
 * In all cases, x must be an integer between 0 and max_idx-1 
 * 
 */
// small coefficients (no more than 64 bits)
extern void bvpoly_buffer_add_mono64(bvpoly_buffer_t *buffer, thvar_t x, uint64_t a);
extern void bvpoly_buffer_sub_mono64(bvpoly_buffer_t *buffer, thvar_t x, uint64_t a);
extern void bvpoly_buffer_addmul_mono64(bvpoly_buffer_t *buffer, thvar_t x, uint64_t a, uint64_t b);
extern void bvpoly_buffer_submul_mono64(bvpoly_buffer_t *buffer, thvar_t x, uint64_t a, uint64_t b);

// large coefficients (more than 64 bits) a = array of words
extern void bvpoly_buffer_add_monomial(bvpoly_buffer_t *buffer, thvar_t x, uint32_t *a);
extern void bvpoly_buffer_sub_monomial(bvpoly_buffer_t *buffer, thvar_t x, uint32_t *a);
extern void bvpoly_buffer_addmul_monomial(bvpoly_buffer_t *buffer, thvar_t x, uint32_t *a, uint32_t *b);
extern void bvpoly_buffer_submul_monomial(bvpoly_buffer_t *buffer, thvar_t x, uint32_t *a, uint32_t *b);

extern void bvpoly_buffer_add_var(bvpoly_buffer_t *buffer, thvar_t x);
extern void bvpoly_buffer_sub_var(bvpoly_buffer_t *buffer, thvar_t x);


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





/*******************
 *  NORMALIZATION  *
 ******************/

/*
 * Normalize buffer:
 * - normalize all the coefficients (reduce them modulo 2^n where n = bitsize)
 * - replace coeff a by -a if (-a) has fewer 1-bits than a 
 *   (e.g., if a is 0b111...1, then it's replaced by - 0b000001)
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
static inline uint32_t bvpoly_buffer_var(bvpoly_buffer_t *b, uint32_t i) {
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
 * Test the sign of coefficient i.
 * The bit sign is valid only after normalization
 * - sign_bit returns 0 or 1  (0 means positive coefficiemt
 * - is_pos, is_neg check the sign bit
 */
static inline uint32_t bvpoly_buffer_sign(bvpoly_buffer_t *b, uint32_t i) {
  assert(i < b->nterms);
  return tst_bit(b->sign, i);
}

static inline bool bvpoly_buffer_is_neg(bvpoly_buffer_t *b, uint32_t i) {
  assert(i < b->nterms);
  return tst_bit(b->sign, i);
}

static inline bool bvpoly_buffer_is_pos(bvpoly_buffer_t *b, uint32_t i) {
  return ! bvpoly_buffer_is_neg(b, i);
}



#endif /* __BVPOLY_BUFFER_H */
