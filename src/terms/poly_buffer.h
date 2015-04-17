/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Buffer for polynomial construction in an arithmetic solver.
 * (Simpler than arith_buffers/Supports only linear arithmetic).
 *
 * The buffer may be normalized or not.
 * - once the buffer is normalized, the monomials are sorted, all coefficients
 *   are non-zero and there is an end marker
 * - operations such as adding monomials or polynomials do not require the
 *   input buffer to be normalized, and their result is not normalized.
 */

#ifndef __POLY_BUFFER_H
#define __POLY_BUFFER_H

#include <assert.h>
#include <stdint.h>
#include <stdbool.h>

#include "solvers/simplex/matrices.h"
#include "terms/polynomials.h"


/*
 * Buffer for constructing polynomials
 * - the polynomial under construction is stored in a monomial array
 *   (i.e., in mono[0 ... nterms - 1])
 * - array index maps variables to the corresponding monomial
 * For a variable x:
 * - buffer->index[x] = -1 if there's no monomial of the form a * x
 * - otherwise buffer->index[x] = i, where mono[i] is a * x
 *
 * As in polynomials.h, const_idx = 0 is used to denote constants.
 * (e.g., 3 + 2 x is represented as 3 * const_idx + 2 * x)
 */
typedef struct poly_buffer_s {
  int32_t *index;   // index array
  monomial_t *mono; // monomial array
  rational_t aux;   // auxiliary buffer
  uint32_t i_size;  // size of the index array
  uint32_t m_size;  // size of the monomial array
  uint32_t nterms;  // number of monomials
} poly_buffer_t;


/*
 * Default initial m_size for a buffer
 * The maximal m_size is MAX_POLY_SIZE, defined in polynomials.h
 * For i_size: default = 100
 */
#define DEF_POLYBUFFER_MSIZE 10
#define MAX_POLYBUFFER_MSIZE MAX_POLY_SIZE

#define DEF_POLYBUFFER_ISIZE 100
#define MAX_POLYBUFFER_ISIZE (UINT32_MAX/4)


/*
 * Initialize a buffer:
 * - m_size and i_size are set to their default values
 */
extern void init_poly_buffer(poly_buffer_t *buffer);


/*
 * Delete buffer: free all internally allocated memory
 */
extern void delete_poly_buffer(poly_buffer_t *buffer);


/*
 * Reset the buffer: clear all mpq_t numbers it contains
 * and reset it to zero.
 */
extern void reset_poly_buffer(poly_buffer_t *buffer);



/*
 * CONSTRUCTION OF POLYNOMIALS
 */

/*
 * Add monomials to the buffer
 * - poly_buffer_add_monomial: add              a * x
 * - poly_buffer_sub_monomial: subtract         a * x
 * - poly_buffer_add_var:      add monomial     1 * x
 * - poly_buffer_sub_var:      add monomial    -1 * x
 * - poly_buffer_addmul_monomial: add       a * b * x
 * - poly_buffer_submul_monomial: subtract  a * b * x
 * In all cases, x must be an integer between 0 and max_idx - 1
 *
 * The result is not in normal form.
 */
extern void poly_buffer_add_monomial(poly_buffer_t *buffer, int32_t x, rational_t *a);
extern void poly_buffer_sub_monomial(poly_buffer_t *buffer, int32_t x, rational_t *a);
extern void poly_buffer_add_var(poly_buffer_t *buffer, int32_t x);
extern void poly_buffer_sub_var(poly_buffer_t *buffer, int32_t x);
extern void poly_buffer_submul_monomial(poly_buffer_t *buffer, int32_t x, rational_t *a, rational_t *b);
extern void poly_buffer_addmul_monomial(poly_buffer_t *buffer, int32_t x, rational_t *a, rational_t *b);


/*
 * Clear a monomial: make coefficient of x equal to zero
 * - x must be between 0 and max_idx - 1
 */
extern void poly_buffer_clear_monomial(poly_buffer_t *buffer, int32_t x);


/*
 * Short cuts: for add_const and sub_const
 */
static inline void poly_buffer_add_const(poly_buffer_t *buffer, rational_t *a) {
  poly_buffer_add_monomial(buffer, const_idx, a);
}

static inline void poly_buffer_sub_const(poly_buffer_t *buffer, rational_t *a) {
  poly_buffer_sub_monomial(buffer, const_idx, a);
}

static inline void poly_buffer_add_one(poly_buffer_t *buffer) {
  poly_buffer_add_var(buffer, const_idx);
}

static inline void poly_buffer_sub_one(poly_buffer_t *buffer) {
  poly_buffer_sub_var(buffer, const_idx);
}


/*
 * Short cut for clear_const: make constant equal to zero
 */
static inline void poly_buffer_clear_const(poly_buffer_t *buffer) {
  poly_buffer_clear_monomial(buffer, const_idx);
}



/*
 * Add polynomials:
 * - p is given as an array of n monomials
 * - n = number of monomials in p
 *
 * addmul means add a * p to buffer
 * submul maans subtract a * p from buffer
 */
extern void poly_buffer_add_monarray(poly_buffer_t *buffer, monomial_t *p, uint32_t n);
extern void poly_buffer_sub_monarray(poly_buffer_t *buffer, monomial_t *p, uint32_t n);
extern void poly_buffer_addmul_monarray(poly_buffer_t *buffer, monomial_t *p, uint32_t n, rational_t *a);
extern void poly_buffer_submul_monarray(poly_buffer_t *buffer, monomial_t *p, uint32_t n, rational_t *a);



/*
 * Same operations with p given as a polynomial object
 */
static inline  void poly_buffer_add_poly(poly_buffer_t *buffer, polynomial_t *p) {
  poly_buffer_add_monarray(buffer, p->mono, p->nterms);
}

static inline void poly_buffer_sub_poly(poly_buffer_t *buffer, polynomial_t *p) {
  poly_buffer_sub_monarray(buffer, p->mono, p->nterms);
}

static inline void poly_buffer_addmul_poly(poly_buffer_t *buffer, polynomial_t *p, rational_t *a) {
  poly_buffer_addmul_monarray(buffer, p->mono, p->nterms, a);
}

static inline void poly_buffer_submul_poly(poly_buffer_t *buffer, polynomial_t *p, rational_t *a) {
  poly_buffer_submul_monarray(buffer, p->mono, p->nterms, a);
}


/*
 * Substitute basic variables in buffer
 * - matrix must be in tableau form
 * - if y is a basic variable in matrix, then it occurs in a single row
 *   of the form (y + a_1 x_1 + ... + a_n x_n) = 0
 * - the function replaces y by - (a_1 x_1 + ... + a_n x_n) in buffer,
 *   for all basic variables y.
 */
extern void poly_buffer_substitution(poly_buffer_t *buffer, matrix_t *matrix);






/*
 * READ COEFFICIENTS
 */

/*
 * Check whether variable x occurs in buffer
 * - x must be between 0 (const_idx) and max_idx
 * - if buffer is not normalized, this function returns true if x
 *   occurs with coefficient 0 in buffer.
 */
static inline bool poly_buffer_has_var(poly_buffer_t *buffer, int32_t x) {
  assert(0 <= x && x < max_idx);
  return x < buffer->i_size && buffer->index[x] >= 0;
}

/*
 * Get a pointer to the coefficient of x in buffer
 * - x must be between 0 and max_idx
 * - returns NULL if x does not occur in the buffer
 * - IMPORTANT: the pointer may become invalid after the next add/sub/addmul/submul
 */
extern rational_t *poly_buffer_var_coeff(poly_buffer_t *buffer, int32_t x);


/*
 * Copy the coefficient of x into a
 * - x must be between 0 and max_idx.
 * - a is set to zero if x does not occur in buffer
 */
extern void poly_buffer_copy_var_coeff(poly_buffer_t *buffer, rational_t *a, int32_t x);



/*
 * Normalize buffer
 * - sort the monomials and remove all monomials with zero coefficient
 * - add an end-marker (i.e., a monomial with variable == max_idx)
 * - the monomials are sorted in increasing variable order
 * - the constant term (if any) comes first
 */
extern void normalize_poly_buffer(poly_buffer_t *buffer);


/*
 * Multiply by -1
 * - this keeps buffer normalized if it is when the function is called
 */
extern void poly_buffer_negate(poly_buffer_t *buffer);


/*
 * Multiply by constant a (a must not be zero)
 * - this keeps the buffer normalized if it is when the function is called
 */
extern void poly_buffer_rescale(poly_buffer_t *buffer, rational_t *a);



/*
 * POST-NORMALIZATION OPERATIONS: THE FOLLOWING OPERATIONS ASSUME THAT
 * BUFFER IS NORMALIZED
 */

/*
 * To access the buffer after normalization:
 * - the polynomial is stored as a sum of monomials in
 *   buffer->mono[0] ... buffer->mono[n-1]
 *   where buffer->nterms = n
 * - the end-marked is in buffer->mono[n] (so it's not included in the number of terms)
 */
static inline uint32_t poly_buffer_nterms(poly_buffer_t *buffer) {
  return buffer->nterms;
}

static inline monomial_t *poly_buffer_mono(poly_buffer_t *buffer) {
  return buffer->mono;
}


/*
 * Check whether the buffer is the zero polynomial
 */
static inline bool poly_buffer_is_zero(poly_buffer_t *buffer) {
  return buffer->nterms == 0;
}


/*
 * Check whether the buffer is constant
 */
static inline bool poly_buffer_is_constant(poly_buffer_t *buffer) {
  return buffer->nterms == 0 || (buffer->nterms == 1 && buffer->mono[0].var == const_idx);
}

/*
 * Check whether the buffer is constant and non-zero
 */
static inline bool poly_buffer_is_nzconstant(poly_buffer_t *buffer) {
  return buffer->nterms == 1 && buffer->mono[0].var == const_idx;
}

/*
 * Check whether the buffer is constant and positive
 */
static inline bool poly_buffer_is_pos_constant(poly_buffer_t *buffer) {
  return buffer->nterms == 1 && buffer->mono[0].var == const_idx &&
    q_is_pos(&buffer->mono[0].coeff);
}

/*
 * Check whether the buffer is constant and non-negative
 */
static inline bool poly_buffer_is_nonneg_constant(poly_buffer_t *buffer) {
  return buffer->nterms == 0 || (buffer->nterms == 1 && buffer->mono[0].var == const_idx &&
          q_is_nonneg(&buffer->mono[0].coeff));
}

/*
 * Check whether the buffer is constant and negative
 */
static inline bool poly_buffer_is_neg_constant(poly_buffer_t *buffer) {
  return buffer->nterms == 1 && buffer->mono[0].var == const_idx &&
    q_is_neg(&buffer->mono[0].coeff);
}

/*
 * Check whether the buffer is constant and negative
 */
static inline bool poly_buffer_is_nonpos_constant(poly_buffer_t *buffer) {
  return buffer->nterms == 1 && buffer->mono[0].var == const_idx &&
    q_is_nonpos(&buffer->mono[0].coeff);
}


/*
 * Return a pointer to the main coefficient of p
 * - if buffer is a_0 + a_1 x_1 + ... + a_n x_n in that order, then the
 *   main coeff is a_n
 * - buffer must be non zero
 */
static inline rational_t *poly_buffer_get_main_coeff(poly_buffer_t *buffer) {
  assert(buffer->nterms > 0);
  return &buffer->mono[buffer->nterms - 1].coeff;
}


/*
 * Multiply by the inverse of the main coefficient: this makes the
 * main coefficient equal to one.
 * - return true is the main coefficient was negative
 * - return false otherwise
 * - buffer must be non-zero
 */
extern bool poly_buffer_make_monic(poly_buffer_t *buffer);


/*
 * Make all coefficients integral and make the main coefficient positive:
 * If the buffer contains b + a_1 x_1 + ... + a_n x_n, the result is
 *    Lb + La_1 x_1 + ... + La_n x_n
 * where L is an integer such that
 *    Lb, La_1, ..., La_n are integer and La_n > 0
 *  (L is either the lcm of den(b), den(a_1), ..., den(a_n) or its opposite)
 *
 * - return true if L < 0, false if L > 0
 * - buffer must be non-zero
 */
extern bool poly_buffer_make_integral(poly_buffer_t *buffer);


/*
 * Make all coefficients, except the constant term, integral. Make the main
 * coefficient positive.
 * If the buffer contains b + a_1 x_1 + ... + a_n x_n, the result is
 *    Lb + La_1 x_1 + ... + La_n x_n
 * where L is an integer such that
 *    La_1 ... La_n are integer and La_n > 0
 * (L is either the lcm of den(a_1), ..., den(a_n) or its opposite)
 *
 * - return true is L<0, false if L > 0
 * - buffer must be non-zero
 */
extern bool poly_buffer_make_nonconstant_integral(poly_buffer_t *buffer);



/*
 * Apply the gcd test to buffer:
 * - if buffer contains b + a_1 x_1 + ... + a_n x_n, then
 *   check whether b is a multiple of gcd(a_1, ..., a_n).
 * - if so return true, otherwise return false
 * All coefficients b, a_1, ... , a_n must be integer.
 * If x_1, ..., x_n are integer and the gcd test fails then
 *  (b + a_1 x_1 + ... + a_n a_n) can't be zero
 */
extern bool poly_buffer_gcd_test(poly_buffer_t *buffer);


/*
 * Copy the constant term of buffer, or its opposite, into a
 *
 * NOTE: This is used to construct atoms: for example, to rewrite
 * atom (a + q) >= 0 to (q >= -a)
 */
extern void poly_buffer_get_constant(poly_buffer_t *buffer, rational_t *a);
extern void poly_buffer_get_neg_constant(poly_buffer_t *buffer, rational_t *a);


/*
 * Build the least common multiple of the denominators of buffer's coefficients
 * - store the result in a
 * (i.e., multiplying by lcm makes all coefficients integer)
 */
extern void poly_buffer_get_den_lcm(poly_buffer_t *buffer, rational_t *a);


/*
 * Check whether the normalized buffer is reduced to a single variable or equal to 1
 * (i.e., if it's 1.x for some variable x, where x may be const_idx)
 * - if so return x, otherwise return null_idx = -1
 */
static inline int32_t poly_buffer_convert_to_var(poly_buffer_t *buffer) {
  if (buffer->nterms == 1 && q_is_one(&buffer->mono[0].coeff)) {
    return buffer->mono[0].var;
  }
  return null_idx;
}


/*
 * Check whether the non-constant part of buffer is reduced to a single variable
 * or equal to 0 (i.e., the buffer is either a + x or x, where a
 * is a constant).
 * - if so return x, otherwise return null_idx = -1
 */
extern int32_t poly_buffer_nonconstant_convert_to_var(poly_buffer_t *buffer);


/*
 * Given p = content of buffer, check whether (p == 0) can be rewritten
 * to x = a where x is a variable and a is a rational constant.
 * - if so return the variable index x and copy the constant in a
 * - otherwise, return null_idx and leave a unchanged
 * - buffer must be normalized
 */
extern int32_t poly_buffer_convert_to_vareq(poly_buffer_t *buffer, rational_t *a);


/*
 * Create a polynomial equal to buffer then reset buffer.
 * - buffer must be normalized
 */
extern polynomial_t *poly_buffer_get_poly(poly_buffer_t *buffer);


#endif /* __POLY_BUFFER_H */
