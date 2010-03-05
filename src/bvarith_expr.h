/*
 * Bit-vector arithmetic expressions.
 *
 * They are represented as polynomials with fixed-width 
 * integer-valued coefficients (bvarith_constants).
 * 
 * Variables are maintained by a polynomial_manager:
 * - primitive variables represent bitvector variables
 * - auxiliary variables represent products of bitvector variables.
 */

#ifndef __BVARITH_EXPR_H
#define __BVARITH_EXPR_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "bv_constants.h"
#include "bitvector_variable_manager.h"
#include "object_stores.h"


/*
 * Polynomials: sums of pairs <coeff, index>
 * - coeff is either an unsigned 64bit integer or a pointer 
 *   to a bvarith_constant of more than 64 bits.
 * - index is a variable (primitive/auxiliary variables)
 *
 * bvarith_expr object:
 * - size = number of bits
 * - nterms = number of monomials
 * - mono = array of (nterms + 1) monomials
 * the polynomial is normalized:
 * - monomials are in increasing order
 * - last monomial has index max_idx (end marker)
 *
 * bvarith_buffer:
 * - list of pairs <coeff, variable> in increasing order
 * - first element is a start marker (index = null_idx)
 * - last element is an end marker (index = max_idx)
 * - size = number of bits
 * - nterms = number of elements in the list, exluding
 *   the start and end marker
 */

typedef int32_t bv_var_t;

// coefficient
typedef union {
  uint64_t c;     // immediate value if it fits in 64 bits
  uint32_t *ptr;  // pointer to value of more than 64 bits
} bvcoeff_t;

// monomial
typedef struct {
  bv_var_t var;
  bvcoeff_t coeff;
} bvmono_t;

/*
 * bvarith_expr = array of nterms + 1 monomials
 * size = number of bits of the polynomial
 * width = ceil(size/32)
 * - if width <= 2, the coefficients are stored in 64bits
 * - if width > 2, the coefficients are more than 64 bits,
 * and are stored indirectly as bvarith_constants.
 */
typedef struct {
  int32_t nterms;
  uint32_t size;
  uint32_t width;
  bvmono_t mono[0]; // actual size = nterms + 1
} bvarith_expr_t;


// list element
typedef struct bvmlist_s {
  struct bvmlist_s *next;
  bv_var_t var;
  bvcoeff_t coeff;
} bvmlist_t;

// block size for list store
#define BVMBANK_SIZE 64

/*
 * Buffer for computation
 * - nterms = number of monomials (excluding start/end markers)
 * - size = number of bits in the expression
 *   all coefficients and variables are assumed to be of that size.
 * - width = size of the coefficients in words (i.e., width = ceil(size/32))
 *   if width <= 2, they are stored directly as 64bit numbers
 *   if width > 2, coefficients are stored as bvarith_constants.
 * - list = monomial list with start and end markers.
 * - manager = variable manager. 
 *   All variables in the buffer must be defined in manager.
 * - store = object store for allocating list elements
 *
 * manager and store are set by calling init
 * size, width, and list are initialized by calling prepare
 */
typedef struct {
  int32_t nterms;
  uint32_t size;
  uint32_t width;
  bvmlist_t *list;
  object_store_t *store;
  bv_var_manager_t *manager;
} bvarith_buffer_t;


/*
 * Maximal number of terms in a polynomial
 */
#define MAX_BVPOLY_SIZE (((UINT32_MAX-sizeof(bvarith_expr_t))/sizeof(bvmono_t))-1)


/*
 * Initialize a list store 
 */
extern void init_bvmlist_store(object_store_t *s);

/*
 * Delete store s
 */
extern void delete_bvmlist_store(object_store_t *s);

/*
 * Initialize buffer b with given manager and store
 */
extern void init_bvarith_buffer(bvarith_buffer_t *b, bv_var_manager_t *m, object_store_t *s);

/*
 * Delete buffer b
 */
extern void delete_bvarith_buffer(bvarith_buffer_t *b);

/*
 * Prepare b to store a polynomial of n bits (0 polynomial is stored in b)
 * Can also be used to reset b to 0.
 */
extern void bvarith_buffer_prepare(bvarith_buffer_t *b, uint32_t n);

/*
 * Normalize buffer b: reduce coefficients modulo 2^size
 * and remove monomials with zero coefficients.
 */
extern void bvarith_buffer_normalize(bvarith_buffer_t *b);

/*
 * Construct a bvarith_term object from b
 * - b must be normalized
 */
extern bvarith_expr_t *bvarith_buffer_get_expr(bvarith_buffer_t *b);

/*
 * Check whether b is a constant polynomial.
 * - b must be normalized.
 */
extern bool bvarith_buffer_is_constant(bvarith_buffer_t *b);

/*
 * Read constant stored in b when b->size <= 64, and reset b
 * - b must be normalized and a constant polynomial
 */
extern uint64_t bvarith_buffer_get_constant64(bvarith_buffer_t *b);

/*
 * Read constant stored in b when b->size > 64, and reset b.
 * - b must be normalized and a constant polynomial
 * - the returned constant has bitsize equal to b->size 
 *   (i.e., k = ceil(b->size/32) words).
 */
extern uint32_t *bvarith_buffer_get_constant(bvarith_buffer_t *b);

/*
 * Copy constant stored in b into c, then reset b
 * - b must be normalized and a constant polynomial
 * - the returned constant has bitsize equal to b->size 
 */
extern void bvarith_buffer_copy_constant(bvarith_buffer_t *b, bvconstant_t *c);


/*
 * Check whether b is reduced to a single variable x
 * - b must be normalized
 */
extern bool bvarith_buffer_is_variable(bvarith_buffer_t *b);


/*
 * Get the first variable of b.
 */
static inline bv_var_t bvarith_buffer_first_var(bvarith_buffer_t *b) {
  return b->list->next->var;
}

/*
 * Hash of polynomial in b 
 * b must be normalized.
 */
extern uint32_t bvarith_buffer_hash(bvarith_buffer_t *b);


/*
 * Hash of expression e
 */
extern uint32_t bvarith_expr_hash(bvarith_expr_t *e);


/*
 * Degree of an expression: m must be the variable manager
 * for all variables in p. return 0 if p == 0.
 */
extern int32_t bvarith_expr_degree(bvarith_expr_t *p, bv_var_manager_t *m);


/*
 * Degree of the expression in buffer.
 */
extern int32_t bvarith_buffer_degree(bvarith_buffer_t *b);


/*
 * Store primitive bv-variables of p in u
 */
extern void bvarith_expr_get_vars(bvarith_expr_t *p, bv_var_manager_t *m, ivector_t *u);


/*
 * Store terms attached to p's primitive variables in u
 */
extern void bvarith_expr_get_terms(bvarith_expr_t *p, bv_var_manager_t *m, ivector_t *u);



/*
 * Check whether e and b are equal. b must be normalized.
 */
extern bool bvarith_buffer_equal_expr(bvarith_buffer_t *b, bvarith_expr_t *e);

/*
 * Check whether b and b1 are equal. Both must be normalized.
 */
extern bool bvarith_buffer_equal_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1);

/*
 * Check whether e1 and e2 are equal. Both must be normalized.
 */
extern bool bvarith_expr_equal_expr(bvarith_expr_t *e1, bvarith_expr_t *e2);

/*
 * Check for trivial disequality: return true if (e1 - e2) is a non-zero constant
 * bitvector.
 */
extern bool bvarith_must_disequal_expr(bvarith_expr_t *e1, bvarith_expr_t *e2);




/*
 * Arithmetic operations
 */

// assign b to the constant 1 or -1 on n bits
extern void bvarith_buffer_set_one(bvarith_buffer_t *b);
extern void bvarith_buffer_set_minus_one(bvarith_buffer_t *b);

extern void bvarith_buffer_negate(bvarith_buffer_t *b);

extern void bvarith_buffer_add_mono(bvarith_buffer_t *b, bv_var_t v, uint32_t *a);
extern void bvarith_buffer_sub_mono(bvarith_buffer_t *b, bv_var_t v, uint32_t *a);

extern void bvarith_buffer_add_var(bvarith_buffer_t *b, bv_var_t v);
extern void bvarith_buffer_sub_var(bvarith_buffer_t *b, bv_var_t v);
extern void bvarith_buffer_mul_var(bvarith_buffer_t *b, bv_var_t v);

extern void bvarith_buffer_add_const(bvarith_buffer_t *b, uint32_t *a);
extern void bvarith_buffer_sub_const(bvarith_buffer_t *b, uint32_t *a);
extern void bvarith_buffer_mul_const(bvarith_buffer_t *b, uint32_t *a);

// p1 and p2 must be normalized.
extern void bvarith_buffer_add_expr(bvarith_buffer_t *b, bvarith_expr_t *p1);
extern void bvarith_buffer_sub_expr(bvarith_buffer_t *b, bvarith_expr_t *p1);
extern void bvarith_buffer_mul_expr(bvarith_buffer_t *b, bvarith_expr_t *p1);

// b1 and b2 must be distinct from b.
extern void bvarith_buffer_add_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1);
extern void bvarith_buffer_sub_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1);
extern void bvarith_buffer_mul_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1);

extern void bvarith_buffer_square(bvarith_buffer_t *b);


/*
 * Helper functions for subsitutions and related constructs.
 * - these functions correspond to addmul/submul
 * - they add a * v * p to a buffer q
 *   where a is a constant, v a variable, p a bvbuffer or bvarith_expr 
 *   (p and q must be distinct if both are buffers).
 * - if v = const_idx, this adds a * p to q
 *
 * The functions exist in two forms depending on the bitsize of a (and p and q):
 * - for bit sizes up to 64, a is a 64bit unsigned integer (narrow functions)
 * - for larger bitsizes, a is a pointer to an array of k, 32bit words where
 *   k = ceil(bitsize/32).
 */

extern void wide_buffer_add_mono_times_expr(bvarith_buffer_t *q, bvarith_expr_t *p, bv_var_t v, uint32_t *a);
extern void wide_buffer_add_mono_times_buffer(bvarith_buffer_t *q, bvarith_buffer_t *p, bv_var_t v, uint32_t *a);

extern void narrow_buffer_add_mono_times_expr(bvarith_buffer_t *q, bvarith_expr_t *p, bv_var_t v, uint64_t a);
extern void narrow_buffer_add_mono_times_buffer(bvarith_buffer_t *q, bvarith_buffer_t *p, bv_var_t v, uint64_t a);

#endif
