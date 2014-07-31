/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BUFFERS FOR OPERATIONS ON BIT-VECTOR POLYNOMIALS
 */

/*
 * Bitvector polynomials are sums of pairs <coeff, pp>
 * - the coeff is a bitvector constant
 * - pp is a power product (cf. power_products.h)
 * - all coefficients have the same bit-size
 * - the data structure in this module support arbitrary
 *   bit size; coefficients are pointers to 32bit words
 *   (cf. bv_constants.h).
 *
 * In normal form, polynomials have the following properties:
 * - the coefficients are all reduced modulo 2^n
 *   and are all non zero
 * - the monomials are stored in deg-lex order: lower degree
 *   monomials appear first; monomials of equal degree are
 *   sorted in lexicographic order.
 *
 * There's a limit on the coefficients' bitsize defined in
 * yices_limits.h (YICES_MAX_BVSIZE).
 */

#ifndef __BVARITH_BUFFERS_H
#define __BVARITH_BUFFERS_H

#include <stdint.h>
#include <assert.h>

#include "terms/bv_constants.h"
#include "utils/object_stores.h"
#include "terms/pprod_table.h"
#include "terms/bv_polynomials.h"


/*
 * A buffer stores a polynomial as a list of monomials
 * - list = list of pairs <coeff, pp> sorted in increasing order
 *   - coeff is a pointer to an array of 32bit words
 *   - pp is a power product
 * - the list contains an end marker (with pp = end_pp),
 *   which is always the last element in the list.
 * - some of the coefficients may be zero
 * - the normalize operation reduces all the coefficients modulo 2^n
 *   and remove the zero coefficients.
 *
 * Other components of a buffer:
 * - nterms = number of monomials in the list, excluding end marker.
 * - bitsize = size of the coefficients (number of bits).
 * - width = ceil(bitsize/32) = size of the coefficients in number words
 */

// element in a list of monomials
typedef struct bvmlist_s {
  struct bvmlist_s *next;
  uint32_t *coeff;
  pprod_t *prod;
} bvmlist_t;

// buffer
typedef struct bvarith_buffer_s {
  uint32_t nterms;        // length of the list (excluding the end marker)
  uint32_t bitsize;
  uint32_t width;
  bvmlist_t *list;        // start of the list
  object_store_t *store;  // for allocation of list elements
  pprod_table_t *ptbl;    // for creation of power products
} bvarith_buffer_t;


/*
 * Block size of an bvarith_buffer store
 */
#define BVMLIST_BANK_SIZE 64



/***********************
 * BUFFER  OPERATIONS  *
 **********************/

/*
 * Initialize store s for list elements
 */
extern void init_bvmlist_store(object_store_t *s);


/*
 * Delete store s: free all attached memory.
 * Must not be called unless all buffers with store s are deleted.
 */
extern void delete_bvmlist_store(object_store_t *s);


/*
 * Initialize buffer b to the zero polynomial
 * - ptbl = attached power product table
 * - s = attached store
 */
extern void init_bvarith_buffer(bvarith_buffer_t *b, pprod_table_t *ptbl, object_store_t *s);


/*
 * Delete b and free all attached memory
 */
extern void delete_bvarith_buffer(bvarith_buffer_t *b);


/*
 * Prepare b for a polynomial of n bits
 * - n must be positive and no more than YICES_MAX_BVSIZE
 * - this clears the current content of b  and
 *   sets b to the 0 polynomial of n bits
 */
extern void bvarith_buffer_prepare(bvarith_buffer_t *b, uint32_t n);


/*
 * Normalize b:
 * - reduce all coefficients modulo 2^bitsize
 * - remove monomials with a zero coefficient
 */
extern void bvarith_buffer_normalize(bvarith_buffer_t *b);


/*
 * Reset
 */
static inline void reset_bvarith_buffer(bvarith_buffer_t *b) {
  bvarith_buffer_prepare(b, 32);
}


/*************
 *  QUERIES  *
 ************/

/*
 * Size = number of terms.
 */
static inline uint32_t bvarith_buffer_size(bvarith_buffer_t *b) {
  return b->nterms;
}


/*
 * Bitsize
 */
static inline uint32_t bvarith_buffer_bitsize(bvarith_buffer_t *b) {
  return b->bitsize;
}


/*
 * Width = size of coefficients in 32bit words
 */
static inline uint32_t bvarith_buffer_width(bvarith_buffer_t *b) {
  return b->width;
}


/*
 * Check whether b is zero
 * - b must be normalized
 */
static inline bool bvarith_buffer_is_zero(bvarith_buffer_t *b) {
  return b->nterms == 0;
}


/*
 * Check whether b is constant
 * - b must be normalized
 */
extern bool bvarith_buffer_is_constant(bvarith_buffer_t *b);


/*
 * Read the constant term of b as a 64bit integer.
 * - b's bitsize must be between 1 and 64
 * - b must be normalized
 */
extern uint64_t bvarith_buffer_get_constant64(bvarith_buffer_t *b);


/*
 * Copy constant term of b into c.
 * - b must be normalized.
 * - the returned constant has bitsize equal to b->size.
 */
extern void bvarith_buffer_copy_constant(bvarith_buffer_t *b, bvconstant_t *c);


/*
 * Get the degree of polynomial in buffer b.
 * - b must be normalized
 * - returns 0 if b is zero
 */
extern uint32_t bvarith_buffer_degree(bvarith_buffer_t *b);


/*
 * Main term = maximal power product of b in the deg-lex ordering.
 * - b must be normalized and non zero
 */
extern pprod_t *bvarith_buffer_main_term(bvarith_buffer_t *b);


/*
 * Main monomial = monomial whose pp is the main term
 * - b must be normalized and non zero
 * - this returns the last element in b's monomial list
 */
extern bvmlist_t *bvarith_buffer_main_mono(bvarith_buffer_t *b);


/*
 * Check whether b1 and b2 are equal
 * - both must be normalized and use the same ptbl
 */
extern bool bvarith_buffer_equal(bvarith_buffer_t *b1, bvarith_buffer_t *b2);



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
 * For operations that have a bitvector constant a as an argument,
 * the constant a must have the same bitsize as b.
 */

/*
 * Assign the constant +1 or -1 to b.
 * This is extended to n bits where n = bitsize of b.
 */
extern void bvarith_buffer_set_one(bvarith_buffer_t *b);
extern void bvarith_buffer_set_minus_one(bvarith_buffer_t *b);


/*
 * Multiply b by -1
 */
extern void bvarith_buffer_negate(bvarith_buffer_t *b);


/*
 * Multiply b by constant a
 */
extern void bvarith_buffer_mul_const(bvarith_buffer_t *b, uint32_t *a);


/*
 * Multiply b by power product r
 */
extern void bvarith_buffer_mul_pp(bvarith_buffer_t *b, pprod_t *r);


/*
 * Multiply b by (- r)
 */
extern void bvarith_buffer_mul_negpp(bvarith_buffer_t *b, pprod_t *r);


/*
 * Multiply b by a * r
 */
extern void bvarith_buffer_mul_mono(bvarith_buffer_t *b, uint32_t *a, pprod_t *r);



/*
 * Add constant a to b
 */
extern void bvarith_buffer_add_const(bvarith_buffer_t *b, uint32_t *a);


/*
 * Add constant (-a) to b
 */
extern void bvarith_buffer_sub_const(bvarith_buffer_t *b, uint32_t *a);


/*
 * Add a * c to b
 */
extern void bvarith_buffer_add_const_times_const(bvarith_buffer_t *b, uint32_t *a, uint32_t *c);


/*
 * Subtract a * c to b
 */
extern void bvarith_buffer_sub_const_times_const(bvarith_buffer_t *b, uint32_t *a, uint32_t *c);


/*
 * Add r to b
 */
extern void bvarith_buffer_add_pp(bvarith_buffer_t *b, pprod_t *r);


/*
 * Add -r to b
 */
extern void bvarith_buffer_sub_pp(bvarith_buffer_t *b, pprod_t *r);


/*
 * Add a * r to b
 */
extern void bvarith_buffer_add_mono(bvarith_buffer_t *b, uint32_t *a, pprod_t *r);


/*
 * Add -a * r to b
 */
extern void bvarith_buffer_sub_mono(bvarith_buffer_t *b, uint32_t *a, pprod_t *r);


/*
 * Add a * c * r to b
 */
extern void bvarith_buffer_add_const_times_mono(bvarith_buffer_t *b, uint32_t *a, uint32_t *c, pprod_t *r);


/*
 * Add -a * c * r to b
 */
extern void bvarith_buffer_sub_const_times_mono(bvarith_buffer_t *b, uint32_t *a, uint32_t *c, pprod_t *r);



/*
 * Compute the square of b
 */
extern void bvarith_buffer_square(bvarith_buffer_t *b);




/************************************
 *  OPERATIONS WITH MONOMIAL LISTS  *
 ***********************************/

/*
 * In all operations, p1 and p2 must be lists of monomials built using the
 * same pprod_table as b. The coefficients in p1 and p2 must have the
 * same bitsize as in b. The monomial lists must be sorted and terminated
 * by the end marker.
 */

/*
 * Add p1 to b
 */
extern void bvarith_buffer_add_mlist(bvarith_buffer_t *b, bvmlist_t *p1);


/*
 * Add (-p1) to b
 */
extern void bvarith_buffer_sub_mlist(bvarith_buffer_t *b, bvmlist_t *p1);


/*
 * Add a * p1 to b
 */
extern void bvarith_buffer_add_const_times_mlist(bvarith_buffer_t *b, bvmlist_t *p1, uint32_t *a);


/*
 * Add (-a) * p1 to b
 */
extern void bvarith_buffer_sub_const_times_mlist(bvarith_buffer_t *b, bvmlist_t *p1, uint32_t *a);


/*
 * Add r * p1 to b
 */
extern void bvarith_buffer_add_pp_times_mlist(bvarith_buffer_t *b, bvmlist_t *p1, pprod_t *r);


/*
 * Add - r * p1 to b
 */
extern void bvarith_buffer_sub_pp_times_mlist(bvarith_buffer_t *b, bvmlist_t *p1, pprod_t *r);


/*
 * Add a * r * p1 to b
 */
extern void bvarith_buffer_add_mono_times_mlist(bvarith_buffer_t *b, bvmlist_t *p1, uint32_t *a, pprod_t *r);


/*
 * Add -a * r * p1 to b
 */
extern void bvarith_buffer_sub_mono_times_mlist(bvarith_buffer_t *b, bvmlist_t *p1, uint32_t *a, pprod_t *r);


/*
 * Multiply b by p1
 * - p1 must be disjoint from b
 */
extern void bvarith_buffer_mul_mlist(bvarith_buffer_t *b, bvmlist_t *p1);


/*
 * Multiply b by p1 ^ d
 * - use aux as an auxiliary buffer.
 * - aux must be distinct from b, but use the same power_product table
 */
extern void bvarith_buffer_mul_mlist_power(bvarith_buffer_t *b, bvmlist_t *p1, uint32_t d, bvarith_buffer_t *aux);


/*
 * Add p1 * p2 to b
 * - p1 and p2 must be disjoint from b (but p1 may be equal to p2)
 */
extern void bvarith_buffer_add_mlist_times_mlist(bvarith_buffer_t *b, bvmlist_t *p1, bvmlist_t *p2);


/*
 * Add - p1 * p2 to b
 * - p1 and p2 must be disjoint from b (but p1 may be equal to p2)
 */
extern void bvarith_buffer_sub_mlist_times_mlist(bvarith_buffer_t *b, bvmlist_t *p1, bvmlist_t *p2);


/*
 * Extract b's content as a list of monomials, then reset b to the zero polynomial
 * - b must be normalized
 */
extern bvmlist_t *bvarith_buffer_get_mlist(bvarith_buffer_t *b);


/*
 * Hash code for a list of monomials p:
 * - p must be sorted and terminated by the end marker
 * - all coefficients in p must be non-zero and normalized modulo 2^n
 */
extern uint32_t hash_bvmlist(bvmlist_t *p, uint32_t n);


/*
 * Test whether p1 and p2 are equal
 * - both lists must be sorted, and terminated by the end marker,
 *   and use the same pprod table.
 * - n = bitsize of p1 and p2
 */
extern bool equal_bvmlists(bvmlist_t *p1, bvmlist_t *p2, uint32_t n);


/*
 * Delete all monomials in *p
 * - store = the relevant monomial store (all monomials of p
 *   must have been allocated in store).
 * - n = number of bits in p
 */
extern void free_bvmlist(bvmlist_t *p, object_store_t *store, uint32_t n);


/************************************
 *  OPERATIONS WITH OTHER BUFFERS   *
 ***********************************/

/*
 * In all operations, b1 and b2 must be bvarith_buffers with the same ptbl and
 * the same bitsize as b.
 */

/*
 * Add b1 to b
 */
static inline void bvarith_buffer_add_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1) {
  assert(b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);
  bvarith_buffer_add_mlist(b, b1->list);
}


/*
 * Add (-b1) to b
 */
static inline void bvarith_buffer_sub_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1) {
  assert(b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);
  bvarith_buffer_sub_mlist(b, b1->list);
}


/*
 * Add a * b1 to b
 */
static inline void bvarith_buffer_add_const_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, uint32_t *a) {
  assert(b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);
  bvarith_buffer_add_const_times_mlist(b, b1->list, a);
}


/*
 * Add (-a) * b1 to b
 */
static inline void bvarith_buffer_sub_const_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, uint32_t *a) {
  assert(b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);
  bvarith_buffer_sub_const_times_mlist(b, b1->list, a);
}


/*
 * Add r * b1 to b
 */
static inline void bvarith_buffer_add_pp_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, pprod_t *r) {
  assert(b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);
  bvarith_buffer_add_pp_times_mlist(b, b1->list, r);
}


/*
 * Add - r * b1 to b
 */
static inline void bvarith_buffer_sub_pp_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, pprod_t *r) {
  assert(b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);
  bvarith_buffer_sub_pp_times_mlist(b, b1->list, r);
}


/*
 * Add a * r * b1 to b
 */
static inline void bvarith_buffer_add_mono_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, uint32_t *a, pprod_t *r) {
  assert(b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);
  bvarith_buffer_add_mono_times_mlist(b, b1->list, a, r);
}


/*
 * Add -a * r * b1 to b
 */
static inline void bvarith_buffer_sub_mono_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, uint32_t *a, pprod_t *r) {
  assert(b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);
  bvarith_buffer_sub_mono_times_mlist(b, b1->list, a, r);
}


/*
 * Multiply b by b1
 * - b1 must be different from b
 */
static inline void bvarith_buffer_mul_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1) {
  assert(b != b1 && b->ptbl == b1->ptbl && b->bitsize == b1->bitsize);
  bvarith_buffer_mul_mlist(b, b1->list);
}


/*
 * Multiply b by b1 ^ d
 * - use aux as an auxiliary buffer.
 * - aux must be distinct from b and b1, but use the same power_product table
 */
static inline void bvarith_buffer_mul_buffer_power(bvarith_buffer_t *b, bvarith_buffer_t *b1, uint32_t d, bvarith_buffer_t *aux) {
  bvarith_buffer_mul_mlist_power(b, b1->list, d, aux);
}


/*
 * Add b1 * b2 to b
 * - b1 and b2 must be disjoint from b (but b1 may be equal to b2)
 */
static inline void bvarith_buffer_add_buffer_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, bvarith_buffer_t *b2) {
  assert(b != b1 && b != b2 && b1->ptbl == b->ptbl && b2->ptbl == b->ptbl &&
         b->bitsize == b1->bitsize && b->bitsize == b2->bitsize);
  bvarith_buffer_add_mlist_times_mlist(b, b1->list, b2->list);
}


/*
 * Add - b1 * b2 to b
 * - b1 and b2 must be disjoint from b (but b1 may be equal to b2)
 */
static inline void bvarith_buffer_sub_buffer_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, bvarith_buffer_t *b2) {
  assert(b != b1 && b != b2 && b1->ptbl == b->ptbl && b2->ptbl == b->ptbl &&
         b->bitsize == b1->bitsize && b->bitsize == b2->bitsize);
  bvarith_buffer_sub_mlist_times_mlist(b, b1->list, b2->list);
}






/*******************************************
 *  OPERATIONS WITH POLYNOMIAL STRUCTURES  *
 ******************************************/

/*
 * A bit-vector polynomial is an array of monomials of the form
 * (coeff, index) where indices are signed integers. Operations
 * between buffers and polynomials require a conversion of
 * the integer indices used by monomials to power products used by buffers.
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
extern void bvarith_buffer_add_bvpoly(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp);


/*
 * Subtract poly from buffer b
 */
extern void bvarith_buffer_sub_bvpoly(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp);


/*
 * Add a * poly to buffer b
 */
extern void bvarith_buffer_add_const_times_bvpoly(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp, uint32_t *a);


/*
 * Subtract a * poly from b
 */
extern void bvarith_buffer_sub_const_times_bvpoly(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp, uint32_t *a);


/*
 * Add a * r * poly to b
 */
extern void bvarith_buffer_add_mono_times_bvpoly(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp, uint32_t *a, pprod_t *r);


/*
 * Add -a * r * poly to b
 */
extern void bvarith_buffer_sub_mono_times_bvpoly(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp, uint32_t *a, pprod_t *r);


/*
 * Multiply b by poly
 */
extern void bvarith_buffer_mul_bvpoly(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp);


/*
 * Multiply b by poly ^ d
 * - use aux as an auxiliary buffer (aux must be distinct from b)
 */
extern void bvarith_buffer_mul_bvpoly_power(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp, uint32_t d, bvarith_buffer_t *aux);




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
 * and the integer  index for power product r_i is v[i]. The last element v[n+1]
 * must be max_idx.
 *
 * The pair (b, v) defines then a bitvector polynomial
 * P(b, v) = a_1 v[1] + ... + a_n v[n],
 */

/*
 * Hash code for P(b, v).
 * This function is consistent with hash_bvpoly defined in bv_polynomials.c.
 * If P(b, v) = p0 then hash_bvarith_buffer(b, v) = hash_bvpoly(p0).
 */
extern uint32_t hash_bvarith_buffer(bvarith_buffer_t *b, int32_t *v);


/*
 * Check where P(b, v) is equal to p
 */
extern bool bvarith_buffer_equal_bvpoly(bvarith_buffer_t *b, int32_t *v, bvpoly_t *p);


/*
 * Build P(b, v) (i.e., convert b to a polynomial then reset b).
 * SIDE EFFECT: b is reset to the zero polynomial.
 */
extern bvpoly_t *bvarith_buffer_get_bvpoly(bvarith_buffer_t *b, int32_t *v);





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
static inline void bvarith_buffer_mul_var(bvarith_buffer_t *b, int32_t x) {
  bvarith_buffer_mul_pp(b, var_pp(x));
}


/*
 * Multiply b by (- x)
 */
static inline void bvarith_buffer_mul_negvar(bvarith_buffer_t *b, int32_t x) {
  bvarith_buffer_mul_negpp(b, var_pp(x));
}


/*
 * Multiply b by a * x
 */
static inline void bvarith_buffer_mul_varmono(bvarith_buffer_t *b, uint32_t *a, int32_t x) {
  bvarith_buffer_mul_mono(b, a, var_pp(x));
}


/*
 * Add x to b
 */
static inline void bvarith_buffer_add_var(bvarith_buffer_t *b, int32_t x) {
  bvarith_buffer_add_pp(b, var_pp(x));
}


/*
 * Add -x to b
 */
static inline void bvarith_buffer_sub_var(bvarith_buffer_t *b, int32_t x) {
  bvarith_buffer_sub_pp(b, var_pp(x));
}


/*
 * Add a * x to b
 */
static inline void bvarith_buffer_add_varmono(bvarith_buffer_t *b, uint32_t *a, int32_t x) {
  bvarith_buffer_add_mono(b, a, var_pp(x));
}


/*
 * Add -a * x to b
 */
static inline void bvarith_buffer_sub_varmono(bvarith_buffer_t *b, uint32_t *a, int32_t x) {
  bvarith_buffer_sub_mono(b, a, var_pp(x));
}


/*
 * Add x * b1 to b
 */
static inline void bvarith_buffer_add_var_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, int32_t x) {
  bvarith_buffer_add_pp_times_buffer(b, b1, var_pp(x));
}


/*
 * Add - x * b1 to b
 */
static inline void bvarith_buffer_sub_var_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, int32_t x) {
  bvarith_buffer_sub_pp_times_buffer(b, b1, var_pp(x));
}


/*
 * Add a * x * b1 to b
 */
static inline void
bvarith_buffer_add_varmono_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, uint32_t *a, int32_t x) {
  bvarith_buffer_add_mono_times_buffer(b, b1, a, var_pp(x));
}

/*
 * Add -a * x * b1 to b
 */
static inline void
bvarith_buffer_sub_varmono_times_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1, uint32_t *a, int32_t x) {
  bvarith_buffer_sub_mono_times_buffer(b, b1, a, var_pp(x));
}


/*
 * Add a * x * poly to b
 */
static inline void
bvarith_buffer_add_varmono_times_bvpoly(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp, uint32_t *a, int32_t x) {
  bvarith_buffer_add_mono_times_bvpoly(b, poly, pp, a, var_pp(x));
}


/*
 * Add -a * x * poly to b
 */
static inline void
bvarith_buffer_sub_varmono_times_bvpoly(bvarith_buffer_t *b, bvpoly_t *poly, pprod_t **pp, uint32_t *a, int32_t x) {
  bvarith_buffer_sub_mono_times_bvpoly(b, poly, pp, a, var_pp(x));
}



#endif /* __BVARITH_BUFFERS_H */
