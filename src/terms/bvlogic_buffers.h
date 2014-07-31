/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */


/*
 * BUFFERS FOR BITVECTORS REPRESENTED AS ARRAYS OF BOOLEAN TERMS
 */

/*
 * This representation supports logical operations such as
 * bvand, bvor, bvxor, etc. and structural operations such as
 * shift, rotate, concat, bvextract, etc.
 *
 * Each bit is represented as a node in an OR/XOR DAG (cf. bit_expr).
 *
 * IMPORTANT
 * ---------
 * For proper garbage collection of the node table, we want
 * to ensure that the node table's reference counter is equal to
 * the number of non-empty bvlogic_buffers. This is done in this
 * module by calling node_table_incref/node_table_decref whenever
 * the size of a buffer b becomes zero or nonzero.
 *
 * But, we don't do any checking when delete_bvlogic_buffer is called.
 * If a buffer b is deleted and the node table keeps being used, it's
 * important to call bvlogic_buffer_clear first.
 */

#ifndef __BVLOGIC_BUFFERS_H
#define __BVLOGIC_BUFFERS_H

#include <stdint.h>
#include <stdbool.h>

#include "terms/bv_constants.h"
#include "terms/bit_expr.h"
#include "terms/terms.h"


/*
 * Buffer = resizable array of boolean terms
 * - size = size of the array
 * - bitsize = number of bits used
 * - bit[0] = low-order bit
 *   ..
 *   bit[bitsize - 1] = high order bit
 * - terms = the corresponding term table
 * - nodes = the DAG table
 */
typedef struct bvlogic_buffer_s {
  uint32_t bitsize;
  uint32_t size;
  bit_t *bit;
  node_table_t *nodes;
} bvlogic_buffer_t;



/*
 * Initial size and maximal size.
 */
#define BVLOGIC_BUFFER_INITIAL_SIZE 64
#define BVLOGIC_BUFFER_MAX_SIZE (UINT32_MAX/sizeof(bit_t))



/*
 * INITIALIZATION/DELETION/RESET
 */

/*
 * Initialize buffer b
 * - nodes = attached node table
 * - b is initially empty
 */
extern void init_bvlogic_buffer(bvlogic_buffer_t *b, node_table_t *nodes);

/*
 * Delete buffer b.
 *
 * NOTE: call bvlogic_buffer_clear first if the node table keeps
 * being used after b is deleted.
 */
extern void delete_bvlogic_buffer(bvlogic_buffer_t *b);


/*
 * Clear b: set it to the empty vector (also decrement b's
 * node table reference counter if b->bitsize was positive).
 */
extern void bvlogic_buffer_clear(bvlogic_buffer_t *b);



/*
 * TEST A BUFFER'S CONTENT
 */

/*
 * Check whether b is empty
 */
static inline bool bvlogic_buffer_is_empty(bvlogic_buffer_t *b) {
  return b->bitsize == 0;
}


/*
 * Get the number of bits
 */
static inline uint32_t bvlogic_buffer_bitsize(bvlogic_buffer_t *b) {
  return b->bitsize;
}


/*
 * Check whether the bitvector stored in b is constant.
 */
extern bool bvlogic_buffer_is_constant(bvlogic_buffer_t *b);


/*
 * Convert constant in b to a 64bit integer.
 * - b->bitsize must be between 1 and 64 and b must be constant
 * - the returned value is padded with 0 if n < 64.
 */
extern uint64_t bvlogic_buffer_get_constant64(bvlogic_buffer_t *b);


/*
 * Copy constant stored in b into c
 * - b must be a constant.
 */
extern void bvlogic_buffer_get_constant(bvlogic_buffer_t *b, bvconstant_t *c);


/*
 * Check whether b is of the form (sel 0 x) ... (sel k-1 x)
 * - if so return x
 * - otherwise return -1
 */
extern int32_t bvlogic_buffer_get_var(bvlogic_buffer_t *b);


/*
 * Check wether all bits in b are equal to term 'bit'
 * - bit must be a valid bit expression
 */
// TODO: remove this function? It doesn't seem to be used anywhere
extern bool bvlogic_buffer_allbits_equal(bvlogic_buffer_t *b, bit_t bit);





/*
 * ASSIGNMENT OPERATIONS
 */

/*
 * In all operations:
 * - n = number of bits in the operand (n must be positive).
 *
 * set_constant64: copy the n lower order bits of an unsigned 64bit integer c
 * set_constant: copy the n lower order bits of a constant stored in an array
 *               of 32bit words (cf. bv_constant)
 * set_bitarray: copy a[0] ... a[n-1] into b
 * set_allbits: set all bits of b equal to bit
 */
extern void bvlogic_buffer_set_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c);
extern void bvlogic_buffer_set_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_set_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);
extern void bvlogic_buffer_set_allbits(bvlogic_buffer_t *b, uint32_t n, bit_t bit);


/*
 * Copy term t into b:
 * - t must be a bitvector term defined in 'table'
 */
extern void bvlogic_buffer_set_term(bvlogic_buffer_t *b, term_table_t *table, term_t t);


/*
 * Initialize b with n boolean terms: a[0] ... a[n-1]
 * - n must be positive
 * - each element of array a must be a boolean term defined in table
 * - a[0] = low order bit
 *   a[n] = high order bit
 */
extern void bvlogic_buffer_set_term_array(bvlogic_buffer_t *b, term_table_t *table, uint32_t n, const term_t *a);


/*
 * Set the k low order bits of b to 1, and the rest to 0
 * (i.e., store 2^k - 1)
 * - n = number of bits
 * - n must be positive and k must be between 0 and n-1
 */
extern void bvlogic_buffer_set_low_mask(bvlogic_buffer_t *b, uint32_t k, uint32_t n);


/*
 * SLICE ASSIGNMENT
 */

/*
 * Given a bitvector u of n bits, the following functions store
 * bits[i ... j] of u into b.
 * - i and j must satisfy 0 <= i <= j < n.
 *
 * The parameters c, a, t are as in the assignment operations above.
 */
extern void bvlogic_buffer_set_slice_constant64(bvlogic_buffer_t *b, uint32_t i, uint32_t j, uint64_t c);
extern void bvlogic_buffer_set_slice_constant(bvlogic_buffer_t *b, uint32_t i, uint32_t j, uint32_t *c);
extern void bvlogic_buffer_set_slice_bitarray(bvlogic_buffer_t *b, uint32_t i, uint32_t j, bit_t *a);
extern void bvlogic_buffer_set_slice_term_array(bvlogic_buffer_t *b, term_table_t *table, uint32_t i, uint32_t j, term_t *a);

extern void bvlogic_buffer_set_slice_term(bvlogic_buffer_t *b, term_table_t *table, uint32_t i, uint32_t j, term_t t);



/*
 * BITWISE BOOLEAN OPERATIONS
 */

/*
 * Negate all the bits
 */
extern void bvlogic_buffer_not(bvlogic_buffer_t *b);

/*
 * Binary operations:
 * - n = number of bits in the operands. n must be positive and equal to
 *   b's current bitsize.
 */
extern void bvlogic_buffer_and_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c);
extern void bvlogic_buffer_or_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c);
extern void bvlogic_buffer_xor_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c);

extern void bvlogic_buffer_and_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_or_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_xor_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);

extern void bvlogic_buffer_and_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);
extern void bvlogic_buffer_or_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);
extern void bvlogic_buffer_xor_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);


/*
 * Using a term operand:
 * - t must be a valid bitvector term in table and must have the same bitsize as b.
 */
extern void bvlogic_buffer_and_term(bvlogic_buffer_t *b, term_table_t *table, term_t t);
extern void bvlogic_buffer_or_term(bvlogic_buffer_t *b, term_table_t *table, term_t t);
extern void bvlogic_buffer_xor_term(bvlogic_buffer_t *b, term_table_t *table, term_t t);



/*
 * CONCATENATION
 */

/*
 * Left/right refer to b written in big-endian form: (b[n-1] ... b[0])
 * if v = v[m-1] ... v[0] is added to b, then
 * - concat_left: v[m-1]...v[0] is added to the left of  b[n-1]
 * - concat_right: v[m-1]...v[0] is added to the right of  b[0]
 */
extern void bvlogic_buffer_concat_left_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c);
extern void bvlogic_buffer_concat_right_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c);

extern void bvlogic_buffer_concat_left_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_concat_right_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);

extern void bvlogic_buffer_concat_left_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);
extern void bvlogic_buffer_concat_right_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);


/*
 * Term concatenation:
 * - t must be a valid bitvector term in table
 */
extern void bvlogic_buffer_concat_left_term(bvlogic_buffer_t *b, term_table_t *table, term_t t);
extern void bvlogic_buffer_concat_right_term(bvlogic_buffer_t *b, term_table_t *table, term_t t);


/*
 * Repeat concat: concatenate b with itself (make n copies)
 * - n must be positive.
 */
extern void bvlogic_buffer_repeat_concat(bvlogic_buffer_t *b, uint32_t n);


/*
 * Sign-extend: extend b to an n-bit vector by replicating the sign bit
 * - b must have positive bitsize (p > 0)
 * - we must have p <= n
 */
extern void bvlogic_buffer_sign_extend(bvlogic_buffer_t *b, uint32_t n);


/*
 * Zero-extend: extend b to an n-bit vector by padding high-order bits with 0
 * - b must have positive bitsize (p > 0)
 * - we must have p <= n
 */
extern void bvlogic_buffer_zero_extend(bvlogic_buffer_t *b, uint32_t n);






/*
 * SHIFT AND ROTATE
 */

/*
 * Left/right refer to b written in bigendian form, that is, b[n-1] ... b[0].
 */

/*
 * Shift left by k. replace low-order bits by padding.
 * - k must be between 0 and b->bitsize
 */
extern void bvlogic_buffer_shift_left(bvlogic_buffer_t *b, uint32_t k, bit_t padding);

static inline void bvlogic_buffer_shift_left0(bvlogic_buffer_t *b, uint32_t k) {
  bvlogic_buffer_shift_left(b, k, false_bit);
}

static inline void bvlogic_buffer_shift_left1(bvlogic_buffer_t *b, uint32_t k) {
  bvlogic_buffer_shift_left(b, k, true_bit);
}


/*
 * Shift right by k. Replace high-order bits by padding.
 * - k must be between 0 and b->bitsize.
 */
extern void bvlogic_buffer_shift_right(bvlogic_buffer_t *b, uint32_t k, bit_t padding);

static inline void bvlogic_buffer_shift_right0(bvlogic_buffer_t *b, uint32_t k) {
  bvlogic_buffer_shift_right(b, k, false_bit);
}

static inline void bvlogic_buffer_shift_right1(bvlogic_buffer_t *b, uint32_t k) {
  bvlogic_buffer_shift_right(b, k, true_bit);
}


/*
 * Arithmetic shift: k must be between 0 and b->bitsize
 */
extern void bvlogic_buffer_ashift_right(bvlogic_buffer_t *b, uint32_t k);


/*
 * Left rotation by k bits.
 * - k must be between 0 and b->bitsize - 1
 */
extern void bvlogic_buffer_rotate_left(bvlogic_buffer_t *b, uint32_t k);


/*
 * Rotation to the right by k bits.
 * - k must be between 0 and b->bitsize - 1
 */
extern void bvlogic_buffer_rotate_right(bvlogic_buffer_t *b, uint32_t k);



/*
 * Logical shift left or right:
 * - the shift amount is given by bitvector constant c of n bits
 * - c is converted to an integer k
 * - if k is bigger than b's bitsize then all bits of b are cleared
 *   if k is nonzero, then b is shifted by k bits
 *   if k is zero, b is unchanged
 */
extern void bvlogic_buffer_shl_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c);
extern void bvlogic_buffer_shl_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);

extern void bvlogic_buffer_lshr_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c);
extern void bvlogic_buffer_lshr_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);


/*
 * Arithmetic shift right
 * - the shift amount is given by bitvector constant c of n bits
 * - b must not be empty
 * - c is converted to an integer k
 * - if k is larger than b's bitsize then the sign bit of b is copied
 *   in all bits of b.
 */
extern void bvlogic_buffer_ashr_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c);
extern void bvlogic_buffer_ashr_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);





/*
 * EXTRACTION
 */

/*
 * replace b[0...n-1] by b[start ... end].
 * require 0 <= start <= end <= n-1
 */
extern void bvlogic_buffer_extract_subvector(bvlogic_buffer_t *b, uint32_t start, uint32_t end);



/*
 * REDUCTION
 */

/*
 * All functions compute a bitvector of size 1 from their arguments
 * - redand b: compute (and b[0] ... b[n-1]) and store it into b[0]
 * - redor b:  compute (or b[0] ... b[n-1]) and store that into b[0]
 * - comp b a: compute (and (bit-eq a[0] b[0]) ... (bit-eq a[n-1] b[n-1]))
 *             and store that into b[0]
 *
 * So we get (redand b) == 0b1 iff all bits of b are true
 *           (redand b) == 0b1 iff at least one bit of b is true
 *           (comp b a) == 0b1 iff (a == b)
 */
extern void bvlogic_buffer_redand(bvlogic_buffer_t *b);
extern void bvlogic_buffer_redor(bvlogic_buffer_t *b);

extern void bvlogic_buffer_comp_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c);
extern void bvlogic_buffer_comp_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_comp_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);


/*
 * COMP reduction with a term t:
 * - t must be a valid bitvector term in table and must have the same bitsize as b
 */
extern void bvlogic_buffer_comp_term(bvlogic_buffer_t *b, term_table_t *table, term_t t);




/****************
 *  SHORT CUTS  *
 ***************/

/*
 * All operations that take an bitarray argument have a variant that
 * use a buffer b2.
 */
static inline void bvlogic_buffer_set_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b2) {
  assert(b != b2);
  bvlogic_buffer_set_bitarray(b, b2->bitsize, b2->bit);
}

static inline void bvlogic_buffer_set_slice_buffer(bvlogic_buffer_t *b, uint32_t i, uint32_t j, bvlogic_buffer_t *b2) {
  assert(b != b2);
  bvlogic_buffer_set_slice_bitarray(b, i, j, b2->bit);
}



static inline void bvlogic_buffer_and_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b2) {
  assert(b != b2);
  bvlogic_buffer_and_bitarray(b, b2->bitsize, b2->bit);
}

static inline void bvlogic_buffer_or_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b2) {
  assert(b != b2);
  bvlogic_buffer_or_bitarray(b, b2->bitsize, b2->bit);
}

static inline void bvlogic_buffer_xor_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b2) {
  assert(b != b2);
  bvlogic_buffer_xor_bitarray(b, b2->bitsize, b2->bit);
}

static inline void bvlogic_buffer_concat_left_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b2) {
  assert(b != b2);
  bvlogic_buffer_concat_left_bitarray(b, b2->bitsize, b2->bit);
}

static inline void bvlogic_buffer_concat_right_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b2) {
  assert(b != b2);
  bvlogic_buffer_concat_right_bitarray(b, b2->bitsize, b2->bit);
}

static inline void bvlogic_buffer_comp_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b2) {
  assert(b != b2);
  bvlogic_buffer_comp_bitarray(b, b2->bitsize, b2->bit);
}



#endif /* __BVLOGIC_BUFFERS_H */
