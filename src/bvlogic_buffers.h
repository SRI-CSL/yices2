/*
 * BUFFERS FOR BITVECTORS REPRESENTED AS ARRAYS OF BOOLEAN TERMS
 */

/*
 * This representation supports logical operations such as
 * bvand, bvor, bvxor, etc. and structural operations such as 
 * shift, rotate, concat, bvextract, etc.
 */

#ifndef __BVLOGIC_BUFFERS_H
#define __BVLOGIC_BUFFERS_H

#include <stdint.h>
#include <stdbool.h>

#include "bv_constants.h"
#include "terms.h"



/*
 * Buffer = resizable array of boolean terms
 * - size = size of the array
 * - bitsize = number of bits used
 * - bit[0] = low-order bit
 *   ..
 *   bit[bitsize - 1] = high order bit
 * - terms = the corresponding term table
 */
typedef struct bvlogic_buffer_s {
  uint32_t bitsize;
  uint32_t size;
  term_t *bit;
  term_table_t *terms;
} bvlogic_buffer_t;



/*
 * Initial size and maximal size.
 */
#define BVLOGIC_BUFFER_INITIAL_SIZE 64
#define BVLOGIC_BUFFER_MAX_SIZE (UINT32_MAX/sizeof(term_t))



/*
 * INITIALIZATION/DELETION/RESET
 */

/*
 * Initialize buffer b
 * - terms = the attached term table
 * - b is empty
 */
extern void init_bvlogic_buffer(bvlogic_buffer_t *b, term_table_t *terms);

/*
 * Delete buffer b
 */
extern void delete_bvlogic_buffer(bvlogic_buffer_t *b);


/*
 * Clear b: set it to the empty vector
 */
static inline void bvlogic_buffer_clear(bvlogic_buffer_t *b) {
  b->bitsize = 0;
}

 

/*
 * TESTS
 */

/*
 * Check whether b is empty
 */
static inline bool bvlogic_buffer_is_empty(bvlogic_buffer_t *b) {
  return b->bitsize == 0;
}


/*
 * Check whether the bitvector stored in b is constant.
 */
extern bool bvlogic_buffer_is_constant(bvlogic_buffer_t *b);


/*
 * Convert constant in b to a 64bit integer and clear b.
 * - b->bitsize must be between 1 and 64
 */
extern uint64_t bvlogic_buffer_get_constant64(bvlogic_buffer_t *b);


/*
 * Copy constant stored in b into c, then reset b
 * - b must be a constant.
 */
extern void bvlogic_buffer_get_constant(bvlogic_buffer_t *b, bvconstant_t *c);


/*
 * Check wether all bits in b are equal to term 'bit'
 * - bit must be a valid boolean term
 */
extern bool bvlogic_buffer_allbits_equal(bvlogic_buffer_t *b, term_t bit);




/*
 * CONVERSION TO A TERM
 */

/*
 * Convert b to a bitvector term:
 * - build a bitvector constant if that's possible
 * - apply the conversion [b0 ... b_{n-1}] --> t if 
 *   b_i = (bit i t) and t has bitsize n
 * - otherwise build a bitarray term in the table attached to b.
 */
extern term_t bvlogic_buffer_get_term(bvlogic_buffer_t *b);



/*
 * ASSIGNMENT OPERATIONS
 *
 * For operations that use a term t: t must be a bit-vector term defined in
 * the b->terms, and t must have the same bitsize as b.
 *
 * For all the other operations: 
 * - n = number of bits in the operand (n must be equal to b's bitsize).
 * - the array a used as operand must be an array of n boolean terms.
 */
extern void bvlogic_buffer_set_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_set_bitarray(bvlogic_buffer_t *b, uint32_t n, term_t *a);
extern void bvlogic_buffer_set_allbits(bvlogic_buffer_t *b, uint32_t n, term_t bit);
extern void bvlogic_buffer_set_term(bvlogic_buffer_t *b, term_t t);


/*
 * BITWISE OPERATIONS
 */
extern void bvlogic_buffer_not(bvlogic_buffer_t *b);

extern void bvlogic_buffer_and_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_or_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_xor_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);

extern void bvlogic_buffer_and_bitarray(bvlogic_buffer_t *b, uint32_t n, term_t *a);
extern void bvlogic_buffer_or_bitarray(bvlogic_buffer_t *b, uint32_t n, term_t *a);
extern void bvlogic_buffer_xor_bitarray(bvlogic_buffer_t *b, uint32_t n, term_t *a);

extern void bvlogic_buffer_and_term(bvlogic_buffer_t *b, term_t t);
extern void bvlogic_buffer_or_term(bvlogic_buffer_t *b, term_t t);
extern void bvlogic_buffer_xor_term(bvlogic_buffer_t *b, term_t t);



/*
 * SHIFT AND ROTATE
 */

/*
 * left/right refer to b written in bigendian form, that is, b[n-1] ... b[0]
 */
extern void bvlogic_buffer_shift_left(bvlogic_buffer_t *b, uint32_t k, term_t padding);
extern void bvlogic_buffer_shift_right(bvlogic_buffer_t *b, uint32_t k, term_t padding);
extern void bvlogic_buffer_ashift_right(bvlogic_buffer_t *b, uint32_t k);
extern void bvlogic_buffer_rotate_left(bvlogic_buffer_t *b, uint32_t k);
extern void bvlogic_buffer_rotate_right(bvlogic_buffer_t *b, uint32_t k);

static inline void bvlogic_buffer_shift_left0(bvlogic_buffer_t *b, uint32_t k) {
  bvlogic_buffer_shift_left(b, k, false_term);
}

static inline void bvlogic_buffer_shift_left1(bvlogic_buffer_t *b, uint32_t k) {
  bvlogic_buffer_shift_left(b, k, true_term);
}

static inline void bvlogic_buffer_shift_right0(bvlogic_buffer_t *b, uint32_t k) {
  bvlogic_buffer_shift_right(b, k, false_term);
}

static inline void bvlogic_buffer_shift_right1(bvlogic_buffer_t *b, uint32_t k) {
  bvlogic_buffer_shift_right(b, k, true_term);
}


/*
 * EXTRACT
 * 
 * replace b[0...n-1] by b[start ... end]. 
 * require 0 <= start <= end <= n-1
 */
extern void bvlogic_buffer_extract_subvector(bvlogic_buffer_t *b, uint32_t start, uint32_t end);


/*
 * CONCATENATION
 *
 * left/right refer to b written in bigendian form: (b[n-1] ... b[0])
 * if v = v[m-1] ... v[0] is the added to b, then 
 * - concat_left: v[m-1]...v[0] is added to the left of  b[n-1]
 * - concat_right: v[m-1]...v[0] is added to the right of  b[0]
 */
extern void bvlogic_buffer_concat_left_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_concat_right_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);

extern void bvlogic_buffer_concat_left_bitarray(bvlogic_buffer_t *b, uint32_t n, term_t *a);
extern void bvlogic_buffer_concat_right_bitarray(bvlogic_buffer_t *b, uint32_t n, term_t *a);

extern void bvlogic_buffer_concat_left_term(bvlogic_buffer_t *b, term_t t);
extern void bvlogic_buffer_concat_right_term(bvlogic_buffer_t *b, term_t t);


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
 * Sign-extend: extend b to an n-bit vector by padding high-order bits with 0 
 * - b must have positive bitsize (p > 0)
 * - we must have p <= n
 */
extern void bvlogic_buffer_zero_extend(bvlogic_buffer_t *b, uint32_t n);




/*
 * REDUCTION:
 * - all compute a bitvector of size 1 from their arguments
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

extern void bvlogic_buffer_comp_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_comp_bitarray(bvlogic_buffer_t *b, uint32_t n, term_t *a);
extern void bvlogic_buffer_comp_term(bvlogic_buffer_t *b, term_t t);



/*
 * CONVERSION OF ADDITION AND PRODUCT TO BV-SHIFT AND BV-OR
 */

/*
 * Attempt to convert b + c * a into (bv-or b (shift-left a k))
 * - c is a bitvector constant of n bits
 * - a is a bit array of n bits
 * The conversion works if c is a power of 2 (then k = log_2 c)
 * and if for every index i, we have b[i] == ff or a[i+k] == ff.
 *
 * The function returns true and store b + c * a into b if the 
 * conversion is successful. It returns false otherwise. 
 */
extern bool bvlogic_buffer_addmul_bitarray(bvlogic_buffer_t *b, uint32_t n, term_t *a, uint32_t *c);




#endif /* __BVLOGIC_BUFFERS_H */
