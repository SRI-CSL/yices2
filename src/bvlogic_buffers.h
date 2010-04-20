/*
 * BUFFERS FOR BITVECTORS REPRESENTED AS ARRAYS OF BOOLEAN TERMS
 */

/*
 * This representation supports logical operations such as
 * bvand, bvor, bvxor, etc. and structural operations such as 
 * shift, rotate, concat, bvextract, etc.
 *
 * Each bit is represented as a node in an OR/XOR DAG (cf. bit_expr)
 */

#ifndef __BVLOGIC_BUFFERS_H
#define __BVLOGIC_BUFFERS_H

#include <stdint.h>
#include <stdbool.h>

#include "bv_constants.h"
#include "bit_expr.h"


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
 * Check wether all bits in b are equal to term 'bit'
 * - bit must be a valid bit expression
 */
// TODO: remove this function? It doesn't seem to be used anywhere
extern bool bvlogic_buffer_allbits_equal(bvlogic_buffer_t *b, bit_t bit);





/*
 * ASSIGNMENTS
 */

/*
 * In all operations:
 * - n = number of bits in the operand
 * - n must be positive.
 *
 * set_constant64: copy the n lower order bits of an unsigned 64bit integer c
 * set_constant: copy the n lower order bits of a constant stored in an array 
 *               of 32bit words (cf. bv_constant)
 * set_bitarray: copy a[0] ... a[n-1] into b
 * set_allbits: set all bits of b equal to bit
 * set_bv: store the expression (select v 0) ... (select v n-1) into b
 */
extern void bvlogic_buffer_set_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c);
extern void bvlogic_buffer_set_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_set_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);
extern void bvlogic_buffer_set_allbits(bvlogic_buffer_t *b, uint32_t n, bit_t bit);
extern void bvlogic_buffer_set_bv(bvlogic_buffer_t *b, uint32_t n, int32_t v);


/*
 * BITWISE BOOLEAN OPERATIONS
 *
 * Same conventions as in the assignment operations,
 * - n = number of bits in the operands: n must be positive and equal to 
 *   b's current bitsize.
 */
extern void bvlogic_buffer_not(bvlogic_buffer_t *b);

extern void bvlogic_buffer_and_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c);
extern void bvlogic_buffer_or_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c);
extern void bvlogic_buffer_xor_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c);

extern void bvlogic_buffer_and_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_or_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_xor_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);

extern void bvlogic_buffer_and_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);
extern void bvlogic_buffer_or_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);
extern void bvlogic_buffer_xor_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);

extern void bvlogic_buffer_and_bv(bvlogic_buffer_t *b, uint32_t n, int32_t v);
extern void bvlogic_buffer_or_bv(bvlogic_buffer_t *b, uint32_t n, int32_t v);
extern void bvlogic_buffer_xor_bv(bvlogic_buffer_t *b, uint32_t n, int32_t v);




/*
 * CONCATENATION
 *
 * left/right refer to b written in big-endian form: (b[n-1] ... b[0])
 * if v = v[m-1] ... v[0] is the added to b, then 
 * - concat_left: v[m-1]...v[0] is added to the left of  b[n-1]
 * - concat_right: v[m-1]...v[0] is added to the right of  b[0]
 */
extern void bvlogic_buffer_concat_left_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c);
extern void bvlogic_buffer_concat_right_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c);

extern void bvlogic_buffer_concat_left_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_concat_right_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);

extern void bvlogic_buffer_concat_left_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);
extern void bvlogic_buffer_concat_right_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);

extern void bvlogic_buffer_concat_left_bv(bvlogic_buffer_t *b, uint32_t n, int32_t v);
extern void bvlogic_buffer_concat_right_bv(bvlogic_buffer_t *b, uint32_t n, int32_t v);


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
 *
 * left/right refer to b written in bigendian form, that is, b[n-1] ... b[0]
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
 * EXTRACTION
 *
 * replace b[0...n-1] by b[start ... end]. 
 * require 0 <= start <= end <= n-1
 */
extern void bvlogic_buffer_extract_subvector(bvlogic_buffer_t *b, uint32_t start, uint32_t end);



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

extern void bvlogic_buffer_comp_constant64(bvlogic_buffer_t *b, uint32_t n, uint64_t c);
extern void bvlogic_buffer_comp_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_comp_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);
extern void bvlogic_buffer_comp_bv(bvlogic_buffer_t *b, uint32_t n, int32_t v);




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
 * The functions return true and store b + c * a into b if the 
 * conversion is successful. They return false otherwise. 
 */
extern bool bvlogic_buffer_addmul_bitarray64(bvlogic_buffer_t *b, uint32_t n, bit_t *a, uint64_t c);
extern bool bvlogic_buffer_addmul_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a, uint32_t *c);




#endif /* __BVLOGIC_BUFFERS_H */
