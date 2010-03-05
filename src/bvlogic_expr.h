/*
 * Bit-vector logic expressions.
 *
 * Represented as arrays of bits: b[n-1] ... b[0]
 * where b[0] is the low order bit and b[n-1] is the high order bit
 */

#ifndef __BVLOGIC_EXPR_H
#define __BVLOGIC_EXPR_H

#include <stdint.h>
#include <stdbool.h>

#include "bit_expr.h"
#include "bv_constants.h"
#include "bitvector_variable_manager.h"
#include "int_vectors.h"


/*
 * Bit arrays.
 * bit[0] = low-order bit
 * bit[nbits-1] = high-order bit
 */
typedef struct {
  uint32_t nbits; // number of bits
  bit_t bit[0];   // array of bits, actual size = nbits
} bvlogic_expr_t;


/*
 * Buffer for computations: resizable vector of n bit expressions
 * - size = size of the array
 * - nbits = number of bits used
 * - manager = attached node table
 */
typedef struct {
  uint32_t nbits;
  uint32_t size;
  bit_t *bit;
  node_table_t *nodes;
} bvlogic_buffer_t;


/*
 * Initial size
 */
#define BVLOGIC_BUFFER_INITIAL_SIZE 64

/*
 * Maximal size
 */
#define BVLOGIC_BUFFER_MAX_SIZE (UINT32_MAX/8)


/*
 * Initialize buffer b
 * - nodes is the attached node table
 */
extern void init_bvlogic_buffer(bvlogic_buffer_t *b, node_table_t *nodes);

/*
 * Delete buffer b
 */
extern void delete_bvlogic_buffer(bvlogic_buffer_t *b);


/*
 * Clear b: set it to the empty vector
 */
extern void bvlogic_buffer_clear(bvlogic_buffer_t *b);

 
/*
 * Construct a bvlogic_expr object from b and clear b
 */
extern bvlogic_expr_t *bvlogic_buffer_get_expr(bvlogic_buffer_t *b);


/*
 * Hash of the bit array stored in b
 */
extern uint32_t bvlogic_buffer_hash(bvlogic_buffer_t *b);


/*
 * Hash of the bit array in e
 */
extern uint32_t bvlogic_expr_hash(bvlogic_expr_t *e);


/*
 * Equality tests
 */
extern bool bvlogic_buffer_equal_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);

static inline bool bvlogic_buffer_equal_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b1) {
  return bvlogic_buffer_equal_bitarray(b, b1->nbits, b1->bit);
}

static inline bool bvlogic_buffer_equal_expr(bvlogic_buffer_t *b, bvlogic_expr_t *e) {
  return bvlogic_buffer_equal_bitarray(b, e->nbits, e->bit);
}

extern bool bvlogic_expr_equal_expr(bvlogic_expr_t *e1, bvlogic_expr_t *e2);


/*
 * Check whether e1 and e2 must be disequal.
 */
extern bool bvlogic_must_disequal_expr(bvlogic_expr_t *e1, bvlogic_expr_t *e2);

/*
 * Check whether e and constant c must be disequal.
 * n = number of bits in c
 */
extern bool bvlogic_must_disequal_constant(bvlogic_expr_t *e1, uint32_t n, uint32_t *c);


/*
 * Check whether bitvector stored in b is constant.
 */
extern bool bvlogic_buffer_is_constant(bvlogic_buffer_t *b);


/*
 * Same thing for bitvector expression
 */
extern bool bvlogic_expr_is_constant(bvlogic_expr_t *e);


/*
 * Convert constant in b to a 64bit integer and clear b.
 */
extern uint64_t bvlogic_buffer_get_constant64(bvlogic_buffer_t *b);


/*
 * Allocate an array c and store contant of b in c, then clear b.
 * The returned array has the same bitsize as b and witdh k = ceil(bitsize/32).
 */
extern uint32_t *bvlogic_buffer_get_constant(bvlogic_buffer_t *b);


/*
 * Copy constant stored in b into c, then reset b
 * - b must be a constant.
 */
extern void bvlogic_buffer_copy_constant(bvlogic_buffer_t *b, bvconstant_t *c);


/*
 * Check whether b is reduced to a single variable x
 * m = bv_var_manager for the bitvector theory variables
 */
extern bool bvlogic_buffer_is_variable(bvlogic_buffer_t *b, bv_var_manager_t *m);


/*
 * Get the variable x stored in b if the previous condition is satisfied.
 */
extern int32_t bvlogic_buffer_get_variable(bvlogic_buffer_t *b);


/*
 * Get upper and lower bounds on the bitvector stored in bitarray a of n bits
 * - n must be positive.
 * - the bound is stored in bvconstant *c
 */
extern void bitarray_upper_bound_unsigned(uint32_t n, bit_t *a, bvconstant_t *c);
extern void bitarray_upper_bound_signed(uint32_t n, bit_t *a, bvconstant_t *c);
extern void bitarray_lower_bound_unsigned(uint32_t n, bit_t *a, bvconstant_t *c);
extern void bitarray_lower_bound_signed(uint32_t n,bit_t *a, bvconstant_t *c);



/*
 * Check wether all bits in b are equal to bit-expression bit
 */
extern bool bvlogic_buffer_allbit_equal(bvlogic_buffer_t *b, bit_t bit);


/*
 * Get all bit-vector variables reachable from e
 * - the variables are stored in vector u
 * - nodes must be the node table where e was created
 */
extern void bvlogic_expr_get_vars(bvlogic_expr_t *e, node_table_t *nodes, ivector_t *u);


/*
 * Get all terms occurring in e: i.e., terms whose theory variable is attached to
 * a bitvector variable of e
 * - the terms are stored in u
 * - nodes must be the node table where e was created
 * - pm must be the bitvector variable manager for e
 */
extern void bvlogic_expr_get_terms(bvlogic_expr_t *e, node_table_t *nodes, bv_var_manager_t *pm, ivector_t *u);


/*
 * Number of nodes in e
 */
extern uint32_t bvlogic_expr_size(bvlogic_expr_t *e, node_table_t *m);
extern uint32_t bvlogic_buffer_size(bvlogic_buffer_t *b);



/*
 * ASSIGNMENT OPERATIONS
 */
extern void bvlogic_buffer_set_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_set_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);
extern void bvlogic_buffer_set_allbits(bvlogic_buffer_t *b, uint32_t n, bit_t bit);


/*
 * BITWISE OPERATIONS
 */
extern void bvlogic_buffer_not(bvlogic_buffer_t *b);

extern void bvlogic_buffer_and_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_or_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);
extern void bvlogic_buffer_xor_constant(bvlogic_buffer_t *b, uint32_t n, uint32_t *c);

extern void bvlogic_buffer_and_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);
extern void bvlogic_buffer_or_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);
extern void bvlogic_buffer_xor_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);


/*
 * SHIFT AND ROTATE
 */

/*
 * left/right refer to b written in bigendian form, that is, b[n-1] ... b[0]
 */
extern void bvlogic_buffer_shift_left(bvlogic_buffer_t *b, uint32_t k, bit_t padding);
extern void bvlogic_buffer_shift_right(bvlogic_buffer_t *b, uint32_t k, bit_t padding);
extern void bvlogic_buffer_ashift_right(bvlogic_buffer_t *b, uint32_t k);
extern void bvlogic_buffer_rotate_left(bvlogic_buffer_t *b, uint32_t k);
extern void bvlogic_buffer_rotate_right(bvlogic_buffer_t *b, uint32_t k);

static inline void bvlogic_buffer_shift_left0(bvlogic_buffer_t *b, uint32_t k) {
  bvlogic_buffer_shift_left(b, k, false_bit);
}

static inline void bvlogic_buffer_shift_left1(bvlogic_buffer_t *b, uint32_t k) {
  bvlogic_buffer_shift_left(b, k, true_bit);
}

static inline void bvlogic_buffer_shift_right0(bvlogic_buffer_t *b, uint32_t k) {
  bvlogic_buffer_shift_right(b, k, false_bit);
}

static inline void bvlogic_buffer_shift_right1(bvlogic_buffer_t *b, uint32_t k) {
  bvlogic_buffer_shift_right(b, k, true_bit);
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

extern void bvlogic_buffer_concat_left_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);
extern void bvlogic_buffer_concat_right_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);

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
extern void bvlogic_buffer_comp_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a);







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
extern bool bvlogic_buffer_addmul_bitarray(bvlogic_buffer_t *b, uint32_t n, bit_t *a, uint32_t *c);



#endif /* __BVLOGIC_EXPR_H */
