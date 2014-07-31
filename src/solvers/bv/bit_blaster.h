/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * SUPPORT FOR CONVERTING BITVECTOR CONSTRAINTS INTO CLAUSES
 */

#ifndef __BIT_BLASTER_H
#define __BIT_BLASTER_H

#include <stdint.h>
#include <stdbool.h>

#include "utils/int_vectors.h"
#include "solvers/cdcl/gates_hash_table.h"
#include "solvers/bv/remap_table.h"
#include "solvers/cdcl/smt_core.h"



/*
 * CLAUSE-SET BUFFER
 *
 * Each gate/elementary component is encoded as a small set
 * of clauses (with no more than four variables).
 * A clause buffer is used to build and simplify this set.
 *
 * Main components:
 * - var[0 .. 3] = boolean variables occurring in the set
 *   if there are fewer than 4 variables, then var is
 *   padded with null_bvar
 * - nclauses = number of clauses in the set
 * - each clause is identified by an index between 0 and nclauses-1
 * - data = two-dimensional array.
 *   For clause i and var[j] = x, data[i][j] indicates whether x
 *   occurs in clause i, and if so, with which polarity.
 *   This is encoded as follows:
 *      data[i][j] =  0 --> x does not occur in clause i
 *      data[i][j] = +1 --> clause i contains the literal pos_lit(x)
 *      data[i][j] = -1 --> clause i contains the literal neg_lit(x)
 *
 * To check for subsumption and subsumption-resolution, we keep
 * a signature for each clause. The signature is a 4-bit integer,
 * bit j of signature[i] is 1 iff var[j] occurs in clause i.
 *
 * The flag is_unsat is set if one of the clauses is empty.
 *
 * Mask is used as a bitvector in simplification. If bit i
 * of mask is 1 then clause i has been removed.
 */

// Dimensions: at most 8 clauses, at most 4 variables
#define CBUFFER_NVARS    4
#define CBUFFER_NCLAUSES 8

typedef struct cbuffer_s {
  uint32_t nclauses;
  uint32_t mask;
  bool is_unsat;
  bvar_t var[CBUFFER_NVARS];
  uint8_t signature[CBUFFER_NCLAUSES];
  int8_t data[CBUFFER_NCLAUSES][CBUFFER_NVARS];
} cbuffer_t;



/*
 * BIT-BLASTER:
 *
 * This is the main structure for encoding boolean gates and
 * bit-vector constraints into clauses.
 *
 * Components:
 * - solver: attached smt_core
 *   where the clauses and literals are created
 * - remap_table to interface with the bvsolver
 * - gate table for hash consing
 * - buffers
 */
typedef struct bit_blaster_s {
  smt_core_t *solver;
  remap_table_t *remap;
  gate_table_t htbl;
  cbuffer_t buffer;
  ivector_t aux_vector;
  ivector_t aux_vector2;
  ivector_t aux_vector3;
  ivector_t aux_vector4;
} bit_blaster_t;



/*
 * BOUND FOR HASH-CONSING
 *
 * When building (OR a[0] ... a[n-1]) or (XOR a[0] ... a[n-1]),
 * hash consing is used only if n <= BIT_BLASTER_MAX_HASHCONS_SIZE.
 *
 * The bound must be no more than MAX_INDEGREE (defined in gates_hash_table.h).
 * It should be at least 3, since or/xor with 2 or 3 arguments are always
 * hash-consed.
 */
#define BIT_BLASTER_MAX_HASHCONS_SIZE 20



/***********************************
 *  INITIALIZATION/PUSH/POP/RESET  *
 **********************************/

/*
 * Initialization:
 * - htbl is initialized to its default size
 * - solver and remap must be initialized outside this function
 */
extern void init_bit_blaster(bit_blaster_t *blaster, smt_core_t *solver, remap_table_t *remap);


/*
 * Deletion: don't delete the solver, just the hash table
 */
extern void delete_bit_blaster(bit_blaster_t *blaster);


/*
 * Reset internal structures, not the solver
 */
extern void reset_bit_blaster(bit_blaster_t *blaster);


/*
 * Push/pop just apply to the internal gate table
 */
static inline void bit_blaster_push(bit_blaster_t *blaster) {
  gate_table_push(&blaster->htbl);
}

static inline void bit_blaster_pop(bit_blaster_t *blaster) {
  gate_table_pop(&blaster->htbl);
}


/*
 * Set level: same effect as calling push n times
 * - this is used to ensure that the bit-blaster trail stack
 *   has the same depth as the bv_solver when the bit_blaster is allocated
 */
static inline void bit_blaster_set_level(bit_blaster_t *blaster, uint32_t n) {
  gate_table_set_level(&blaster->htbl, n);
}



/**********************
 *  ELEMENTARY GATES  *
 *********************/

/*
 * The basic gates are listed in gates_hash_table.h.  All functions
 * below add clauses that encode the definition of a specific
 * gate. The clauses are simplified as much as possible. If the
 * constraints are inconsistent then the empty clause is added to
 * the solver.
 */

/*
 * Constraint: b = a or (xor a b) = 0
 */
extern void bit_blaster_eq(bit_blaster_t *blaster, literal_t a, literal_t b);


/*
 * Constraint: x = (xor a b) or (xor a b x) = 0
 */
extern void bit_blaster_xor2_gate(bit_blaster_t *blaster, literal_t a, literal_t b, literal_t x);


/*
 * Constraint: x = (xor a b c) or (xor a b c x) = 0
 */
extern void bit_blaster_xor3_gate(bit_blaster_t *blaster, literal_t a, literal_t b, literal_t c, literal_t x);


/*
 * Constraint: x = (or a b)
 */
extern void bit_blaster_or2_gate(bit_blaster_t *blaster, literal_t a, literal_t b, literal_t x);


/*
 * Constraint: x = (or a b c)
 */
extern void bit_blaster_or3_gate(bit_blaster_t *blaster, literal_t a, literal_t b, literal_t c, literal_t x);


/*
 * Constraint: x = (ite c a b)
 */
extern void bit_blaster_mux(bit_blaster_t *blaster, literal_t c, literal_t a, literal_t b, literal_t x);


/*
 * Constraint: x = (cmp a b c)
 * Defined as: x = ((a > b) or (a = b and c))
 *
 * This is used to encode (bvuge u v) or (bvsge u v) via the following equations:
 * 1) (bvuge u v) = (u[n] > v[n]) or (u[n] == v[n] and (bvuge u[n-1 .. 1] v[n-1 .. 1]))
 * 2) (bvsge u v) = (v[n] > u[n]) or (u[n] == v[n] and (bvuge u[n-1 .. 1] v[n-1 .. 1]))
 */
extern void bit_blaster_cmp(bit_blaster_t *blaster, literal_t a, literal_t b, literal_t c, literal_t x);


/*
 * Constraint: x = (majority a b c)
 */
extern void bit_blaster_maj3(bit_blaster_t *blaster, literal_t a, literal_t b, literal_t c, literal_t x);


/*
 * Constraint: x = (or a[0] ... a[n-1])
 */
extern void bit_blaster_or_gate(bit_blaster_t *blaster, uint32_t n, literal_t *a, literal_t x);


/*
 * Constraint: x = (xor a[0] ... a[n-1])
 */
extern void bit_blaster_xor_gate(bit_blaster_t *blaster, uint32_t n, literal_t *a, literal_t x);


/*
 * Constraint: (x, y) = half-add(a, b) where x = sum, y = carry
 * This is encoded as
 *    x = (xor a b)
 *    y = (and a b)
 */
extern void bit_blaster_half_adder(bit_blaster_t *blaster, literal_t a, literal_t b,
                                   literal_t x, literal_t y);

/*
 * Constraint: (x, y) = full-adder(a, b, c) where x = sum, y = carry
 * This is encoded as
 *    x = (xor a b c)
 *    y = (majority a b c)
 */
extern void bit_blaster_full_adder(bit_blaster_t *blaster, literal_t a, literal_t b, literal_t c,
                                   literal_t x, literal_t y);






/*****************
 *  SIMPLIFIER   *
 ****************/

/*
 * All functions below attempt to reduce an expression to a literal.
 * They return null_literal when they fail.
 * They take into account the base-value of all literals.
 */

/*
 * (xor a b)
 */
extern literal_t bit_blaster_eval_xor2(bit_blaster_t *blaster, literal_t a, literal_t b);


/*
 * (xor a b c)
 */
extern literal_t bit_blaster_eval_xor3(bit_blaster_t *blaster, literal_t a, literal_t b, literal_t c);


/*
 * (eq a b)
 */
static inline literal_t bit_blaster_eval_eq(bit_blaster_t *blaster, literal_t a, literal_t b) {
  return bit_blaster_eval_xor2(blaster, not(a), b);
}


/*
 * (or a b)
 */
extern literal_t bit_blaster_eval_or2(bit_blaster_t *blaster, literal_t a, literal_t b);


/*
 * (or a b c)
 */
extern literal_t bit_blaster_eval_or3(bit_blaster_t *blaster, literal_t a, literal_t b, literal_t c);


/*
 * (ite c a b)
 */
extern literal_t bit_blaster_eval_mux(bit_blaster_t *blaster, literal_t c, literal_t a, literal_t b);


/*
 * (a > b): i.e. (a and not b)
 */
extern literal_t bit_blaster_eval_gt(bit_blaster_t *blaster, literal_t a, literal_t b);


/*
 * (cmp a b c) i.e., ((a > b) or (a = b and c))
 */
extern literal_t bit_blaster_eval_cmp(bit_blaster_t *blaster, literal_t a, literal_t b, literal_t c);


/*
 * (majority a b c)
 */
extern literal_t bit_blaster_eval_maj3(bit_blaster_t *blaster, literal_t a, literal_t b, literal_t c);


/*
 * (or a[0] ... a[n-1])
 */
extern literal_t bit_blaster_eval_or(bit_blaster_t *blaster, uint32_t n, literal_t *a);


/*
 * (xor a[0] ... a[n-1])
 */
extern literal_t bit_blaster_eval_xor(bit_blaster_t *blaster, uint32_t n, literal_t *a);



/*
 * (bveq a b): a and b are vectors of n bits
 */
extern literal_t bit_blaster_eval_bveq(bit_blaster_t *blaster, uint32_t n, literal_t *a, literal_t *b);






/*******************************
 *  BOOLEAN GATE CONSTRUCTION  *
 ******************************/

/*
 * Create a new boolean variable
 */
extern bvar_t bit_blaster_new_var(bit_blaster_t *blaster);

/*
 * Create a new literal
 */
static inline literal_t bit_blaster_fresh_literal(bit_blaster_t *blaster) {
  return pos_lit(bit_blaster_new_var(blaster));
}



/*
 * All functions below return a literal l = (op a b ..) for some
 * primitive operator op. They use the following steps:
 * 1) Try to simplify (op a b ...) to l
 * 2) If that fails, search for the the gate (op a b ..)
 *    in the hash table.
 * 3) If that fails create a fresh literal l, assert
 *    the constraints l = (op a b ...) and add the gate to
 *    the hash table.
 */

/*
 * (xor a[0] ... a[n-1])
 */
extern literal_t bit_blaster_make_xor(bit_blaster_t *blaster, uint32_t n, literal_t *a);

/*
 * (xor a b)
 */
extern literal_t bit_blaster_make_xor2(bit_blaster_t *blaster, literal_t a, literal_t b);


/*
 * (xor a b c)
 */
extern literal_t bit_blaster_make_xor3(bit_blaster_t *blaster, literal_t a, literal_t b, literal_t c);


/*
 * (eq a b)
 */
static inline literal_t bit_blaster_make_eq(bit_blaster_t *blaster, literal_t a, literal_t b) {
  return bit_blaster_make_xor2(blaster, not(a), b);
}


/*
 * (or a[0] ... a[n-1])
 */
extern literal_t bit_blaster_make_or(bit_blaster_t *blaster, uint32_t n, literal_t *a);

/*
 * (or a b)
 */
extern literal_t bit_blaster_make_or2(bit_blaster_t *blaster, literal_t a, literal_t b);


/*
 * (or a b c)
 */
extern literal_t bit_blaster_make_or3(bit_blaster_t *blaster, literal_t a, literal_t b, literal_t c);


/*
 * (and a b)
 */
static inline literal_t bit_blaster_make_and2(bit_blaster_t *blaster, literal_t a, literal_t b) {
  return not(bit_blaster_make_or2(blaster, not(a), not(b)));
}




/***************************
 *  CIRCUIT CONSTRUCTION   *
 **************************/

/*
 * BIT-VECTOR COMPARATORS:
 * - input = 2 literal arrays of size n
 * - output = 1 literal
 * All the literals in both arrays must be non-null (valid literals in the bit_solver)
 *
 * (bveq a b)   --> equality
 * (bvuge a b)  --> (a >= b) with both interpreted as n-bit unsigned integers
 * (bvsge a b)  --> (a >= b) with both interpreted as n-bit signed integers.
 *
 * For bveq and bvuge, n may be zero.
 * For bvsge, n must be positive.
 */
extern literal_t bit_blaster_make_bveq(bit_blaster_t *blaster, literal_t *a, literal_t *b, uint32_t n);
extern literal_t bit_blaster_make_bvuge(bit_blaster_t *blaster, literal_t *a, literal_t *b, uint32_t n);
extern literal_t bit_blaster_make_bvsge(bit_blaster_t *blaster, literal_t *a, literal_t *b, uint32_t n);


/*
 * Variants
 * - assert l == (bveq a b)
 * - assert l == (bvuge a b)
 * - assert l == (bvsge a b)
 */
extern void bit_blaster_make_bveq2(bit_blaster_t *blaster, literal_t *a, literal_t *b, literal_t l, uint32_t n);
extern void bit_blaster_make_bvuge2(bit_blaster_t *blaster, literal_t *a, literal_t *b, literal_t l, uint32_t n);
extern void bit_blaster_make_bvsge2(bit_blaster_t *blaster, literal_t *a, literal_t *b, literal_t l, uint32_t n);



/*
 * ASSERTION OF EQUALITIES/INEQUALITIES
 * - a and b must be literal arrays of size n
 * - all literals in both arrays must be non-null
 *
 *  (bveq a b): assert a = b
 * (bvneq a b): assert a /= b
 * (bvuge a b): assert a >= b (unsigned)
 * (bvult a b): assert a < b  (unsigned)
 * (bvsge a b): assert a >= b (signed, n must be positive)
 * (bvslt a b): assert a < b  (signed, n must be positive)
 *
 * If the constraint is inconsistent, then a conflict is recorded
 * in the bit_solver (by adding the empty clause).
 */
extern void bit_blaster_assert_bveq(bit_blaster_t *blaster, literal_t *a, literal_t *b, uint32_t n);
extern void bit_blaster_assert_bvneq(bit_blaster_t *blaster, literal_t *a, literal_t *b, uint32_t n);
extern void bit_blaster_assert_bvuge(bit_blaster_t *blaster, literal_t *a, literal_t *b, uint32_t n);
extern void bit_blaster_assert_bvult(bit_blaster_t *blaster, literal_t *a, literal_t *b, uint32_t n);
extern void bit_blaster_assert_bvsge(bit_blaster_t *blaster, literal_t *a, literal_t *b, uint32_t n);
extern void bit_blaster_assert_bvslt(bit_blaster_t *blaster, literal_t *a, literal_t *b, uint32_t n);




/*
 * The following functions encode a bit-vector circuit with arrays of literals
 * as input and an array u of pseudo-literal as output.
 * - all elements in arrays a and b must be valid literals in the bit_solver
 * - all elements of u must be non-null pseudo literals in the remap table
 * - if pseudo-literal u[i] is not mapped to a real literal, then the
 *   circuit constructions assign a real literal to u[i]
 *   (and all elements of its class)
 * - if pseudo-literal u[i] is mapped to a real literal l, then the functions
 *   add clauses to encode the equality between l and the circuit output
 *   (e.g., for the adder circuit: assert l = bit[i] in sum of a and b).
 *
 * If the constraint is inconsistent, then a conflict is recorded
 * in the bit_solver (by adding the empty clause).
 */


/*
 * MULTIPLEXER: assert u = (ite c a b)
 * - a and b must be literal arrays of size n
 * - u must be a pseudo literal array of size n
 * - c must be a valid literal in the bit_solver
 */
extern void bit_blaster_make_bvmux(bit_blaster_t *blaster, literal_t c, literal_t *a,
                                   literal_t *b, literal_t *u, uint32_t n);


/*
 * ARITHMETIC CIRCUITS
 * - a and b must be literal arrays of size n
 * - u must be a pseudo literal array of size n
 */
extern void bit_blaster_make_bvadd(bit_blaster_t *blaster, literal_t *a, literal_t *b, literal_t *u, uint32_t n);
extern void bit_blaster_make_bvsub(bit_blaster_t *blaster, literal_t *a, literal_t *b, literal_t *u, uint32_t n);
extern void bit_blaster_make_bvneg(bit_blaster_t *blaster, literal_t *a, literal_t *u, uint32_t n);
extern void bit_blaster_make_bvmul(bit_blaster_t *blaster, literal_t *a, literal_t *b, literal_t *u, uint32_t n);



/*
 * Variant implementation of bvmul
 */
extern void bit_blaster_make_bvmul2(bit_blaster_t *blaster, literal_t *a, literal_t *b, literal_t *u, uint32_t n);


/*
 * UNSIGNED DIVISION
 * - a and b must be literal arrays of size n
 * - q = either NULL or an array of n pseudo literals
 * - r = either NULL of an array of n pseudo literals
 *
 * If both r and q are non-null, the function asserts
 *   q = (bvudiv a b): quotient
 *   r = (bvurem a b): remainder
 * If r is NULL only the first part is asserted.
 * If q is NULL only the second equality is asserted.
 *
 * This asserts (a = b * q + r) AND (b == 0 or r < b)
 *
 * For division by zero: q is 0b111...1 and r = a.
 */
extern void bit_blaster_make_udivision(bit_blaster_t *blaster, literal_t *a, literal_t *b,
                                       literal_t *q, literal_t *r, uint32_t n);


// Variant implementation
extern void bit_blaster_make_udivision2(bit_blaster_t *blaster, literal_t *a, literal_t *b,
                                        literal_t *q, literal_t *r, uint32_t n);




/*
 * SIGNED DIVISION
 * - a and b must be literal arrays of size n
 * - q = either NULL or an array of n pseudo literals
 * - r = either NULL of an array of n pseudo literals
 *
 * If both r and q are non-null, the function asserts
 *   q = (bvsdiv a b): quotient
 *   r = (bvsrem a b): remainder
 * If r is NULL only the first part is asserted.
 * If q is NULL only the secont equality is asserted.
 *
 * This asserts a = b * q + r
 * with the following constraints on r:
 *  (a >= 0, b > 0 ==>  0 <= r <  b)
 *  (a >= 0, b < 0 ==>  0 <= r < -b)
 *  (a < 0,  b > 0 ==> -b <  r <= 0)
 *  (a < 0,  b < 0 ==>  b <  r <= 0)
 *
 * For division by zero:
 *  (a >= 0, b = 0 ==>  r = a, q = -1)
 *  (a < 0,  b = 0 ==>  r = a, q = +1)
 *
 */
extern void bit_blaster_make_sdivision(bit_blaster_t *blaster, literal_t *a, literal_t *b,
                                       literal_t *q, literal_t *r, uint32_t n);


// Variant implementation
extern void bit_blaster_make_sdivision2(bit_blaster_t *blaster, literal_t *a, literal_t *b,
                                        literal_t *q, literal_t *r, uint32_t n);




/*
 * FLOOR DIVISION REMAINDER.
 *
 * - a and b must be literal arrays of size n
 * - r must be an array of n pseudo literals
 *
 * This asserts r = bvsmod(a, b)
 * - if b is zero, then bsvmod(a, b) = a
 * - otherwise, bvsmod(a, b) = a - b * floor(a/b)
 *
 * This is similar to fdiv in GMP: division with
 * rounding toward minus infinity.
 *
 * For b > 0, we have 0 <= r <  b
 * For b < 0, we have b <  r <= 0
 */
extern void bit_blaster_make_smod(bit_blaster_t *blaster, literal_t *a, literal_t *b, literal_t *r, uint32_t n);


/*
 * SHIFT LEFT
 * - a = vector to be shifted
 * - b = shift amount
 * Both a and b must be arrays of n non-null literals
 * - u = result: array of n pseudo literals
 *
 * The function asserts u == (bvshl a b)
 *
 * The SMT-LIB semantics for logical shift is that (bvshl a b) is equivalent
 * to multiplying a by 2^b. So if b's value is larger than n the result is 0b00..000.
 */
extern void bit_blaster_make_shift_left(bit_blaster_t *blaster, literal_t *a, literal_t *b, literal_t *u, uint32_t n);



/*
 * LOGICAL SHIFT RIGHT
 * - a = vector to be shifted
 * - b = shift amount
 * Both a and b must be arrays of n non-null literals
 * - u = result: array of n pseudo literals
 *
 * The function asserts u == (bvlshr a b) (padding with 0)
 *
 * If b's value is larger than n the result is 0b00..000.
 */
extern void bit_blaster_make_lshift_right(bit_blaster_t *blaster, literal_t *a, literal_t *b, literal_t *u, uint32_t n);


/*
 * LOGICAL SHIFT RIGHT
 * - a = vector to be shifted
 * - b = shift amount
 * Both a and b must be arrays of n non-null literals
 * - u = result: array of n pseudo literals
 *
 * The function asserts u == (bvashr a b) (sign bit is copied)
 *
 * If b's value is larger than n the result is [s ... s],
 * where s = sign bit of a.
 */
extern void bit_blaster_make_ashift_right(bit_blaster_t *blaster, literal_t *a, literal_t *b, literal_t *u, uint32_t n);



#endif /* __BIT_BLASTER_H */
