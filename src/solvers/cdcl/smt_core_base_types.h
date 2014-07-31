/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * BOOLEAN VARIABLES AND LITERALS
 */

#ifndef __SMT_CORE_BASE_TYPES_H
#define __SMT_CORE_BASE_TYPES_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>


/*
 * Boolean variables: integers between 0 and nvars - 1
 * Literals: integers between 0 and 2nvar - 1.
 *
 * For a variable x, the positive literal is 2x, the negative
 * literal is 2x + 1.
 *
 * -1 is a special marker for both variables and literals
 *
 * Two literals representing the constant true/false are created
 * when the solver is initialized.
 */
typedef int32_t bvar_t;
typedef int32_t literal_t;

enum {
  // markers
  null_bvar = -1,
  null_literal = -1,

  // boolean constants
  const_bvar = 0,
  true_literal = 0,
  false_literal = 1,
};


/*
 * Maximal number of boolean variables
 */
#define MAX_VARIABLES (INT32_MAX >> 2)

/*
 * Conversions from variables to literals
 */
static inline literal_t pos_lit(bvar_t x) {
  return x<<1;
}

static inline literal_t neg_lit(bvar_t x) {
  return (x<<1) | 1;
}

/*
 * mk_lit(x, 0) = pos_lit(x)
 * mk_lit(x, 1) = neg_lit(x)
 */
static inline literal_t mk_lit(bvar_t x, uint32_t sign) {
  assert((sign & ~1) == 0);
  return (x<<1)|sign;
}


/*
 * Extract variable and sign
 */
static inline bvar_t var_of(literal_t l) {
  return l>>1;
}

static inline uint32_t sign_of_lit(literal_t l) {
  return ((uint32_t) l) & 1;
}


// true if l has positive polarity (i.e., l = pos_lit(x))
static inline bool is_pos(literal_t l) {
  return !(l & 1);
}

static inline bool is_neg(literal_t l) {
  return (l & 1);
}


// negation of literal l
static inline literal_t not(literal_t l) {
  return l ^ 1;
}

// check whether l1 and l2 are opposite
static inline bool opposite(literal_t l1, literal_t l2) {
  return (l1 ^ l2) == 1;
}


/*
 * add polarity tt to l:
 * - if tt is true return l
 * - if tt is false, return (not l)
 */
static inline literal_t signed_literal(literal_t l, bool tt) {
  return l ^ (((int32_t) tt) ^ 1);
}


/*
 * Variant of mk_lit that takes a boolean polarity instead of
 * a sign:
 * - mk_signed_lit(x, true) = mk_lit(x, 0) = pos_lit(x)
 * - mk_signed_lit(x, false) = mk_lit(x, 1) = neg_lit(x)
 */
static inline literal_t mk_signed_lit(bvar_t x, bool tt) {
  return (x << 1) | (tt ^ 1);
}


/*
 * Remove the sign of l (i.e., force the sign bit to 0)
 * - if l is pos_lit(x) return l
 * - if l is neg_lit(x) return not(l)
 */
static inline literal_t unsigned_literal(literal_t l) {
  return l & ~1;
}


/*
 * Conversion from boolean to literals
 * - bool2literal(true) = true_literal
 * - bool2literal(false) = false_literal
 */
static inline literal_t bool2literal(bool tt) {
  return ((int32_t) tt) ^ 1;
}



/*
 * Assignment values for a literal or variable
 * - we use four values to encode the truth value of x
 *   when x is assigned, and the preferred value when x is
 *   not assigned.
 * - value[x] is interpreted as follows
 *   VAL_UNDEF_FALSE = 0b00 --> x not assigned, preferred value = false
 *   VAL_UNDEF_TRUE  = 0b01 --> x not assigned, preferred value = true
 *   VAL_FALSE = 0b10       --> x assigned false
 *   VAL_TRUE =  0b11       --> x assigned true
 *
 * The preferred value is used when x is selected as a decision variable.
 * Then we assign x to true or false depending on the preferred value.
 * This is done by setting bit 1 in value[x].
 */
typedef enum bval {
  VAL_UNDEF_FALSE = 0,
  VAL_UNDEF_TRUE = 1,
  VAL_FALSE = 2,
  VAL_TRUE = 3,
} bval_t;


/*
 * Check on boolean values
 */
static inline bool bval_is_undef(bval_t v) { // bit 1 is unset
  return (v & 2) == 0;
}

static inline bool bval_is_def(bval_t v) { // bit 1 is set
  return (v & 2) != 0;
}

/*
 * Convert to a Boolean (extract the low-order bit)
 */
static inline bool bval2bool(bval_t v) {
  return v & 1;
}


#endif /* __SMT_CORE_BASE_TYPES_H */
