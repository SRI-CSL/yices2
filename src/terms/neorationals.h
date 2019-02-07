/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * NEORATIONAL NUMBERS
 */

#ifndef __RATIONALS_H
#define __RATIONALS_H

#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <gmp.h>

#include "terms/mpq_aux.h"

#include "utils/memalloc.h"



/*
 * INTERNAL REPRESENTATION
 */

/*
 * A Neorational is a union of size 64 bits.
 *
 * if the least bit is 1 it represents a
 * pointer to a gmp number.
 *
 * if the least bit is zero it is a struct
 * consisting of
 * a 32 bit signed numerator, and
 * a 31 bit unsigned denominator.
 *
 */

typedef struct {
  uint32_t den;
  int32_t  num;
} rat32_t;

typedef struct {
  intptr_t gmp;
} ratgmp_t;


typedef union neorational { rat32_t s; ratgmp_t p; } neorational_t;   //s for struct; p for pointer

#define IS_RAT32  0x0
#define IS_RATGMP 0x1
/* the test for unicity in the denominator occurs frequently. the denominator is one if it is 2 :-) */
#define ONE_DEN   0x2


/*
 * Initialization: allocate and initialize
 * global variables.
 */
extern void init_neorationals(void);


/*
 * Cleanup: free memory
 */
extern void cleanup_neorationals(void);



/*
 * Set r to 0/1, Must be called before any operation on r.
 */
static inline void neoq_init(neorational_t *r) {
  r->s.num = 0;
  r->s.den = ONE_DEN;
}

/* the thing is a struct if the least bit is zero */
static inline bool is_rat32(const neorational_t *r) {
  return (r->p.gmp & IS_RATGMP) != IS_RATGMP;
}

/* the thing is a pointer if the last bit is one */
static inline bool is_ratgmp(const neorational_t *r) {
  return (r->p.gmp & IS_RATGMP) == IS_RATGMP;
}

static inline mpq_t *get_gmp(const neorational_t *r) {
  if(is_ratgmp(r)){
    return (mpq_t  *)(r->p.gmp ^ IS_RATGMP);
  } else {
    return 0;
  }
}

static inline int32_t get_num(const neorational_t *r) {
  if(is_rat32(r)){
    return r->s.num;
  } else {
    return 0;
  }
}

static inline uint32_t get_den(const neorational_t *r) {
  if(is_rat32(r)){
    return r->s.den >> 1;
  } else {
    return 0;
  }
}

//is this used?
static inline void set_rat32(neorational_t *r, int32_t num,  uint32_t den){
  //clear it first?
  r->s.num = num;
  r->s.den = (den << 1);
}

static inline void set_ratgmp(neorational_t *r, mpq_t *gmp){
  r->p.gmp = ((intptr_t)gmp) | IS_RATGMP;
}

/*
 * Allocates a new mpq object. (in case we pool them later)
 *
 */
static inline mpq_t* new_mpq(){
  mpq_t* retval;

  retval = safe_malloc(sizeof(mpq_t));
  mpq_init(*retval);
  return retval;
}

/*
 * Deallocates a new mpq object. (in case we pool them later)
 *
 */
static inline void release_mpq(neorational_t *r){
  mpq_t *q;

  assert(is_ratgmp(r));

  q = (mpq_t *)get_gmp(r);
  mpq_clear(*q);
  safe_free(q);
}


/*
 * Free mpq number attached to r if any, then set r to 0/1.
 * Must be called before r is deleted to prevent memory leaks.
 */
static inline void neoq_clear(neorational_t *r) {
  if(is_ratgmp(r)){ release_mpq(r);  }
  r->s.num = 0;
  r->s.den = ONE_DEN;
}


/*
 * If r is represented as a gmp rational, convert it
 * to a pair of integers if possible.
 * If it's possible the gmp number is freed.
 */
extern void neoq_normalize(neorational_t *r);

/*
 * ASSIGNMENT
 */

/*
 * Assign +1 or -1 to r
 */
static inline void neoq_set_one(neorational_t *r) {
  neoq_clear(r);
  r->s.num = 1;
}

static inline void neoq_set_minus_one(neorational_t *r) {
  neoq_clear(r);
  r->s.num = -1;
}

/*
 * Assignment operations: all set the value of the first argument (r or r1).
 * - in q_set_int32 and q_set_int64, num/den is normalized first
 *   (common factors are removed) and den must be non-zero
 * - in q_set_mpq, q must be canonicalized first
 *   (a copy of q is made)
 * - q_set copies r2 into r1 (if r2 is a gmp number,
 *   then a new gmp number is allocated with the same value
 *   and assigned to r1)
 * - q_set_neg assigns the opposite of r2 to r1
 * - q_set_abs assigns the absolute value of r2 to r1
 */
extern void neoq_set_int32(neorational_t *r, int32_t num, uint32_t den);
extern void neoq_set_int64(neorational_t *r, int64_t num, uint64_t den);
extern void neoq_set32(neorational_t *r, int32_t num);
extern void neoq_set64(neorational_t *r, int64_t num);

extern void neoq_set_mpq(neorational_t *r, const mpq_t q);
extern void neoq_set_mpz(neorational_t *r, const mpz_t z);
extern void neoq_set(neorational_t *r1, const neorational_t *r2);
extern void neoq_set_neg(neorational_t *r1, const neorational_t *r2);
extern void neoq_set_abs(neorational_t *r1, const neorational_t *r2);

/*
 * Copy r2 into r1: share the gmp index if r2
 * is a gmp number. Then clear r2.
 * This can be used without calling q_init(r1).
 */
static inline void neoq_copy_and_clear(neorational_t *r1, neorational_t *r2) {
  r1->s.num = r2->s.num;
  r1->s.den = r2->s.den;
  r2->s.num = 0;
  r2->s.den = ONE_DEN;
}

/*
 * Swap values of r1 and r2
 */
static inline void neoq_swap(neorational_t *r1, neorational_t *r2) {
  int32_t n;
  uint32_t d;

  n = r1->s.num;
  d = r1->s.den;
  r1->s.num = r2->s.num;
  r1->s.den = r2->s.den;
  r2->s.num = n;
  r2->s.den = d;
}

/*
 * Copy the numerator or denominator of r2 into r1
 */
extern void neoq_get_num(neorational_t *r1, const neorational_t *r2);
extern void neoq_get_den(neorational_t *r1, const neorational_t *r2);

/*
 * String parsing:
 * - set_from_string uses the GMP format with base 10:
 *       <optional_sign> <numerator>/<denominator>
 *       <optional_sign> <number>
 *
 * - set_from_string_base uses the GMP format with base b
 *
 * - set_from_float_string uses a floating point format:
 *   <optional sign> <integer part> . <fractional part>
 *   <optional sign> <integer part> <exp> <optional sign> <integer>
 *   <optional sign> <integer part> . <fractional part> <exp> <optional sign> <integer>
 *
 * where <optional sign> is + or - or nothing
 *       <exp> is either 'e' or 'E'
 *
 * The functions return -1 if the format is wrong and leave r unchanged.
 * The functions q_set_from_string and q_set_from_string_base return -2
 * if the denominator is 0.
 * Otherwise, the functions return 0 and the parsed value is stored in r.
 */
extern int neoq_set_from_string(neorational_t *r, const char *s);
extern int neoq_set_from_string_base(neorational_t *r, const char *s, int32_t b);
extern int neoq_set_from_float_string(neorational_t *r, const char *s);

/*
 * ARITHMETIC: ALL OPERATIONS MODIFY THE FIRST ARGUMENT
 */

/*
 * Arithmetic operations:
 * - all operate on the first argument:
 *    q_add: add r2 to r1
 *    q_sub: subtract r2 from r1
 *    q_mul: set r1 to r1 * r2
 *    q_div: set r1 to r1/r2 (r2 must be nonzero)
 *    q_neg: negate r
 *    q_inv: invert r (r must be nonzero)
 *    q_addmul: add r2 * r3 to r1
 *    q_submul: subtract r2 * r3 from r1
 *    q_addone: add 1 to r1
 *    q_subone: subtract 1 from r1
 * - lcm/gcd operations (r1 and r2 must be integers)
 *    q_lcm: store lcm(r1, r2) into r1
 *    q_gcd: store gcd(r1, r2) into r1 (r1 and r2 must not be zero)
 * - floor and ceiling are also in-place operations:
 *    q_floor: store largest integer <= r into r
 *    q_ceil: store smaller integer >= r into r
 */
extern void neoq_add(neorational_t *r1, const neorational_t *r2);
extern void neoq_sub(neorational_t *r1, const neorational_t *r2);
extern void neoq_mul(neorational_t *r1, const neorational_t *r2);
extern void neoq_div(neorational_t *r1, const neorational_t *r2);
extern void neoq_neg(neorational_t *r);
extern void neoq_inv(neorational_t *r);

extern void neoq_addmul(neorational_t *r1, const neorational_t *r2, const neorational_t *r3);
extern void neoq_submul(neorational_t *r1, const neorational_t *r2, const neorational_t *r3);
extern void neoq_add_one(neorational_t *r1);
extern void neoq_sub_one(neorational_t *r1);

extern void neoq_lcm(neorational_t *r1, const neorational_t *r2);
extern void neoq_gcd(neorational_t *r1, const neorational_t *r2);

extern void neoq_floor(neorational_t *r);
extern void neoq_ceil(neorational_t *r);



/*
 * Exponentiation:
 * - q_mulexp(r1, r2, n): multiply r1 by r2^n
 */
extern void neoq_mulexp(neorational_t *r1, const neorational_t *r2, uint32_t n);


/*
 * Integer division and remainder
 * - r1 and r2 must both be integer
 * - r2 must be positive.
 * - side effect: r2 is normalized
 *
 * q_integer_div(r1, r2) stores the quotient of r1 divided by r2 into r1
 * q_integer_rem(r1, r2) stores the remainder into r1
 *
 * This implements the usual definition of division (unlike C).
 * If r = remainder and q = quotient then we have
 *    0 <= r < r2 and  r1 = q * r2 + r
 */
extern void neoq_integer_div(neorational_t *r1, neorational_t *r2);
extern void neoq_integer_rem(neorational_t *r1, neorational_t *r2);


/*
 * Generalized LCM: compute the smallest non-negative rational q
 * such that q/r1 is an integer and q/r2 is an integer.
 * - r1 and r2 can be arbitrary rationals.
 * - the result is stored in r1
 */
extern void neoq_generalized_lcm(neorational_t *r1, neorational_t *r2);

/*
 * Generalized GCD: compute the largest positive rational q
 * such that r1/q and r2/q are both integer.
 * - the result is stored in r2
 */
extern void neoq_generalized_gcd(neorational_t *r1, neorational_t *r2);



/*
 * SMT2 Versions of division and mod
 *
 * Intended semantics for div and mod:
 * - if y > 0 then div(x, y) is floor(x/y)
 * - if y < 0 then div(x, y) is ceil(x/y)
 * - 0 <= mod(x, y) < y
 * - x = y * div(x, y) + mod(x, y)
 * These operations are defined for any x and non-zero y.
 * The terms x and y are not required to be integers.
 *
 * - q_smt2_div(q, x, y) stores (div x y) in q
 * - q_smt2_mod(q, x, y) stores (mod x y) in q
 *
 * For both functions, y must not be zero.
 */
extern void neoq_smt2_div(neorational_t *q, const neorational_t *x, const neorational_t *y);
extern void neoq_smt2_mod(neorational_t *q, const neorational_t *x, const neorational_t *y);


/*
 * TESTS: DO NOT MODIFY THE ARGUMENT(S)
 */

/*
 * Sign of r: q_sgn(r) = 0 if r = 0
 *            q_sgn(r) = +1 if r > 0
 *            q_sgn(r) = -1 if r < 0
 */
static inline int neoq_sgn(neorational_t *r) { //IAM: So why isn't this declared "const"????????
  if (is_ratgmp(r)) {
    mpq_t *q;

    q = get_gmp(r);
    return mpq_sgn(*q);
  } else {
    return (r->s.num < 0 ? -1 : (r->s.num > 0));
  }
}


/*
 * Compare r1 and r2:
 * - returns a negative number if r1 < r2
 * - returns 0 if r1 = r2
 * - returns a positive number if r1 > r2
 */
extern int neoq_cmp(const neorational_t *r1, const neorational_t *r2);


/*
 * Compare r1 and num/den
 * - den must be nonzero
 * - returns a negative number if r1 < num/den
 * - returns 0 if r1 = num/den
 * - returns a positive number if r1 > num/den
 */
extern int neoq_cmp_int32(const neorational_t *r1, int32_t num, uint32_t den);
extern int neoq_cmp_int64(const neorational_t *r1, int64_t num, uint64_t den);


/*
 * Variants of q_cmp:
 * - q_le(r1, r2) is nonzero iff r1 <= r2
 * - q_lt(r1, r2) is nonzero iff r1 < r2
 * - q_gt(r1, r2) is nonzero iff r1 > r2
 * - q_ge(r1, r2) is nonzero iff r1 >= r2
 * - q_eq(r1, r2) is nonzero iff r1 = r2
 * - q_neq(r1, r2) is nonzero iff r1 != r2
 */
static inline bool neoq_le(const neorational_t *r1, const neorational_t *r2) {
  return neoq_cmp(r1, r2) <= 0;
}

static inline bool neoq_lt(const neorational_t *r1, const neorational_t *r2) {
  return neoq_cmp(r1, r2) < 0;
}

static inline bool neoq_ge(const neorational_t *r1, const neorational_t *r2) {
  return neoq_cmp(r1, r2) >= 0;
}

static inline bool neoq_gt(const neorational_t *r1, const neorational_t *r2) {
  return neoq_cmp(r1, r2) > 0;
}

static inline bool neoq_eq(const neorational_t *r1, const neorational_t *r2) {
  return neoq_cmp(r1, r2) == 0;
}

static inline bool neoq_neq(const neorational_t *r1, const neorational_t *r2) {
  return neoq_cmp(r1, r2) != 0;
}


/*
 * Check whether r1 and r2 are opposite (i.e., r1 + r2 = 0)
 */
extern bool neoq_opposite(const neorational_t *r1, const neorational_t *r2);


/*
 * Tests on rational r
 */
static inline bool neoq_is_zero(const neorational_t *r) {
  return is_ratgmp(r) ? mpq_is_zero(*get_gmp(r)) : r->s.num == 0;
}

static inline bool neoq_is_nonzero(const neorational_t *r) {
  return is_ratgmp(r) ? mpq_is_nonzero(*get_gmp(r)) : r->s.num != 0;
}

static inline bool neoq_is_one(const neorational_t *r) {
  return (is_rat32(r) && r->s.den == ONE_DEN && r->s.num == 1) ||
    (is_ratgmp(r) && mpq_is_one(*get_gmp(r)));
}

static inline bool neoq_is_minus_one(const neorational_t *r) {
  return (is_rat32(r) && r->s.den == ONE_DEN && r->s.num == -1) ||
    (is_ratgmp(r) && mpq_is_minus_one(*get_gmp(r)));
}

static inline bool neoq_is_pos(const neorational_t *r) {
  return (is_rat32(r) ?  r->s.num > 0 : mpq_is_pos(*get_gmp(r)));
}

static inline bool neoq_is_nonneg(const neorational_t *r) {
  return (is_rat32(r) ?  r->s.num >= 0 : mpq_is_nonneg(*get_gmp(r)));
}

static inline bool neoq_is_neg(const neorational_t *r) {
  return (is_rat32(r) ?  r->s.num < 0 : mpq_is_neg(*get_gmp(r)));
}

static inline bool neoq_is_nonpos(const neorational_t *r) {
  return (is_rat32(r) ?  r->s.num <= 0 : mpq_is_nonpos(*get_gmp(r)));
}

static inline bool neoq_is_integer(const neorational_t *r) {
  return (is_rat32(r) && r->s.den == ONE_DEN) || (is_ratgmp(r) && mpq_is_integer(*get_gmp(r)));
}



/*
 * DIVISIBILITY TESTS
 */

/*
 * Check whether r1 divides r2: both must be integers
 * - r1 must be non-zero
 * - side effect: r1 is normalized
 */
extern bool neoq_integer_divides(neorational_t *r1, const neorational_t *r2);


/*
 * General divisibility check: return true iff r2/r1 is an integer
 * - r1 must be non-zero
 */
extern bool neoq_divides(const neorational_t *r1, const neorational_t *r2);


/*
 * SMT2 version:
 * - if t1 is non-zero, return true iff (r2/r1) is an integer
 * - if t1 is zero, return true iff r2 is zero
 */
extern bool neoq_smt2_divides(const neorational_t *r1, const neorational_t *r2);




/*
 * CONVERSIONS TO INTEGERS
 */

/*
 * Check whether r is a small integer (use with care: this
 * ignores the case where r is a small integer that happens
 * to be represented as a gmp rational).
 * Call q_normalize(r) first if there's a doubt.
 */
static inline bool neoq_is_smallint(neorational_t *r) {
  return r->s.den == ONE_DEN;    //IAM: this looks too risky to be worth it.
}

/*
 * Convert r to an integer, provided q_is_smallint(r) is true
 */
static inline int32_t neoq_get_smallint(neorational_t *r) {
  return r->s.num;
}


/*
 * Conversions: all functions attempt to convert r into an integer or
 * a pair of integers (num/den). If the conversion is not possible
 * the functions return false. Otherwise, the result is true and the
 * value is returned in v or num/den.
 */
extern bool neoq_get32(neorational_t *r, int32_t *v);
extern bool neoq_get64(neorational_t *r, int64_t *v);
extern bool neoq_get_int32(neorational_t *r, int32_t *num, uint32_t *den);
extern bool neoq_get_int64(neorational_t *r, int64_t *num, uint64_t *den);


/*
 * Similar to the conversion functions above but just check
 * whether the conversions are possible.
 */
extern bool neoq_is_int32(neorational_t *r);   // r is a/1 where a is int32
extern bool neoq_is_int64(neorational_t *r);   // r is a/1 where a is int64
extern bool neoq_fits_int32(neorational_t *r); // r is a/b where a is int32, b is uint32
extern bool neoq_fits_int64(neorational_t *r); // r is a/b where a is int64, b is uint64



/*
 * Size estimate
 * - this returns approximately the number of bits to represent r's numerator
 * - this may not be exact (typically rounded up to a multiple of 32)
 * - also if r is really really big, this function may return
 *   UINT32_MAX (not very likely!)
 */
extern uint32_t neoq_size(neorational_t *r);


/*
 * CONVERSION TO GMP OBJECTS
 */

/*
 * Store r into the GMP integer z.
 * - return false if r is not a integer, true otherwise
 */
extern bool neoq_get_mpz(neorational_t *r, mpz_t z);


/*
 * Store r into q
 */
extern void neoq_get_mpq(neorational_t *r, mpq_t q);


/*
 * Convert to a floating point number
 */
extern double neoq_get_double(neorational_t *r);



/*
 * PRINT
 */

/*
 * Print r on stream f.
 * q_print_abs prints the absolute value
 */
extern void neoq_print(FILE *f, const neorational_t *r);
extern void neoq_print_abs(FILE *f, const neorational_t *r);


/*
 * HASH FUNCTION
 */

/*
 * Hash functions: return a hash of numerator or denominator.
 * - hash_numerator(r) = numerator MOD bigprime
 * - hash_denominator(r) = denominator MOD bigprime
 * where bigprime is the largest prime number smaller than 2^32.
 */
extern uint32_t neoq_hash_numerator(const neorational_t *r);
extern uint32_t neoq_hash_denominator(const neorational_t *r);
extern void neoq_hash_decompose(const neorational_t *r, uint32_t *h_num, uint32_t *h_den);




/*
 * RATIONAL ARRAYS
 */

#define MAX_RATIONAL_ARRAY_SIZE (UINT32_MAX/sizeof(neorational_t))

/*
 * Create and initialize an array of n rationals.
 */
extern neorational_t *new_rational_array(uint32_t n);

/*
 * Delete an array created by the previous function
 * - n must be the size of a
 */
extern void free_rational_array(neorational_t *a, uint32_t n);





#endif /* __NEORATIONALS_H */
