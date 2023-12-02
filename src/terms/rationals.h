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
 * A neorational is a union of size 64 bits.
 *
 * if the least bit is 1 it represents a
 * pointer to a gmp number.
 *
 * if the least bit is zero it is a struct consisting of a 32 bit
 * signed numerator, and a 31 bit unsigned denominator.
 */
typedef struct {
#ifdef WORDS_BIGENDIAN
  int32_t  num;
  uint32_t den;
#else
  uint32_t den;
  int32_t  num;
#endif
} rat32_t;

typedef struct {
  intptr_t gmp;
} ratgmp_t;


typedef union rational { rat32_t s; ratgmp_t p; } rational_t;   //s for struct; p for pointer

#define IS_RAT32  0x0
#define IS_RATGMP 0x1
/* the test for unicity in the denominator occurs frequently. the denominator is one if it is 2 :-) */
#define ONE_DEN   0x2


/*
 * Initialization: allocate and initialize
 * global variables.
 */
extern void init_rationals(void);


/*
 * Cleanup: free memory
 */
extern void cleanup_rationals(void);


/*
 * Set r to 0/1, Must be called before any operation on r.
 */
static inline void q_init(rational_t *r) {
  r->s.num = 0;
  r->s.den = ONE_DEN;
}


/*
 * Tests and conversions to/from gmp and rat32
 *
 * NOTE: the type mpq_ptr is defined in gmp.h. It's a pointer
 * to the internal structure representing a gmp number.
 */
static inline bool is_rat32(const rational_t *r) {
  return (r->p.gmp & IS_RATGMP) != IS_RATGMP;
}

static inline bool is_ratgmp(const rational_t *r) {
  return (r->p.gmp & IS_RATGMP) == IS_RATGMP;
}

static inline mpq_ptr get_gmp(const rational_t *r) {
  assert(is_ratgmp(r));  
  return (mpq_ptr) (r->p.gmp ^ IS_RATGMP);
}

static inline int32_t get_num(const rational_t *r) {
  assert(is_rat32(r));  
  return r->s.num;
}

static inline uint32_t get_den(const rational_t *r) {
  assert(is_rat32(r));
  return r->s.den >> 1;
}

static inline void set_ratgmp(rational_t *r, mpq_ptr gmp){
  r->p.gmp = ((intptr_t) gmp) | IS_RATGMP;
}

/*
 * Free mpq number attached to r if any, then set r to 0/1.
 * Must be called before r is deleted to prevent memory leaks.
 */
extern void q_clear(rational_t *r);

/*
 * If r is represented as a gmp rational, convert it
 * to a pair of integers if possible.
 * If it's possible the gmp number is freed.
 */
extern void q_normalize(rational_t *r);


/*
 * ASSIGNMENT
 */

/*
 * Assign +1 or -1 to r
 */
static inline void q_set_one(rational_t *r) {
  q_clear(r);
  r->s.num = 1;
}

static inline void q_set_minus_one(rational_t *r) {
  q_clear(r);
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
extern void q_set_int32(rational_t *r, int32_t num, uint32_t den);
extern void q_set_int64(rational_t *r, int64_t num, uint64_t den);
extern void q_set32(rational_t *r, int32_t num);
extern void q_set64(rational_t *r, int64_t num);

extern void q_set_mpq(rational_t *r, const mpq_t q);
extern void q_set_mpz(rational_t *r, const mpz_t z);
extern void q_set(rational_t *r1, const rational_t *r2);
extern void q_set_neg(rational_t *r1, const rational_t *r2);
extern void q_set_abs(rational_t *r1, const rational_t *r2);

/*
 * Copy r2 into r1: share the gmp index if r2
 * is a gmp number. Then clear r2.
 * This can be used without calling q_init(r1).
 */
static inline void q_copy_and_clear(rational_t *r1, rational_t *r2) {
  *r1 = *r2;
  r2->s.num = 0;
  r2->s.den = ONE_DEN;
}

/*
 * Swap values of r1 and r2
 */
static inline void q_swap(rational_t *r1, rational_t *r2) {
  rational_t aux;

  aux = *r1;
  *r1 = *r2;
  *r2 = aux;
}

/*
 * Copy the numerator or denominator of r2 into r1
 */
extern void q_get_num(rational_t *r1, const rational_t *r2);
extern void q_get_den(rational_t *r1, const rational_t *r2);

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
extern int q_set_from_string(rational_t *r, const char *s);
extern int q_set_from_string_base(rational_t *r, const char *s, int32_t b);
extern int q_set_from_float_string(rational_t *r, const char *s);

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
extern void q_add(rational_t *r1, const rational_t *r2);
extern void q_sub(rational_t *r1, const rational_t *r2);
extern void q_mul(rational_t *r1, const rational_t *r2);
extern void q_div(rational_t *r1, const rational_t *r2);
extern void q_neg(rational_t *r);
extern void q_inv(rational_t *r);

extern void q_addmul(rational_t *r1, const rational_t *r2, const rational_t *r3);
extern void q_submul(rational_t *r1, const rational_t *r2, const rational_t *r3);
extern void q_add_one(rational_t *r1);
extern void q_sub_one(rational_t *r1);

extern void q_lcm(rational_t *r1, const rational_t *r2);
extern void q_gcd(rational_t *r1, const rational_t *r2);

extern void q_floor(rational_t *r);
extern void q_ceil(rational_t *r);



/*
 * Exponentiation:
 * - q_mulexp(r1, r2, n): multiply r1 by r2^n
 */
extern void q_mulexp(rational_t *r1, const rational_t *r2, uint32_t n);


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
extern void q_integer_div(rational_t *r1, rational_t *r2);
extern void q_integer_rem(rational_t *r1, rational_t *r2);


/*
 * Generalized LCM: compute the smallest non-negative rational q
 * such that q/r1 is an integer and q/r2 is an integer.
 * - r1 and r2 can be arbitrary rationals.
 * - the result is stored in r1
 */
extern void q_generalized_lcm(rational_t *r1, rational_t *r2);

/*
 * Generalized GCD: compute the largest positive rational q
 * such that r1/q and r2/q are both integer.
 * - the result is stored in r2
 */
extern void q_generalized_gcd(rational_t *r1, rational_t *r2);



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
extern void q_smt2_div(rational_t *q, const rational_t *x, const rational_t *y);
extern void q_smt2_mod(rational_t *q, const rational_t *x, const rational_t *y);


/*
 * TESTS: DO NOT MODIFY THE ARGUMENT(S)
 */

/*
 * Sign of r: q_sgn(r) = 0 if r = 0
 *            q_sgn(r) = +1 if r > 0
 *            q_sgn(r) = -1 if r < 0
 */
static inline int q_sgn(const rational_t *r) {
  if (is_ratgmp(r)) {
    return mpq_sgn(get_gmp(r));
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
extern int q_cmp(const rational_t *r1, const rational_t *r2);


/*
 * Compare r1 and num/den
 * - den must be nonzero
 * - returns a negative number if r1 < num/den
 * - returns 0 if r1 = num/den
 * - returns a positive number if r1 > num/den
 */
extern int q_cmp_int32(const rational_t *r1, int32_t num, uint32_t den);
extern int q_cmp_int64(const rational_t *r1, int64_t num, uint64_t den);


/*
 * Variants of q_cmp:
 * - q_le(r1, r2) is nonzero iff r1 <= r2
 * - q_lt(r1, r2) is nonzero iff r1 < r2
 * - q_gt(r1, r2) is nonzero iff r1 > r2
 * - q_ge(r1, r2) is nonzero iff r1 >= r2
 * - q_eq(r1, r2) is nonzero iff r1 = r2
 * - q_neq(r1, r2) is nonzero iff r1 != r2
 */
static inline bool q_le(const rational_t *r1, const rational_t *r2) {
  return q_cmp(r1, r2) <= 0;
}

static inline bool q_lt(const rational_t *r1, const rational_t *r2) {
  return q_cmp(r1, r2) < 0;
}

static inline bool q_ge(const rational_t *r1, const rational_t *r2) {
  return q_cmp(r1, r2) >= 0;
}

static inline bool q_gt(const rational_t *r1, const rational_t *r2) {
  return q_cmp(r1, r2) > 0;
}

static inline bool q_eq(const rational_t *r1, const rational_t *r2) {
  return q_cmp(r1, r2) == 0;
}

static inline bool q_neq(const rational_t *r1, const rational_t *r2) {
  return q_cmp(r1, r2) != 0;
}


/*
 * Check whether r1 and r2 are opposite (i.e., r1 + r2 = 0)
 */
extern bool q_opposite(const rational_t *r1, const rational_t *r2);


/*
 * Tests on rational r
 */
static inline bool q_is_zero(const rational_t *r) {
  return is_ratgmp(r) ? mpq_is_zero(get_gmp(r)) : r->s.num == 0;
}

static inline bool q_is_nonzero(const rational_t *r) {
  return is_ratgmp(r) ? mpq_is_nonzero(get_gmp(r)) : r->s.num != 0;
}

static inline bool q_is_one(const rational_t *r) {
  return (r->s.den == ONE_DEN && r->s.num == 1) ||
    (is_ratgmp(r) && mpq_is_one(get_gmp(r)));
}

static inline bool q_is_minus_one(const rational_t *r) {
  return (r->s.den == ONE_DEN && r->s.num == -1) ||
    (is_ratgmp(r) && mpq_is_minus_one(get_gmp(r)));
}

static inline bool q_is_pos(const rational_t *r) {
  return (is_rat32(r) ?  r->s.num > 0 : mpq_is_pos(get_gmp(r)));
}

static inline bool q_is_nonneg(const rational_t *r) {
  return (is_rat32(r) ?  r->s.num >= 0 : mpq_is_nonneg(get_gmp(r)));
}

static inline bool q_is_neg(const rational_t *r) {
  return (is_rat32(r) ?  r->s.num < 0 : mpq_is_neg(get_gmp(r)));
}

static inline bool q_is_nonpos(const rational_t *r) {
  return (is_rat32(r) ?  r->s.num <= 0 : mpq_is_nonpos(get_gmp(r)));
}

static inline bool q_is_integer(const rational_t *r) {
  return (is_rat32(r) && r->s.den == ONE_DEN) || (is_ratgmp(r) && mpq_is_integer(get_gmp(r)));
}



/*
 * DIVISIBILITY TESTS
 */

/*
 * Check whether r1 divides r2: both must be integers
 * - r1 must be non-zero
 * - side effect: r1 is normalized
 */
extern bool q_integer_divides(rational_t *r1, const rational_t *r2);


/*
 * General divisibility check: return true iff r2/r1 is an integer
 * - r1 must be non-zero
 */
extern bool q_divides(const rational_t *r1, const rational_t *r2);


/*
 * SMT2 version:
 * - if t1 is non-zero, return true iff (r2/r1) is an integer
 * - if t1 is zero, return true iff r2 is zero
 */
extern bool q_smt2_divides(const rational_t *r1, const rational_t *r2);


/*
 * Tests on integer rational r mod m
 */
static inline bool q_is_zero_mod(const rational_t *r, const rational_t *m) {
  assert(q_is_integer(r) && q_is_integer(m) && q_is_pos(m));
  return q_integer_divides((rational_t *)m, r);
}

static inline bool q_is_nonzero_mod(const rational_t *r, const rational_t *m) {
  return !q_is_zero_mod(r, m);
}


/*
 * CONVERSIONS TO INTEGERS
 */

/*
 * Check whether r is a small integer (use with care: this
 * ignores the case where r is a small integer that happens
 * to be represented as a gmp rational).
 * Call q_normalize(r) first if there's a doubt.
 */
static inline bool q_is_smallint(rational_t *r) {  
  return r->s.den == ONE_DEN;
}

/*
 * Convert r to an integer, provided q_is_smallint(r) is true
 */
static inline int32_t q_get_smallint(rational_t *r) {
  return get_num(r);
}


/*
 * Conversions: all functions attempt to convert r into an integer or
 * a pair of integers (num/den). If the conversion is not possible
 * the functions return false. Otherwise, the result is true and the
 * value is returned in v or num/den.
 */
extern bool q_get32(rational_t *r, int32_t *v);
extern bool q_get64(rational_t *r, int64_t *v);
extern bool q_get_int32(rational_t *r, int32_t *num, uint32_t *den);
extern bool q_get_int64(rational_t *r, int64_t *num, uint64_t *den);


/*
 * Similar to the conversion functions above but just check
 * whether the conversions are possible.
 */
extern bool q_is_int32(rational_t *r);   // r is a/1 where a is int32
extern bool q_is_int64(rational_t *r);   // r is a/1 where a is int64
extern bool q_fits_int32(rational_t *r); // r is a/b where a is int32, b is uint32
extern bool q_fits_int64(rational_t *r); // r is a/b where a is int64, b is uint64



/*
 * Size estimate
 * - this returns approximately the number of bits to represent r's numerator
 * - this may not be exact (typically rounded up to a multiple of 32)
 * - also if r is really really big, this function may return
 *   UINT32_MAX (not very likely!)
 */
extern uint32_t q_size(rational_t *r);


/*
 * CONVERSION TO GMP OBJECTS
 */

/*
 * Store r into the GMP integer z.
 * - return false if r is not a integer, true otherwise
 */
extern bool q_get_mpz(rational_t *r, mpz_t z);


/*
 * Store r into q
 */
extern void q_get_mpq(rational_t *r, mpq_t q);


/*
 * Convert to a floating point number
 */
extern double q_get_double(rational_t *r);



/*
 * PRINT
 */

/*
 * Print r on stream f.
 * q_print_abs prints the absolute value
 */
extern void q_print(FILE *f, const rational_t *r);
extern void q_print_abs(FILE *f, const rational_t *r);


/*
 * HASH FUNCTION
 */

/*
 * Hash functions: return a hash of numerator or denominator.
 * - hash_numerator(r) = numerator MOD bigprime
 * - hash_denominator(r) = denominator MOD bigprime
 * where bigprime is the largest prime number smaller than 2^32.
 */
extern uint32_t q_hash_numerator(const rational_t *r);
extern uint32_t q_hash_denominator(const rational_t *r);
extern void q_hash_decompose(const rational_t *r, uint32_t *h_num, uint32_t *h_den);




/*
 * RATIONAL ARRAYS
 */

#define MAX_RATIONAL_ARRAY_SIZE (UINT32_MAX/sizeof(rational_t))

/*
 * Create and initialize an array of n rationals.
 */
extern rational_t *new_rational_array(uint32_t n);

/*
 * Delete an array created by the previous function
 * - n must be the size of a
 */
extern void free_rational_array(rational_t *a, uint32_t n);





#endif /* __RATIONALS_H */
