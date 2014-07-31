/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * RATIONAL NUMBERS
 */

#ifndef __RATIONALS_H
#define __RATIONALS_H

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <gmp.h>

#include "terms/mpq_aux.h"



/*
 * INTERNAL REPRESENTATION
 */

/*
 * Rational = a pair of 32bit integers
 * - if den = 0 then num is an index into
 *   a global table of gmp rationals.
 */
typedef struct {
  int32_t num;
  uint32_t den;
} rational_t;


/*
 * Global bank of GMP numbers
 */
extern mpq_t *bank_q;

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
 * INITIALIZATION/DELETION
 */

/*
 * q_init must be called before any operation on a rational
 * q_clear must be called before the rational object is freed
 * q_clear can also be used to reset a rational to 0
 */

/*
 * Release internal gmp number of index i.
 */
extern void free_mpq(int32_t i);

/*
 * Get internal gmp number of index i.
 */
extern mpq_ptr get_mpq(int32_t i);

/*
 * Set r to 0/1, Must be called before any operation on r.
 */
static inline void q_init(rational_t *r) {
  r->num = 0;
  r->den = 1;
}

/*
 * Free mpq number attached to r if any, then set r to 0/1.
 * Must be called before r is deleted to prevent memory leaks.
 */
static inline void q_clear(rational_t *r) {
  if (r->den == 0) free_mpq(r->num);
  r->num = 0;
  r->den = 1;
}


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
  if (r->den == 0) free_mpq(r->num);
  r->num = 1;
  r->den = 1;
}

static inline void q_set_minus_one(rational_t *r) {
  if (r->den == 0) free_mpq(r->num);
  r->num = -1;
  r->den = 1;
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
  r1->num = r2->num;
  r1->den = r2->den;
  r2->num = 0;
  r2->den = 1;
}


/*
 * Swap values of r1 and r2
 */
static inline void q_swap(rational_t *r1, rational_t *r2) {
  int32_t n;
  uint32_t d;

  n = r1->num;
  d = r1->den;
  r1->num = r2->num;
  r1->den = r2->den;
  r2->num = n;
  r2->den = d;
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
 * TESTS: DO NOT MODIFY THE ARGUMENT(S)
 */

/*
 * Sign of r: q_sgn(r) = 0 if r = 0
 *            q_sgn(r) = +1 if r > 0
 *            q_sgn(r) = -1 if r < 0
 */
static inline int q_sgn(rational_t *r) {
  if (r->den == 0) {
    return mpq_sgn(bank_q[r->num]);
  } else {
    return (r->num < 0 ? -1 : (r->num > 0));
  }
}


/*
 * Compare r1 and r2:
 * - returns a negative number if r1 < r2
 * - returns 0 if r1 = r2
 * - returns a positive number if r1 > r2
 */
extern int q_cmp(rational_t *r1, rational_t *r2);


/*
 * Compare r1 and num/den
 * - den must be nonzero
 * - returns a negative number if r1 < num/den
 * - returns 0 if r1 = num/den
 * - returns a positive number if r1 > num/den
 */
extern int q_cmp_int32(rational_t *r1, int32_t num, uint32_t den);
extern int q_cmp_int64(rational_t *r1, int64_t num, uint64_t den);


/*
 * Variants of q_cmp:
 * - q_le(r1, r2) is nonzero iff r1 <= r2
 * - q_lt(r1, r2) is nonzero iff r1 < r2
 * - q_gt(r1, r2) is nonzero iff r1 > r2
 * - q_ge(r1, r2) is nonzero iff r1 >= r2
 * - q_eq(r1, r2) is nonzero iff r1 = r2
 * - q_neq(r1, r2) is nonzero iff r1 != r2
 */
static inline bool q_le(rational_t *r1, rational_t *r2) {
  return q_cmp(r1, r2) <= 0;
}

static inline bool q_lt(rational_t *r1, rational_t *r2) {
  return q_cmp(r1, r2) < 0;
}

static inline bool q_ge(rational_t *r1, rational_t *r2) {
  return q_cmp(r1, r2) >= 0;
}

static inline bool q_gt(rational_t *r1, rational_t *r2) {
  return q_cmp(r1, r2) > 0;
}

static inline bool q_eq(rational_t *r1, rational_t *r2) {
  return q_cmp(r1, r2) == 0;
}

static inline bool q_neq(rational_t *r1, rational_t *r2) {
  return q_cmp(r1, r2) != 0;
}


/*
 * Check whether r1 and r2 are opposite (i.e., r1 + r2 = 0)
 */
extern bool q_opposite(rational_t *r1, rational_t *r2);


/*
 * Tests on rational r
 */
static inline bool q_is_zero(rational_t *r) {
  return r->den == 0 ? mpq_is_zero(bank_q[r->num]) : r->num == 0;
}

static inline bool q_is_nonzero(rational_t *r) {
  return r->den == 0 ? mpq_is_nonzero(bank_q[r->num]) : r->num != 0;
}

static inline bool q_is_one(rational_t *r) {
  return (r->den == 1 && r->num == 1) ||
    (r->den == 0 && mpq_is_one(bank_q[r->num]));
}

static inline bool q_is_minus_one(rational_t *r) {
  return (r->den == 1 && r->num == -1) ||
    (r->den == 0 && mpq_is_minus_one(bank_q[r->num]));
}

static inline bool q_is_pos(rational_t *r) {
  return (r->den > 0 ?  r->num > 0 : mpq_is_pos(bank_q[r->num]));
}

static inline bool q_is_nonneg(rational_t *r) {
  return (r->den > 0 ?  r->num >= 0 : mpq_is_nonneg(bank_q[r->num]));
}

static inline bool q_is_neg(rational_t *r) {
  return (r->den > 0 ?  r->num < 0 : mpq_is_neg(bank_q[r->num]));
}

static inline bool q_is_nonpos(rational_t *r) {
  return (r->den > 0 ?  r->num <= 0 : mpq_is_nonpos(bank_q[r->num]));
}

static inline bool q_is_integer(rational_t *r) {
  return (r->den == 1) || (r->den == 0 && mpq_is_integer(bank_q[r->num]));
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
 * CONVERSIONS TO INTEGERS
 */

/*
 * Check whether r is a small integer (use with care: this
 * ignores the case where r is a small integer that happens
 * to be represented as a gmp rational).
 * Call q_normalize(r) first if there's a doubt.
 */
static inline bool q_is_smallint(rational_t *r) {
  return r->den == 1;
}

/*
 * Convert r to an integer, provided q_is_smallint(r) is true
 */
static inline int32_t q_get_smallint(rational_t *r) {
  return r->num;
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
extern void q_print(FILE *f, rational_t *r);
extern void q_print_abs(FILE *f, rational_t *r);


/*
 * HASH FUNCTION
 */

/*
 * Hash functions: return a hash of numerator or denominator.
 * - hash_numerator(r) = numerator MOD bigprime
 * - hash_denominator(r) = denominator MOD bigprime
 * where bigprime is the largest prime number smaller than 2^32.
 */
extern uint32_t q_hash_numerator(rational_t *r);
extern uint32_t q_hash_denominator(rational_t *r);
extern void q_hash_decompose(rational_t *r, uint32_t *h_num, uint32_t *h_den);




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
