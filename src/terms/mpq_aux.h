/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Extra functions for computing with gmp rational numbers.
 *
 * Functions already defined by gmp:
 * - mpq_set_si(mpq_t q, long num, unsigned long den)
 * - mpq_cmp_si(mpq_t q, long num, unsigned long den)
 *
 * New functions defined here:
 * - mpq_set_int64(mpq_t q, int64_t num, uint64_t den)
 * - mpq_add_si(mpq_t q, long num, unsigned long den)
 * - mpq_sub_si(mpq_t q, long num, unsigned long den)
 * - mpq_mul_si(mpq_t q, long num, unsigned long den)
 * - mpq_div_si(mpq_t q, long num, unsigned long den)
 *
 *
 * Initialization function:
 * - mpq_init2(mpq_t q, unsigned long n)
 *
 * Other short cuts:
 * - mpq_is_zero(mpq_t q)
 * - mpq_is_one(mpq_t q)
 * - mpq_is_minus_one(mpq_t q)
 * - mpq_is_pos(mpq_t q)
 * - mpq_is_nonneg(mpq_t q)
 * - mpq_is_neg(mpq_t q)
 * - mpq_is_nonpos(mpq_t q)
 * - mpq_is_integer(mpq_t q)
 */

#ifndef __MPQ_AUX_H
#define __MPQ_AUX_H

#include <stdint.h>
#include <stdbool.h>
#include <limits.h>

#include <gmp.h>


/*
 * Initialization: allocate and initialize the
 * global variables.
 */
extern void init_mpq_aux();


/*
 * Cleanup: delete global variables and free memory
 */
extern void cleanup_mpq_aux();



/*
 * Initialize q with enough room for numerator
 * and denominator with n bits. q is set to 0.
 *
 * Not to be used if q is already initialized.
 */
extern void mpq_init2(mpq_t q, unsigned long n);


/*
 * Add rational num/den to q.
 * - den must be non zero
 * - num and den must have no common factor
 */
extern void mpq_add_si(mpq_t q, long num, unsigned long den);

/*
 * Subtract num/den fromm q.
 * - num must be different from LONG_MIN
 * - den must be non-zero
 * - num and den must have no common factor
 */
static inline void mpq_sub_si(mpq_t q, long num, unsigned long den) {
  mpq_add_si(q, - num, den);
}


/*
 * Multiply q by num/den
 * - num must be different from LONG_MIN
 * - den must be non-zero
 * - num and den must have no common factor
 */
extern void mpq_mul_si(mpq_t q, long num, unsigned long den);

/*
 * Divide q by num/den
 * - num must be non-zero
 * - num and den must have no common factor
 */
extern void mpq_div_si(mpq_t q, long num, unsigned long den);



/*
 * Tests on a rational q
 */
static inline bool mpq_is_zero(mpq_t q) {
  return mpq_sgn(q) == 0;
}

static inline bool mpq_is_nonzero(mpq_t q) {
  return mpq_sgn(q) != 0;
}

static inline bool mpq_is_one(mpq_t q) {
  return mpq_cmp_ui(q, 1, 1) == 0;
}

static inline bool mpq_is_minus_one(mpq_t q) {
  return mpq_cmp_si(q, -1, 1) == 0;
}

static inline bool mpq_is_pos(mpq_t q) {
  return mpq_sgn(q) > 0;
}

static inline bool mpq_is_nonneg(mpq_t q) {
  return mpq_sgn(q) >= 0;
}

static inline bool mpq_is_neg(mpq_t q) {
  return mpq_sgn(q) < 0;
}

static inline bool mpq_is_nonpos(mpq_t q) {
  return mpq_sgn(q) <= 0;
}

static inline bool mpq_is_integer(mpq_t q) {
  return mpz_cmp_ui(mpq_denref(q), 1UL) == 0;
}



/*
 * Assignment functions:
 * - mpq_set_int32 stores num/den into q, where num and den are 32 bit integers.
 * - mpq_set_int64 stores num/den into q, where num and den are 64 bit integers.
 * For both functions:
 * - den must be non-zero
 * - if num and den have common factors, then q must be
 *   made canonical using mpq_canonicalize.
 *
 * Conversion functions:
 * - mpq_fits_int32 checks whether q can be written num/den with both 32bit integers.
 * - mpq_fits_int64 checks whether q can be written nun/den, where both are 64bit integers.
 * - mpq_get_int32 converts q to num/den where num and den are 32bit integers.
 *   The result is valid only if mpq_fits_int32(q) is true.
 * - mpq_get_int64 converts q to num/den where num and den are 64bit integers
 *   The result is correct only if mpq_fits_int64(q) is true.
 *
 * IMPORTANT: the conversion functions require q to be canonicalized.
 *
 * GMP provides conversions from mpz to signed and unsigned long.
 * Depending on the size of long we need to implement some code or we can
 * use the GMP functions directly.
 */
#if (ULONG_MAX == 4294967295UL)
// #warning "32 bits"
#define ULONG_SIZE 4
#elif (ULONG_MAX == 18446744073709551615UL)
// #warning "64 bits"
#define ULONG_SIZE 8
#else
#error "Could not determine size of long"
#endif



/*
 * Check whether q fits 64 or 32 bits
 */
extern bool mpq_fits_int64(mpq_t q);
extern bool mpq_fits_int32(mpq_t q);


/*
 * Check whether q is equal to a 32bit or 64bit signed integer:
 */
extern bool mpq_is_int64(mpq_t q);
extern bool mpq_is_int32(mpq_t q);


/*
 * Conversions to and from 64 bit numbers
 */
#if ULONG_SIZE == 4

extern void mpq_set_int64(mpq_t q, int64_t num, uint64_t den);
extern void mpq_get_int64(mpq_t q, int64_t *num, uint64_t *den);

#else /* ULONG_SIZE == 8 */

static inline void mpq_set_int64(mpq_t q, int64_t num, uint64_t den) {
  mpq_set_si(q, num, den);
}

static inline void mpq_get_int64(mpq_t q, int64_t *num, uint64_t *den) {
  *num = mpz_get_si(mpq_numref(q));
  *den = mpz_get_ui(mpq_denref(q));
}

#endif


/*
 * For 32bit numbers the GMP functions should always be fine
 */
static inline void mpq_set_int32(mpq_t q, int32_t num, uint32_t den) {
  mpq_set_si(q, num, den);
}

static inline void mpq_get_int32(mpq_t q, int32_t *num, uint32_t *den) {
  *num = mpz_get_si(mpq_numref(q));
  *den = mpz_get_ui(mpq_denref(q));
}



#endif /* __MPQ_AUX_H */
