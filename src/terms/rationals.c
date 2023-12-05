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
 * Operations on rational numbers
 * - rationals are represented as pairs of 32 bit integers
 *   or if they are too large as a pointer to a gmp rational.
 */

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>
#include <string.h>

#include <gmp.h>

#include "mt/yices_locks.h"
#include "mt/thread_macros.h"
#include "terms/rationals.h"
#include "terms/mpq_stores.h"
#include "utils/gcd.h"



static mpq_store_t  mpq_store;


/*
 *  String buffer for parsing.
 */
#ifdef THREAD_SAFE
static yices_lock_t string_buffer_lock;
#endif
static char* string_buffer = NULL;
static uint32_t string_buffer_length = 0;

/*
 * Print an error then abort on division by zero
 */
static void division_by_zero(void) {
  fprintf(stderr, "\nRationals: division by zero\n");
  abort();
}


/*
 * Initialize everything including the string lock
 * if we're in thread-safe mode.
 */
void init_rationals(void){
  init_mpq_aux();
  init_mpqstore(&mpq_store);
#ifdef THREAD_SAFE
  create_yices_lock(&string_buffer_lock);
#endif
  string_buffer = NULL;
  string_buffer_length = 0;
}


/*
 * Cleanup: free memory
 */
void cleanup_rationals(void){
  cleanup_mpq_aux();
  delete_mpqstore(&mpq_store);
#ifdef THREAD_SAFE
  destroy_yices_lock(&string_buffer_lock);
#endif
  safe_free(string_buffer);
}


/*************************
 *  MPQ ALLOCATION/FREE  *
 ************************/

/*
 * Allocates a new mpq object.
 */
static inline mpq_ptr new_mpq(void){
  return mpqstore_alloc(&mpq_store);
}


/*
 * Deallocates a new mpq object
 */
static void release_mpq(rational_t *r){
  assert(is_ratgmp(r));
  mpqstore_free(&mpq_store, get_gmp(r));
}


/*
 * Free mpq number attached to r if any, then set r to 0/1.
 * Must be called before r is deleted to prevent memory leaks.
 */
void q_clear(rational_t *r) {
  if (is_ratgmp(r)) {
    release_mpq(r);
  }
  r->s.num = 0;
  r->s.den = ONE_DEN;
}



/*******************
 *  NORMALIZATION  *
 ******************/

/*
 * Bounds on numerator and denominators.
 *
 * a/b can be safely stored as a pair (int32_t/uint32_t)
 * if MIN_NUMERATOR <= a <= MAX_NUMERATOR
 * and 1 <= b <= MAX_DENOMINATOR
 *
 * otherwise a/b must be stored as a gmp rational.
 *
 * The bounds are such that
 * - (a/1)+(b/1), (a/1) - (b/1) can be computed using
 *   32bit arithmetic without overflow.
 * - a/b stored as a pair implies -a/b and b/a can be stored
 *   as pairs too.
 */
#define MAX_NUMERATOR (INT32_MAX>>1)
#define MIN_NUMERATOR (-MAX_NUMERATOR)
#define MAX_DENOMINATOR MAX_NUMERATOR


/*
 * Store num/den in r
 */
static inline void set_rat32(rational_t *r, int32_t num, uint32_t den) {
  assert(MIN_NUMERATOR <= num && num <= MAX_NUMERATOR && den <= MAX_DENOMINATOR);
  r->s.den = den << 1;
  r->s.num = num;
}


/*
 * Normalization: construct rational a/b when
 * a and b are two 64bit numbers.
 * - b must be non-zero
 */
void q_set_int64(rational_t *r, int64_t a, uint64_t b) {
  uint64_t abs_a;
  mpq_ptr q;
  bool a_positive;

  assert(b > 0);

  if (a == 0 || (b == 1 && MIN_NUMERATOR <= a && a <= MAX_NUMERATOR)) {
    if (is_ratgmp(r)) {
      release_mpq(r);
    }
    set_rat32(r, a, 1);
    return;
  }

  // absolute value and sign of a.
  if (a >= 0) {
    abs_a = (uint64_t) a;
    a_positive = true;
  } else {
    abs_a = (uint64_t) - a; // Note: this works even when a = -2^63
    a_positive = false;
  }

  // abs_a and b are positive. remove powers of 2
  while (((abs_a | b) & 15) == 0) {
    abs_a >>= 4;
    b >>= 4;
  }
  switch ((abs_a | b) & 7) {
  case 0: abs_a >>= 3; b >>= 3; break;
  case 1: break;
  case 2: abs_a >>= 1; b >>= 1; break;
  case 3: break;
  case 4: abs_a >>= 2; b >>= 2; break;
  case 5: break;
  case 6: abs_a >>= 1; b >>= 1; break;
  case 7: break;
  }

  // abs_a and b are positive, and at least one of them is odd.
  // if abs_a <= 2 or b <= 2 then gcd = 1.
  if (abs_a > 2 && b > 2) {
    uint64_t a_1 = abs_a;
    uint64_t b_1 = b;

    // compute gcd of abs_a and b
    // loop invariant: abs_a is odd or b is odd (or both)
    for (;;) {
      if ((a_1 & 1) == 0) {
        a_1 >>= 1;
      } else if ((b_1 & 1) == 0) {
        b_1 >>= 1;
      } else if (a_1 >= b_1) {
        a_1 = (a_1 - b_1) >> 1;
        if (a_1 == 0) break;
      } else {
        b_1 = (b_1 - a_1) >> 1;
      }
    }

    // b_1 is gcd(abs_a, b)
    if (b_1 != 1) {
      abs_a /= b_1;
      b /= b_1;
    }
  }

  // abs_a and b are mutually prime and positive

  // restore a
  a = a_positive ? ((int64_t) abs_a) : - ((int64_t) abs_a);

  // assign to r
  if (abs_a <= MAX_NUMERATOR && b <= MAX_DENOMINATOR) {
    if (is_ratgmp(r)) {
      release_mpq(r);
    }
    set_rat32(r, (int32_t) a, (uint32_t) b);
  } else {
    if (is_ratgmp(r)) {
      q = get_gmp(r);
    } else {
      q = new_mpq();
      set_ratgmp(r, q);
    }
    mpq_set_int64(q, a, b);
  }
}



/*
 * Normalization: construct a/b when a and b are 32 bits
 */
void q_set_int32(rational_t *r, int32_t a, uint32_t b) {
  uint32_t abs_a;
  mpq_ptr q;
  bool a_positive;

  assert(b > 0);

  if (a == 0 || (b == 1 && MIN_NUMERATOR <= a && a <= MAX_NUMERATOR)) {
    if (is_ratgmp(r)) {
      release_mpq(r);
    }
    set_rat32(r, a, 1);
    return;
  }

  // absolute value and sign of a.
  if (a >= 0) {
    abs_a = (uint32_t) a;
    a_positive = true;
  } else {
    abs_a = (uint32_t) - a; // Note: this works even when a = -2^31
    a_positive = false;
  }

  // abs_a and b are positive. remove powers of 2
  while (((abs_a | b) & 15) == 0) {
    abs_a >>= 4;
    b >>= 4;
  }
  switch ((abs_a | b) & 7) {
  case 0: abs_a >>= 3; b >>= 3; break;
  case 1: break;
  case 2: abs_a >>= 1; b >>= 1; break;
  case 3: break;
  case 4: abs_a >>= 2; b >>= 2; break;
  case 5: break;
  case 6: abs_a >>= 1; b >>= 1; break;
  case 7: break;
  }

  // abs_a and b are positive, and at least one of them is odd.
  // if abs_a <= 2 or b <= 2 then gcd = 1.
  if (abs_a > 2 && b > 2) {
    uint32_t a_1 = abs_a;
    uint32_t b_1 = b;

    // compute gcd of abs_a and b
    // loop invariant: abs_a is odd or b is odd (or both)
    for (;;) {
      if ((a_1 & 1) == 0) {
        a_1 >>= 1;
      } else if ((b_1 & 1) == 0) {
        b_1 >>= 1;
      } else if (a_1 >= b_1) {
        a_1 = (a_1 - b_1) >> 1;
        if (a_1 == 0) break;

      } else {
        b_1 = (b_1 - a_1) >> 1;
      }
    }

    // b_1 is gcd(abs_a, b)
    if (b_1 != 1) {
      abs_a /= b_1;
      b /= b_1;
    }
  }

  // abs_a and b are mutually prime and positive

  // restore a
  a = a_positive ? ((int32_t) abs_a) : - ((int32_t) abs_a);

  // assign to r
  if (abs_a <= MAX_NUMERATOR && b <= MAX_DENOMINATOR) {
    if (is_ratgmp(r)) {
      release_mpq(r);
    }
    set_rat32(r, (int32_t) a, (uint32_t) b);
  } else {
    if (is_ratgmp(r)) {
      q = get_gmp(r);
    } else {
      q = new_mpq();
      set_ratgmp(r, q);
    }
    mpq_set_int32(q, a, b);
  }
}


/*
 * Construct r = a/1
 */
void q_set64(rational_t *r, int64_t a) {
  mpq_ptr q;

  if (MIN_NUMERATOR <= a && a <= MAX_NUMERATOR) {
    if (is_ratgmp(r)){ release_mpq(r); }
    set_rat32(r, (int32_t) a, 1);
  } else {
    if (!is_ratgmp(r)) {
      q = new_mpq();
      set_ratgmp(r, q);
    } else {
      q = get_gmp(r);
    }
    mpq_set_int64(q, a, 1);
  }
}

void q_set32(rational_t *r, int32_t a) {
  mpq_ptr q;

  if (MIN_NUMERATOR <= a && a <= MAX_NUMERATOR) {
    if (is_ratgmp(r)) { release_mpq(r); }
    set_rat32(r, a, 1);
  } else {
    if (!is_ratgmp(r)) {
      q = new_mpq();
      set_ratgmp(r, q);
    } else {
      q = get_gmp(r);
    }
    mpq_set_int32(q, a, 1);
  }
}



/*
 * Convert r to a gmp number.
 * r->num and r->den must have no common factor
 * and r->den must be non-zero.
 */
static void convert_to_gmp(rational_t *r) {
  mpq_ptr q;

  assert(!is_ratgmp(r));

  q = new_mpq();
  mpq_set_int32(q, get_num(r), get_den(r));
  set_ratgmp(r, q);
}


/*
 * Set r to a gmp with value = a.
 */
static void set_to_gmp64(rational_t *r, int64_t a) {
  mpq_ptr q;

  assert(!is_ratgmp(r));

  q = new_mpq();
  mpq_set_int64(q, a, 1);
  set_ratgmp(r, q);
}


/*****************
 *  ASSIGNMENTS  *
 ****************/


/*
 * Convert mpq to a pair of integers if possible.
 */
void q_normalize(rational_t *r) {
  mpq_ptr q;
  unsigned long den;
  long num;

  if (is_ratgmp(r)) {
    q = get_gmp(r);
    if (mpz_fits_ulong_p(mpq_denref(q)) && mpz_fits_slong_p(mpq_numref(q))) {
      num = mpz_get_si(mpq_numref(q));
      den = mpz_get_ui(mpq_denref(q));
      if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR && den <= MAX_DENOMINATOR) {
	      mpqstore_free(&mpq_store, q);
        set_rat32(r, (int32_t) num, (uint32_t) den);
      }
    }
  }
}

static void q_denormalize(rational_t *r) {
  mpq_ptr q;

  if (is_rat32(r)) {
    q = new_mpq();
    mpq_set_si(q, get_num(r), get_den(r));
    set_ratgmp(r, q);
  }
  assert(is_ratgmp(r));
}

/*
 * Prepare to assign an mpq number to r
 * - if r is not a mpq number, allocate it
 */
static inline void q_prepare(rational_t *r) {
  if (!is_ratgmp(r)) {
    set_ratgmp(r, new_mpq());
  }
}

/*
 * assign r:= z/1
 */
void q_set_mpz(rational_t *r, const mpz_t z) {
  mpq_ptr q;

  q_prepare(r);
  q = get_gmp(r);
  mpq_set_z(q, z);
  q_normalize(r);
}

/*
 * Copy q into r
 */
void q_set_mpq(rational_t *r, const mpq_t q) {
  mpq_ptr qt;

  q_prepare(r);
  qt = get_gmp(r);
  mpq_set(qt, q);
  q_normalize(r);
}

/*
 * Copy r2 into r1
 */
void q_set(rational_t *r1, const rational_t *r2) {
  mpq_ptr q1, q2;

  if (is_ratgmp(r2)) {
    q_prepare(r1);
    q1 = get_gmp(r1);
    q2 = get_gmp(r2);
    mpq_set(q1, q2);
  } else {
    if (is_ratgmp(r1)) {
      release_mpq(r1);
    }
    r1->s.num = r2->s.num;
    r1->s.den = r2->s.den;
  }
}

/*
 * Copy opposite of r2 into r1
 */
void q_set_neg(rational_t *r1, const rational_t *r2) {
  mpq_ptr q1, q2;

  if (is_ratgmp(r2)) {
    q_prepare(r1);
    q1 = get_gmp(r1);
    q2 = get_gmp(r2);
    mpq_neg(q1, q2);
  } else {
    if (is_ratgmp(r1)) {
      release_mpq(r1);
    }
    r1->s.num = - r2->s.num;
    r1->s.den = r2->s.den;
  }
}

/*
 * Copy the absolute value of r2 into r1
 */
void q_set_abs(rational_t *r1, const rational_t *r2) {
  if (is_ratgmp(r2)) {
    mpq_ptr q1;
    mpq_ptr q2;
    q_prepare(r1);
    q1 = get_gmp(r1);
    q2 = get_gmp(r2);
    mpq_abs(q1, q2);
  } else {
    if (is_ratgmp(r1)) {
      release_mpq(r1);
    }
    r1->s.den = r2->s.den;
    if (r2->s.num < 0) {
      r1->s.num = - r2->s.num;
    } else {
      r1->s.num = r2->s.num;
    }
  }
}

/*
 * Copy the numerator of r2 into r1
 * - r1 must be initialized
 * - r2 and r1 must be different objects
 */
void q_get_num(rational_t *r1, const rational_t *r2) {
  mpq_ptr q1, q2;
  long num;

  if (is_ratgmp(r2)) {
    q2 = get_gmp(r2);
    if (mpz_fits_slong_p(mpq_numref(q2))) {
      num = mpz_get_si(mpq_numref(q2));
      if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR) {
        if (is_ratgmp(r1)){ release_mpq(r1); }
        set_rat32(r1, num, 1);
        return;
      }
    }
    q_prepare(r1);
    q1 = get_gmp(r1);
    mpq_set_z(q1,  mpq_numref(q2));
  } else {
    if (is_ratgmp(r1)){ release_mpq(r1); }
    set_rat32(r1, get_num(r2), 1);
  }
}


/*
 * Copy the denominator of r2 into r1
 * - r1 must be initialized
 * - r1 and r2 must be different objects
 */
void q_get_den(rational_t *r1, const rational_t *r2) {
  mpq_ptr q1, q2;
  unsigned long den;

  if (is_ratgmp(r2)) {
    q2 = get_gmp(r2);
    if (mpz_fits_ulong_p(mpq_denref(q2))) {
      den = mpz_get_ui(mpq_denref(q2));
      if (den <= MAX_DENOMINATOR) {
        if (is_ratgmp(r1)){ release_mpq(r1); }
        r1->s.num = den;
        r1->s.den = ONE_DEN;
        return;
      }
    }
    q_prepare(r1);
    q1 = get_gmp(r1);
    mpq_set_z(q1, mpq_denref(q2));

  } else {
    if (is_ratgmp(r1)){ release_mpq(r1); }
    r1->s.num = get_den(r2);
    r1->s.den = ONE_DEN;
  }
}


/*******************************************
 *  PARSING: CONVERT STRINGS TO RATIONALS  *
 ******************************************/

/*
 * Resize string_buffer if necessary
 */
static void resize_string_buffer(uint32_t new_size) {
  uint32_t n;

  if (string_buffer_length < new_size) {
    /*
     * try to make buffer 50% larger
     * in principle the n += n >> 1 could overflow but
     * then (n < new_size) will be true
     * so n will be fixed to new_size.
     *
     * all this is very unlikely to happen in practice
     * (this would require extremely large strings).
     */
    n = string_buffer_length + 1;
    n += n >> 1;
    if (n < new_size) n = new_size;

    string_buffer = (char *) safe_realloc(string_buffer, n);
    string_buffer_length = n;
  }
}


/*
 * Assign q0 to r and try to convert to a pair of integers.
 * - q0 must be canonicalized
 * - return 0.
 */
static int q_set_q0(rational_t *r, mpq_t *q0) {
  mpq_ptr q;
  unsigned long den;
  long num;

  // try to store q0 as a pair num/den
  if (mpz_fits_ulong_p(mpq_denref(*q0)) && mpz_fits_slong_p(mpq_numref(*q0))) {
    num = mpz_get_si(mpq_numref(*q0));
    den = mpz_get_ui(mpq_denref(*q0));
    if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR && den <= MAX_DENOMINATOR) {
      if (is_ratgmp(r)){ release_mpq(r); }
      set_rat32(r, (int32_t) num, (uint32_t) den);
      return 0;
    }
  }

  // copy q0
  if (!is_ratgmp(r)) {
    q_prepare(r);
  }
  q = get_gmp(r);
  mpq_set(q, *q0);
  return 0;
}

/*
 * Conversion from a string in format supported by gmp:
 *   <+/->numerator/denominator or <+/->numerator
 * with numerator and denominator in base 10.
 * - returns -1 and leaves r unchanged if s is not in that format
 * - returns -2 and leaves r unchanged if the denominator is zero
 * - returns 0 otherwise
 */
int q_set_from_string(rational_t *r, const char *s) {
  int retval;
  mpq_t q0;

  mpq_init2(q0, 64);
  // GMP rejects an initial '+' so skip it
  if (*s == '+') s ++;
  if (mpq_set_str(q0, s, 10) < 0){
    retval = -1;
    goto clean_up;
  }
  if (mpz_sgn(mpq_denref(q0)) == 0){
    retval = -2; // the denominator is zero
    goto clean_up;
  }
  mpq_canonicalize(q0);
  retval = q_set_q0(r, &q0);

 clean_up:
  mpq_clear(q0);
  return retval;
}

/*
 * Conversion from a string using the given base.
 * Base is interpreted as in gmp: either 0 or an integer from 2 to 36.
 * If base = 0, then the base is determined independently for the
 * numerator and denominator from the first characters.
 * Prefixes  0x or 0b or 0 indicate base 16, 2, or 8,
 * otherwise, the base is 10.
 */
int q_set_from_string_base(rational_t *r, const char *s, int32_t base) {
  int retval;
  mpq_t q0;

  mpq_init2(q0, 64);


  // GMP rejects an initial '+' so skip it
  if (*s == '+') s ++;
  assert(0 == base || (2 <= base && base <= 36));
  if (mpq_set_str(q0, s, base) < 0){
    retval = -1;
    goto clean_up;
  }
  if (mpz_sgn(mpq_denref(q0)) == 0){
    retval = -2; // the denominator is zero
    goto clean_up;
  }
  mpq_canonicalize(q0);
  retval = q_set_q0(r, &q0);

 clean_up:

  mpq_clear(q0);
  return retval;

}


/*
 * Portable replacement for strtol that we use below to parse an exponent.
 * The input string must have a non-empty prefix of the form
 *     <optional sign> <digits>
 * without space.
 *
 * Portability issues with strtol
 * On some systems strtol("xxx", ..., 10) sets errno to EINVAL
 * On other systems strtol("xxx", ..., 10) returns 0 and doesn't set errno.
 */
static bool parse_exponent(const char *s, long *result) {
  unsigned long x, y;
  int digit;;
  char c;
  bool ok, positive;

  positive = true;
  ok = false;

  c = *s ++;
  if (c == '-') {
    positive = false;
    c = *s ++;
  } else if (c == '+') {
    c = *s ++;
  }

  x = 0;
  while ('0' <= c && c <= '9') {
    ok = true;
    digit = c - '0';
    y = 10*x + digit;
    if (y < x) {
      // overflow
      ok = false;
      break;
    }
    x = y;
    c = *s ++;
  }

  if (ok) {
    if (positive && x <= (unsigned long) LONG_MAX) {
      *result = (long) x;
      return true;
    }
    if (!positive && x <= (unsigned long) LONG_MIN) {
      *result = (long) (- x);
      return true;
    }
  }

  return false;
}


/*
 * Conversion from a string in a floating point format
 * The expected format is one of
 *   <optional sign> <integer part> . <fractional part>
 *   <optional sign> <integer part> <exp> <optional sign> <integer>
 *   <optional sign> <integer part> . <fractional part> <exp> <optional sign> <integer>
 *
 * Where <optional sign> is + or - and <exp> is either 'e' or 'E'
 *
 * - returns -1 and leaves r unchanged if the string is not in that format
 * - returns 0 otherwise
 */
static int _o_q_set_from_float_string(rational_t *r, const char *s) {
  size_t len;
  int frac_len, sign;
  long int exponent;
  char *b, c;
  int retval;
  mpz_t z0;
  mpq_t q0;

  mpz_init2(z0, 64);
  mpq_init2(q0, 64);

  len = strlen(s);
  if (len >= (size_t) UINT32_MAX) {
    // just to be safe if s is really long
    out_of_memory();
  }
  resize_string_buffer(len + 1);
  c = *s ++;

  // get sign
  sign = 1;
  if (c == '-') {
    sign = -1;
    c = * s++;
  } else if (c == '+') {
    c = * s ++;
  }

  // copy integer part into buffer.
  b = string_buffer;
  while ('0' <= c && c <= '9') {
    *b ++ = c;
    c = * s ++;
  }

  // copy fractional part and count its length
  frac_len = 0;
  if (c == '.') {
    c = *s ++;
    while ('0' <= c && c <= '9') {
      frac_len ++;
      *b ++ = c;
      c = * s ++;
    }
  }
  *b = '\0'; // end of buffer

  // check and read exponent
  exponent = 0;
  if (c == 'e' || c == 'E') {
    if (!parse_exponent(s, &exponent)) {
      retval =  -1;
      goto clean_up;
    }
  }

#if 0
  printf("--> Float conversion\n");
  printf("--> sign = %d\n", sign);
  printf("--> mantissa = %s\n", string_buffer);
  printf("--> frac_len = %d\n", frac_len);
  printf("--> exponent = %ld\n", exponent);
#endif

  mpq_set_ui(q0, 0, 1);

  // set numerator
  if (mpz_set_str(mpq_numref(q0), string_buffer, 10) < 0) {
    retval =  -1;
    goto clean_up;
  }
  if (sign < 0) {
    mpq_neg(q0, q0);
  }

  // multiply by 10^exponent
  exponent -= frac_len;
  if (exponent > 0) {
    mpz_ui_pow_ui(z0, 10, exponent);
    mpz_mul(mpq_numref(q0), mpq_numref(q0), z0);
  } else if (exponent < 0) {
    // this works even if exponent == LONG_MIN.
    mpz_ui_pow_ui(mpq_denref(q0), 10UL, (unsigned long) (- exponent));
    mpq_canonicalize(q0);
  }

  retval = q_set_q0(r, &q0);

 clean_up:

  mpz_clear(z0);
  mpq_clear(q0);

  return retval;

}

int q_set_from_float_string(rational_t *r, const char *s) {
  MT_PROTECT(int, string_buffer_lock, _o_q_set_from_float_string(r, s));
}


/****************
 *  ARITHMETIC  *
 ***************/

/*
 * Add r2 to r1
 */
void q_add(rational_t *r1, const rational_t *r2) {
  uint64_t den;
  int64_t num;
  mpq_ptr q1, q2;

  if (r1->s.den == ONE_DEN && r2->s.den == ONE_DEN) {
    assert(is_rat32(r2) && is_rat32(r1));
    r1->s.num += r2->s.num;
    if (r1->s.num < MIN_NUMERATOR || r1->s.num > MAX_NUMERATOR) {
      convert_to_gmp(r1);
    }
    return;
  }

  if (is_ratgmp(r2)) {
    if (!is_ratgmp(r1)) convert_to_gmp(r1) ;
    q1 = get_gmp(r1);
    q2 = get_gmp(r2);
    mpq_add(q1, q1, q2);
  } else if (is_ratgmp(r1)) {
    q1 = get_gmp(r1);
    mpq_add_si(q1, get_num(r2), get_den(r2));
  } else {
    den = get_den(r1) * ((uint64_t) get_den(r2));
    num = get_den(r1) * ((int64_t) get_num(r2)) + get_den(r2) * ((int64_t) get_num(r1));
    q_set_int64(r1, num, den);
  }
}

/*
 * Subtract r2 from r1
 */
void q_sub(rational_t *r1, const rational_t *r2) {
  uint64_t den;
  int64_t num;
  mpq_ptr q1, q2;

  if (r1->s.den == ONE_DEN && r2->s.den == ONE_DEN) {
    assert(is_rat32(r1)  &&  is_rat32(r2));
    r1->s.num -= r2->s.num;
    if (r1->s.num < MIN_NUMERATOR || r1->s.num > MAX_NUMERATOR) {
      convert_to_gmp(r1);
    }
    return;
  }

  if (is_ratgmp(r2)) {
    if (!is_ratgmp(r1)) convert_to_gmp(r1);
    q1 = get_gmp(r1);
    q2 = get_gmp(r2);
    mpq_sub(q1, q1, q2);
  } else if (is_ratgmp(r1)) {
    q1 = get_gmp(r1);
    mpq_sub_si(q1, get_num(r2), get_den(r2));
  } else {
    den = get_den(r1) * ((uint64_t) get_den(r2));
    num = get_den(r2) * ((int64_t) get_num(r1)) - get_den(r1) * ((int64_t)get_num(r2));
    q_set_int64(r1, num, den);
  }
}

/*
 * Negate r
 */
void q_neg(rational_t *r) {
  if (is_ratgmp(r)){
    mpq_ptr q = get_gmp(r);
    mpq_neg(q, q);
  } else {
    r->s.num = - r->s.num;
  }
}

/*
 * Invert r
 */
void q_inv(rational_t *r) {
  uint32_t abs_num;

  if (is_ratgmp(r)) {
    mpq_ptr q = get_gmp(r);
    mpq_inv(q, q);
  } else if (r->s.num < 0) {
    abs_num = (uint32_t) - r->s.num;
    set_rat32(r, - get_den(r), abs_num);
  } else if (r->s.num > 0) {
    abs_num = (uint32_t) r->s.num;
    set_rat32(r, get_den(r), abs_num);
  } else {
    division_by_zero();
  }
}

/*
 * Invert r mod m
 */
void q_inv_mod(rational_t *r, rational_t *mod) {
  assert(q_is_integer(r) && q_is_integer(mod) && q_is_pos(mod));

  rational_t tmp, *mm;
  if (is_rat32(mod)) {
    tmp = *mod; mm = &tmp;
    q_denormalize(mm);
  } else {
    mm = mod;
  }

  q_denormalize(r);
  assert(is_ratgmp(r) && is_ratgmp(mm));
  mpz_ptr z = get_gmp_num(r);
  mpz_ptr m = get_gmp_num(mm);
  mpz_invert(z, z, m);
  q_normalize(r);

  if (mm != mod)
    q_clear(mm);
}

/*
 * Multiply r1 by r2
 */
void q_mul(rational_t *r1, const rational_t *r2) {
  uint64_t den;
  int64_t num;
  mpq_ptr q1, q2;

  if (r1->s.den == ONE_DEN && r2->s.den == ONE_DEN) {
    assert(is_rat32(r1) && is_rat32(r2));
    num = r1->s.num * ((int64_t) r2->s.num);
    if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR) {
      r1->s.num = (int32_t) num;
    } else {
      set_to_gmp64(r1, num);
    }
    return;
  }

  if (is_ratgmp(r2)) {
    if (is_rat32(r1)) {
      convert_to_gmp(r1);
    }
    q1 = get_gmp(r1);
    q2 = get_gmp(r2);
    mpq_mul(q1, q1, q2);
  } else if (is_ratgmp(r1)){
    q1 = get_gmp(r1);
    mpq_mul_si(q1, get_num(r2), get_den(r2));
  } else {
    den = get_den(r1) * ((uint64_t) get_den(r2));
    num = get_num(r1) * ((int64_t) get_num(r2));
    q_set_int64(r1, num, den);
  }
}

/*
 * Divide r1 by r2
 */
void q_div(rational_t *r1, const rational_t *r2) {
  uint64_t den;
  int64_t num;
  mpq_ptr q1, q2;

  if (is_ratgmp(r2)) {
    if (is_rat32(r1)) convert_to_gmp(r1);
    q1 = get_gmp(r1);
    q2 = get_gmp(r2);
    mpq_div(q1, q1, q2);
  } else if (is_ratgmp(r1)){
    if (get_num(r2) == 0) {
      division_by_zero();
    } else {
      q1 = get_gmp(r1);
      mpq_div_si(q1, get_num(r2), get_den(r2));
    }

  } else if (get_num(r2) > 0) {
    den = get_den(r1) * ((uint64_t) get_num(r2));
    num = get_num(r1) * ((int64_t) get_den(r2));
    q_set_int64(r1, num, den);

  } else if (get_num(r2) < 0) {
    den = get_den(r1) * ((uint64_t) (- get_num(r2)));
    num = get_num(r1) * ( - ((int64_t) get_den(r2)));
    q_set_int64(r1, num, den);

  } else {
    division_by_zero();
  }
}

/*
 * Add r2 * r3 to  r1
 */
void q_addmul(rational_t *r1, const rational_t *r2, const rational_t *r3) {
  int64_t num;
  rational_t tmp;

  if (r1->s.den == ONE_DEN && r2->s.den == ONE_DEN && r3->s.den == ONE_DEN) {
    assert(is_rat32(r1) && is_rat32(r2) &&  is_rat32(r3));

    num = get_num(r1) + get_num(r2) * ((int64_t) get_num(r3));
    if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR) {
      r1->s.num = (int32_t) num;
    } else {
      set_to_gmp64(r1, num);
    }
    return;
  }

  q_init(&tmp);
  q_set(&tmp, r2);
  q_mul(&tmp, r3);
  q_add(r1, &tmp);
  q_clear(&tmp);
}


/*
 * Subtract r2 * r3 from r1
 */
void q_submul(rational_t *r1, const rational_t *r2, const rational_t *r3) {
  int64_t num;
  rational_t tmp;

  if (r1->s.den == ONE_DEN && r2->s.den == ONE_DEN && r3->s.den == ONE_DEN) {
    assert(is_rat32(r1) && is_rat32(r2) &&  is_rat32(r3));

    num = get_num(r1) - get_num(r2) * ((int64_t) get_num(r3));
    if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR) {
      r1->s.num = (int32_t) num;
    } else {
      set_to_gmp64(r1, num);
    }
    return;
  }

  q_init(&tmp);
  q_set(&tmp, r2);
  q_mul(&tmp, r3);
  q_sub(r1, &tmp);
  q_clear(&tmp);
}

/*
 * Increment: add one to r1
 */
void q_add_one(rational_t *r1) {
  mpq_ptr q;

  if (is_ratgmp(r1)) {
    q = get_gmp(r1);
    mpz_add(mpq_numref(q), mpq_numref(q), mpq_denref(q));
  } else {
    r1->s.num += get_den(r1);
    if (r1->s.num > MAX_NUMERATOR) {
      convert_to_gmp(r1);
    }
  }
}

/*
 * Decrement: subtract one from r1
 */
void q_sub_one(rational_t *r1) {
  mpq_ptr q;

  if (is_ratgmp(r1)) {
    q = get_gmp(r1);
    mpz_sub(mpq_numref(q), mpq_numref(q), mpq_denref(q));
  } else {
    r1->s.num -= get_den(r1);
    if (r1->s.num < MIN_NUMERATOR) {
      convert_to_gmp(r1);
    }
  }
}



/***********************
 *  CEILING AND FLOOR  *
 **********************/


// set r to floor(r);
void q_floor(rational_t *r) {
  int32_t n;

  if (q_is_integer(r)) return;

  if (is_ratgmp(r)) {
    mpq_ptr q = get_gmp(r);
    mpz_fdiv_q(mpq_numref(q), mpq_numref(q), mpq_denref(q));
    mpz_set_ui(mpq_denref(q), 1UL);
  } else {
    n = r->s.num / (int32_t) get_den(r);
    if (r->s.num < 0) n --;
    set_rat32(r, n, 1);
  }
}

// set r to ceil(r)
void q_ceil(rational_t *r) {
  int32_t n;

  if (q_is_integer(r)) return;

  if (is_ratgmp(r)) {
    mpq_ptr q = get_gmp(r);
    mpz_cdiv_q(mpq_numref(q), mpq_numref(q), mpq_denref(q));
    mpz_set_ui(mpq_denref(q), 1UL);
  } else {
    n = r->s.num / (int32_t) get_den(r);
    if (r->s.num > 0) n ++;
    set_rat32(r, n, 1);
  }
}



/*******************
 *  EXPONENTATION  *
 ******************/

/*
 * Store r1 * (r2 ^ n) into r1
 */
void q_mulexp(rational_t *r1, const rational_t *r2, uint32_t n) {
  rational_t aux;

  if (n <= 3) {
    // small exponent:
    switch (n) {
    case 3: q_mul(r1, r2);
    case 2: q_mul(r1, r2);
    case 1: q_mul(r1, r2);
    case 0: break; // do nothing
    }

  } else {
    q_init(&aux);
    q_set(&aux, r2);

    // compute r1 * aux^n
    for (;;) {
      assert(n > 0);
      if ((n & 1) != 0) {
        q_mul(r1, &aux);
      }
      n >>= 1;
      if (n == 0) break;
      q_mul(&aux, &aux); // this should work
    }

    q_clear(&aux);
  }
}

/*****************
 *  LCM and GCD  *
 ****************/

/*
 * Get the absolute value of x (converted to uint32_t)
 */
static inline uint32_t abs32(int32_t x) {
  return (x >= 0) ? x : -x;
}

/*
 * Store lcm(r1, r2) into r1
 * - r1 and r2 must be integer
 * - the result is always positive
 */
void q_lcm(rational_t *r1, const rational_t *r2) {
  uint32_t a, b;
  uint64_t d;
  mpq_ptr q1, q2;

  if (is_rat32(r2)) {
    if (is_rat32(r1)) {
      // both r1 and r2 are 32bit integers
      a = abs32(r1->s.num);
      b = abs32(r2->s.num);
      d = ((uint64_t) a) * ((uint64_t) (b/gcd32(a, b)));
      if (d <= MAX_NUMERATOR) {
        set_rat32(r1, d, 1);
      } else {
        set_to_gmp64(r1, d);
      }
    } else {
      // r2 is 32bits, r1 is gmp
      b = abs32(r2->s.num);
      q1 = get_gmp(r1);
      mpz_lcm_ui(mpq_numref(q1), mpq_numref(q1), b);
    }
  } else {
    // r2 is a gmp rational
    if (is_rat32(r1)) convert_to_gmp(r1);
    q1 = get_gmp(r1);
    q2 = get_gmp(r2);
    mpz_lcm(mpq_numref(q1), mpq_numref(q1), mpq_numref(q2));
  }

  assert(q_is_pos(r1));
}


/*
 * Store gcd(r1, r2) into r1
 * - r1 and r2 must be integer and non-zero
 * - the result is positive
 */
void q_gcd(rational_t *r1, const rational_t *r2) {
  uint32_t a, b, d;
  mpq_ptr q1, q2;

  if (is_rat32(r2)) {
    if (is_rat32(r1)) {
      // r1 and r2 are small integers
      a = abs32(r1->s.num);
      b = abs32(r2->s.num);
      d = gcd32(a, b);
    } else {
      // r1 is gmp, r2 is a small integer
      b = abs32(r2->s.num);
      q1 = get_gmp(r1);
      d = mpz_gcd_ui(NULL, mpq_numref(q1), b);
      release_mpq(r1);
    }
    assert(d <= MAX_NUMERATOR);
    set_rat32(r1, d, 1);
  } else {
    if (is_rat32(r1)) {
      // r1 is a small integer, r2 is a gmp number
      a = abs32(r1->s.num);
      q2 = get_gmp(r2);
      d = mpz_gcd_ui(NULL, mpq_numref(q2), a);
      assert(d <= MAX_NUMERATOR);
      set_rat32(r1, d, 1);
    } else {
      // both are gmp numbers
      q1 = get_gmp(r1);
      q2 = get_gmp(r2);
      mpz_gcd(mpq_numref(q1), mpq_numref(q1), mpq_numref(q2));
    }
  }
}





/************************
 *  EUCLIDEAN DIVISION  *
 ***********************/

/*
 * Quotient/remainder in Euclidean division
 * - r1 and r2 must be integer
 * - r2 must be positive
 */
void q_integer_div(rational_t *r1, rational_t *r2) {
  int32_t n;
  mpq_ptr q1, q2;

  q_normalize(r2);

  if (is_rat32(r2)) {
    assert(r2->s.den == ONE_DEN && r2->s.num > 0);
    if (is_rat32(r1)) {
      // both r1 and r2 are small integers
      n = r1->s.num % r2->s.num;  // remainder: n has the same sign as r1 (or n == 0)
      r1->s.num /= r2->s.num;     // quotient: same sign as r1, rounded towards 0
      if (n < 0) {
        r1->s.num --;
      }
    } else {
      // r1 is gmp, r2 is a small integer
      q1 = get_gmp(r1);
      mpz_fdiv_q_ui(mpq_numref(q1), mpq_numref(q1), r2->s.num);
      assert(mpq_is_integer(q1));
    }
  } else {
    q2 = get_gmp(r2);
    assert(mpq_is_integer(q2) && mpq_sgn(q2) > 0);
    if (is_rat32(r1)) {
      /*
       * r1 is a small integer, r2 is a gmp rational
       * since r2 is normalized and positive, we have r2 > abs(r1)
       * so r1 div r2 = 0 if r1 >= 0 or -1 if r1 < 0
       */
      assert(r1->s.den == ONE_DEN);
      if (r1->s.num >= 0) {
        r1->s.num = 0;
      } else {
        r1->s.num = -1;
      }
    } else {
      // both r1 and r2 are gmp rationals
      q1 = get_gmp(r1);
      mpz_fdiv_q(mpq_numref(q1), mpq_numref(q1), mpq_numref(q2));
      assert(mpq_is_integer(q1));
    }
  }
}


/*
 * Assign the remainder of r1 divided by r2 to r1
 * - both r1 and r2 must be integer
 * - r2 must be positive
 */
void q_integer_rem(rational_t *r1, rational_t *r2) {
  int32_t n;
  mpq_ptr q1, q2;

  q_normalize(r2);

  if (is_rat32(r2)){
    assert(r2->s.den == ONE_DEN && r2->s.num > 0);
    if (is_rat32(r1)) {
      /*
       * both r1 and r2 are small integers
       * Note: the result of (r1->num % r2->num) has the same sign as r1->num
       */
      n = r1->s.num % r2->s.num;
      if (n < 0) {
        n += r2->s.num;
      }
      assert(0 <= n && n < r2->s.num);
      r1->s.num = n;
    } else {
      // r1 is gmp, r2 is a small integer
      q1 = get_gmp(r1);
      n = mpz_fdiv_ui(mpq_numref(q1), r2->s.num);
      assert(0 <= n && n <= MAX_NUMERATOR);
      release_mpq(r1);
      set_rat32(r1, n, 1);
    }
  } else {
    q2 = get_gmp(r2);

    assert(mpq_is_integer(q2) && mpq_sgn(q2) > 0);
    if (is_rat32(r1)) {
      /*
       * r1 is a small integer, r2 is a gmp rational
       * since r2 is normalized and positive, we have r2 > abs(r1)
       * so r1 mod r2 = r1 if r1 >= 0
       * or r1 mod r2 = (r2 + r1) if r1 < 0
       */
      assert(r1->s.den == ONE_DEN);
      if (r1->s.num < 0) {
        mpq_ptr q = new_mpq();
        mpq_set_si(q, r1->s.num, 1UL);
        mpz_add(mpq_numref(q), mpq_numref(q), mpq_numref(q2));
        set_ratgmp(r1, q);
        assert(mpq_is_integer(q) && mpq_sgn(q) > 0);
      }

    } else {
      // both r1 and r2 are gmp rationals
      q1 = get_gmp(r1);
      mpz_fdiv_r(mpq_numref(q1), mpq_numref(q1), mpq_numref(q2));
      assert(mpq_is_integer(q1));
    }
  }
}

/*
 * Check whether r1 divides r2
 *
 * Both r1 and r2 must be integers and r1 must be non-zero
 */
bool q_integer_divides(rational_t *r1, const rational_t *r2) {
  uint32_t aux;
  mpq_ptr q1, q2;

  q_normalize(r1);

  if (is_ratgmp(r1)) {
    if (is_ratgmp(r2)) {
      q1 = get_gmp(r1);
      q2 = get_gmp(r2);
      return mpz_divisible_p(mpq_numref(q2), mpq_numref(q1));
    } else {
      return false;  // abs(r1) > abs(r2) so r1 can't divide r2
    }

  } else {
    assert(r1->s.den == ONE_DEN);
    aux = abs32(r1->s.num);
    if (is_ratgmp(r2)) {
      q2 = get_gmp(r2);
      return mpz_divisible_ui_p(mpq_numref(q2), aux);
    } else {
      return abs32(r2->s.num) % aux == 0;
    }
  }
}

/*
 * Check whether r2/r1 is an integer
 * - r1 must be non-zero
 */
bool q_divides(const rational_t *r1, const rational_t *r2) {
  rational_t aux;
  bool divides;

  if (r1->s.den == ONE_DEN && (r1->s.num == 1 || r1->s.num == -1)) {
    assert(is_rat32(r1));
    // r1 is +1 or -1
    return true;
  }

  q_init(&aux);
  q_set(&aux, r2);
  q_div(&aux, r1);
  divides = q_is_integer(&aux);
  q_clear(&aux);

  return divides;
}


/***********************************
 *  SMT2 version of (divides x y)  *
 **********************************/

/*
 * (divides r1 r2) is (exist (n::int) r2 = n * r1)
 *
 * This is the same as q_divides(r1, r2) except that the
 * definition allows r1 to be zero. In this case,
 *  (divides 0 r2) is (r2 == 0)
 */
bool q_smt2_divides(const rational_t *r1, const rational_t *r2) {
  if (q_is_zero(r1)) {
    return q_is_zero(r2);
  } else {
    return q_divides(r1, r2);
  }
}





/**********************
 *  GENERALIZED LCM   *
 *********************/

/*
 * This computes the LCM of r1 and r2 for arbitrary rationals:
 * - if r1 is (a1/b1) and r2 is (a2/b2) then the result is
 *    lcm(a1, a2)/gcd(b1, b2).
 * - the result is stored in r1
 */
void q_generalized_lcm(rational_t *r1, rational_t *r2) {
  rational_t a1, b1;
  rational_t a2, b2;

  if (q_is_integer(r1) && q_is_integer(r2)) {
    q_lcm(r1, r2);
  } else {
    q_init(&a1);
    q_get_num(&a1, r1);
    q_init(&b1);
    q_get_den(&b1, r1);

    q_init(&a2);
    q_get_num(&a2, r2);
    q_init(&b2);
    q_get_den(&b2, r2);

    q_lcm(&a1, &a2); // a1 := lcm(a1, a2)
    q_gcd(&b1, &b2); // b1 := gcd(b1, b2)

    // copy the result in r1
    q_set(r1, &a1);
    q_div(r1, &b1);

    q_clear(&a1);
    q_clear(&b1);
    q_clear(&a2);
    q_clear(&b2);
  }
}


/*
 * This computes the GCD of r1 and r2 for arbitrary non-zero rationals:
 * - if r1 is (a1/b1) and r2 is (a2/b2) then the result is
 *    gcd(a1, a2)/lcm(b1, b2).
 * - the result is stored in r1
 */
void q_generalized_gcd(rational_t *r1, rational_t *r2) {
  rational_t a1, b1;
  rational_t a2, b2;

  if (q_is_integer(r1) && q_is_integer(r2)) {
    q_lcm(r1, r2);
  } else {
    q_init(&a1);
    q_get_num(&a1, r1);
    q_init(&b1);
    q_get_den(&b1, r1);

    q_init(&a2);
    q_get_num(&a2, r2);
    q_init(&b2);
    q_get_den(&b2, r2);

    q_gcd(&a1, &a2); // a1 := gcd(a1, a2)
    q_lcm(&b1, &b2); // b1 := lcm(b1, b2)

    // copy the result in r1
    q_set(r1, &a1);
    q_div(r1, &b1);

    q_clear(&a1);
    q_clear(&b1);
    q_clear(&a2);
    q_clear(&b2);
  }
}

/**********************
 *  SMT2 DIV AND MOD  *
 *********************/

/*
 * SMT-LIB 2.0 definitions for div and mod:
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
void q_smt2_div(rational_t *q, const rational_t *x, const rational_t *y) {
  assert(q_is_nonzero(y));

  q_set(q, x);
  q_div(q, y); // q := x/y
  if (q_is_pos(y)) {
    q_floor(q);  // round down
  } else {
    q_ceil(q);  // round up
  }
}

/*
 * For debugging: check that 0 <= r < abs(y)
 */
#ifndef NDEBUG
static bool plausible_mod(const rational_t *r, const rational_t *y) {
  rational_t aux;
  bool ok;

  assert(q_is_nonzero(y));

  q_init(&aux);
  if (q_is_pos(y)) {
    q_set(&aux, y);
  } else {
    q_set_neg(&aux, y);
  }
  q_normalize(&aux);

  ok = q_is_nonneg(r) && q_lt(r, &aux);

  q_clear(&aux);

  return ok;
}
#endif


void q_smt2_mod(rational_t *q, const rational_t *x, const rational_t *y) {
  assert(q_is_nonzero(y));

  q_smt2_div(q, x, y); // q := (div x y)
  q_mul(q, y);         // q := y * (div x y)
  q_sub(q, x);         // q := - x + y * (div x y)
  q_neg(q);            // q := x - y * (div x y) = (mod x y)

  assert(plausible_mod(q, y));
}


/*****************
 *  COMPARISONS  *
 ****************/

/*
 * Compare r1 and r2
 * - returns a negative number if r1 < r2
 * - returns 0 if r1 = r2
 * - returns a positive number if r1 > r2
 */
int q_cmp(const rational_t *r1, const rational_t *r2) {
  int64_t num;
  mpq_ptr q1, q2;

  if (r1->s.den == ONE_DEN && r2->s.den == ONE_DEN) {
    assert(is_rat32(r1) && is_rat32(r2));
    return r1->s.num - r2->s.num;
  }

  if (is_ratgmp(r1)) {
    if (is_ratgmp(r2)) {
      q1 = get_gmp(r1);
      q2 = get_gmp(r2);
      return mpq_cmp(q1, q2);
    } else {
      q1 = get_gmp(r1);
      return mpq_cmp_si(q1, get_num(r2), get_den(r2));
    }
  } else {
    if (is_ratgmp(r2)) {
      q2 = get_gmp(r2);
      return - mpq_cmp_si(q2, get_num(r1), get_den(r1));
    } else {
      num = get_den(r2) * ((int64_t) get_num(r1)) - get_den(r1) * ((int64_t) get_num(r2));
      return (num < 0 ? -1 : (num > 0));
    }
  }
}

/*
 * Compare r1 and num/den
 */
int q_cmp_int32(const rational_t *r1, int32_t num, uint32_t den) {
  int64_t nn;
  mpq_ptr q1;

  if (is_ratgmp(r1)) {
    q1 = get_gmp(r1);
    return mpq_cmp_si(q1, num, den);
  } else {
    nn = den * ((int64_t) r1->s.num) - get_den(r1) * ((int64_t) num);
    return (nn < 0 ? -1 : (nn > 0));
  }
}

int q_cmp_int64(const rational_t *r1, int64_t num, uint64_t den) {
  int retval;
  mpq_ptr q1;
  mpq_t q0;

  mpq_init2(q0, 64);
  mpq_set_int64(q0, num, den);
  mpq_canonicalize(q0);
  if (is_ratgmp(r1)){
    q1 = get_gmp(r1);
    retval = mpq_cmp(q1, q0);
  } else {
    retval = - mpq_cmp_si(q0, r1->s.num, get_den(r1));
  }
  mpq_clear(q0);
  return retval;
}

/*
 * Check whether r1 and r2 are opposite
 */
bool q_opposite(const rational_t *r1, const rational_t *r2) {
  rational_t aux;
  bool result;

  if (r1->s.den == ONE_DEN && r2->s.den == ONE_DEN) {
    assert(is_rat32(r1) && is_rat32(r2));
    return r1->s.num + r2->s.num == 0;
  }

  q_init(&aux);
  q_set(&aux, r1);
  q_add(&aux, r2);
  result = q_is_zero(&aux);
  q_clear(&aux);

  return result;
}


/***********************************************
 *  CONVERSIONS FROM RATIONALS TO OTHER TYPES  *
 **********************************************/

/*
 * Convert r to a 32bit signed integer
 * - return false if r is not an integer or does not fit in 32 bits
 */
bool q_get32(rational_t *r, int32_t *v) {
  uint32_t d;
  mpq_ptr q;

  if (r->s.den == ONE_DEN) {
    assert(is_rat32(r));
    *v = r->s.num;
    return true;
  } else if (is_ratgmp(r)){
    q = get_gmp(r);
    if (mpq_fits_int32(q)) {
      mpq_get_int32(q, v, &d);
      return d == 1;
    }
  }
  return false;
}

/*
 * Convert r to a 64bit signed integer v
 * - return false if r is not an integer or does not fit in 64bits
 */
bool q_get64(rational_t *r, int64_t *v) {
  uint64_t d;
  mpq_ptr q;

  if (r->s.den == ONE_DEN) {
    assert(is_rat32(r));
    *v = r->s.num;
    return true;
  } else if (is_ratgmp(r)){
    q = get_gmp(r);
    if (mpq_fits_int64(q)) {
      mpq_get_int64(q, v, &d);
      return d == 1;
    }
  }
  return false;
}


/*
 * Convert r to a pair of 32 bit integers num/den
 * - return false if the numerator or denominator doesn't fit in 32bits
 */
bool q_get_int32(rational_t *r, int32_t *num, uint32_t *den) {
  mpq_ptr q;

  if (is_rat32(r)) {
    *num = get_num(r);
    *den = get_den(r);
    return true;
  } else {
    q = get_gmp(r);
    if (mpq_fits_int32(q)) {
      mpq_get_int32(q, num, den);
      return true;
    }
  }
  return false;
}


/*
 * Convert r to a pair of 64bit integers num/den
 * - return false if the numerator or denominator doesn't fit in 64bits
 */
bool q_get_int64(rational_t *r, int64_t *num, uint64_t *den) {
  mpq_ptr q;

  if (is_rat32(r)) {
    *num = get_num(r);
    *den = get_den(r);
    return true;
  } else {
    q = get_gmp(r);
    if (mpq_fits_int64(q)) {
      mpq_get_int64(q, num, den);
      return true;
    }
  }
  return false;
}


/*
 * Check whether r can be converted to a 32bit integer,
 * a 64bit integer, or two a pair num/den of 32bit or 64bit integers.
 */

bool q_is_int32(rational_t *r) {
  return (is_rat32(r) && r->s.den == ONE_DEN) || (is_ratgmp(r) && mpq_is_int32(get_gmp(r)));
}

bool q_is_int64(rational_t *r) {
  return (is_rat32(r) && r->s.den == ONE_DEN) || (is_ratgmp(r) && mpq_is_int64(get_gmp(r)));
}

bool q_fits_int32(rational_t *r) {
  return is_rat32(r) || mpq_fits_int32(get_gmp(r));
}

bool q_fits_int64(rational_t *r) {
  return is_rat32(r) || mpq_fits_int64(get_gmp(r));
}


/*
 * Size estimate
 * - r must be an integer
 * - this returns approximately the number of bits to represent r
 */
uint32_t q_size(rational_t *r) {
  size_t n;

  n = 32;
  if (is_ratgmp(r)) {
    n = mpz_size(mpq_numref(get_gmp(r))) * mp_bits_per_limb;
    if (n > (size_t) UINT32_MAX) {
      n = UINT32_MAX;
    }
  }
  return (uint32_t) n;
}

/*
 * Convert r to a GMP integer
 * - return false if r is not an integer
 */
bool q_get_mpz(rational_t *r, mpz_t z) {
  if (r->s.den == ONE_DEN) {
    assert(is_rat32(r));
    mpz_set_si(z, r->s.num);
    return true;
  } else if (is_ratgmp(r)){
    mpq_ptr q = get_gmp(r);
    if (mpq_is_integer(q)) {
      mpz_set(z, mpq_numref(q));
      return true;
    }
  }
  return false;
}

/*
 * Convert r to a GMP rational
 */
void q_get_mpq(rational_t *r, mpq_t q) {
  if (is_ratgmp(r)) {
    mpq_set(q, get_gmp(r));
  } else {
    mpq_set_int32(q, r->s.num, get_den(r));
  }
}

/*
 * Convert to a double
 */
double q_get_double(rational_t *r) {
  double retval;
  mpq_t q0;

  mpq_init2(q0, 64);
  q_get_mpq(r, q0);
  retval = mpq_get_d(q0);
  mpq_clear(q0);

  return retval;
}


/**************
 *  PRINTING  *
 *************/

/*
 * Print r
 */
void q_print(FILE *f, const rational_t *r) {
  if (is_ratgmp(r)) {
    mpq_out_str(f, 10, get_gmp(r));
  } else if (r->s.den != ONE_DEN) {
    fprintf(f, "%" PRId32 "/%" PRIu32, r->s.num, get_den(r));
  } else {
    fprintf(f, "%" PRId32, r->s.num);
  }
}

/*
 * Print r's absolute value
 */
void q_print_abs(FILE *f, const rational_t *r) {
  mpq_ptr q;
  int32_t abs_num;

  if (is_ratgmp(r)) {
    q = get_gmp(r);
    if (mpq_sgn(q) < 0) {
      mpq_neg(q, q);
      mpq_out_str(f, 10, q);
      mpq_neg(q, q);
    } else {
      mpq_out_str(f, 10, q);
    }
  } else {
    abs_num = r->s.num;
    if (abs_num < 0) abs_num = - abs_num;

    if (r->s.den != ONE_DEN) {
      fprintf(f, "%" PRId32 "/%" PRIu32, abs_num, get_den(r));
    } else {
      fprintf(f, "%" PRId32, abs_num);
    }
  }
}


/****************
 *  HASH CODES  *
 ***************/

/* largest prime less than 2^32 */
#define HASH_MODULUS 4294967291UL

/*
 *  we have  HASH_MODULUS > - MIN_NUMERATOR
 *   and HASH_MODULUS > MAX_NUMERATOR
 *
 * if MIN_NUMERATOR <= r->num <= MAX_NUMERATOR then
 * 1) if r->num >= 0 then r_num mod HASH_MODULUS = r_nun
 * 2) if r->num < 0 then r_num mod HASH_MODULUS = r_num + HASH_MODULUS
 *  so  ((uint32_t) r->num) + HASH_MODULUS = (2^32 + r->num) + HASH_MODULUS
 * gives the correct result.
 */
uint32_t q_hash_numerator(const rational_t *r) {
  if (is_ratgmp(r)) {
    return (uint32_t) mpz_fdiv_ui(mpq_numref(get_gmp(r)), HASH_MODULUS);
  } else if (r->s.num >= 0) {
    return (uint32_t) r->s.num;
  } else {
    return ((uint32_t) r->s.num) + ((uint32_t) HASH_MODULUS);
  }
}

uint32_t q_hash_denominator(const rational_t *r) {
  if (is_ratgmp(r)) {
    return (uint32_t) mpz_fdiv_ui(mpq_denref(get_gmp(r)), HASH_MODULUS);
  }
  return get_den(r);
}

void q_hash_decompose(const rational_t *r, uint32_t *h_num, uint32_t *h_den) {
  if (is_ratgmp(r)) {
    mpq_ptr q = get_gmp(r);
    *h_num = (uint32_t) mpz_fdiv_ui(mpq_numref(q), HASH_MODULUS);
    *h_den = (uint32_t) mpz_fdiv_ui(mpq_denref(q), HASH_MODULUS);
  } else if (r->s.num >= 0) {
    *h_num = (uint32_t) r->s.num;
    *h_den = get_den(r);
  } else {
    *h_num = ((uint32_t) r->s.num) + ((uint32_t) HASH_MODULUS);
    *h_den = get_den(r);
  }
}

/***********************
 *   RATIONAL ARRAYS   *
 **********************/

/*
 * Create and initialize an array of n rationals.
 */
rational_t *new_rational_array(uint32_t n) {
  rational_t *a;
  uint32_t i;

  if (n > MAX_RATIONAL_ARRAY_SIZE) {
    out_of_memory();
  }

  a = (rational_t *) safe_malloc(n * sizeof(rational_t));
  for (i=0; i<n; i++) {
    q_init(a + i);
  }

  return a;
}

/*
 * Delete an array created by the previous function
 */
void free_rational_array(rational_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    q_clear(a + i);
  }
  safe_free(a);
}
