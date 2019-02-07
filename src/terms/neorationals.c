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
 * or if they are too large as a pointer to a gmp rational.
 *
 */

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>
#include <string.h>

#include <errno.h>
#include <gmp.h>

#include "mt/yices_locks.h"
#include "mt/thread_macros.h"
#include "terms/neorationals.h"
#include "utils/gcd.h"


/*
 *
 *  String buffer for parsing.
 *
 */

static yices_lock_t string_buffer_lock;
static char* string_buffer = NULL;
static uint32_t string_buffer_length = 0;

static void division_by_zero(void) {
  fprintf(stderr, "\nRationals: division by zero\n");
  abort();
}


void init_neorationals(void){
  create_yices_lock(&string_buffer_lock);
  string_buffer = NULL;
  string_buffer_length = 0;
}


/*
 * Cleanup: free memory
 */
void cleanup_neorationals(void){
  destroy_yices_lock(&string_buffer_lock);
  safe_free(string_buffer);
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
#define MAX_DENOMINATOR (MAX_NUMERATOR>>1)  //IAM: did not lose sleep over this. Is it right though??

/*
 * Convert mpq to a pair of integers if possible.
 */
void neoq_normalize(neorational_t *r) {
  mpq_ptr q;
  unsigned long den;
  long num;

  if (is_ratgmp(r)) {
    q = (mpq_ptr)get_gmp(r);
    if (mpz_fits_ulong_p(mpq_denref(q)) && mpz_fits_slong_p(mpq_numref(q))) {
      num = mpz_get_si(mpq_numref(q));
      den = mpz_get_ui(mpq_denref(q));
      if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR && den <= MAX_DENOMINATOR) {
        mpq_clear(q);
        safe_free(q);
        r->s.num = (int32_t) num;
        r->s.den = (uint32_t) den;
      }
    }
  }
}



/*
 * Normalization: construct a/b when a and b are 32 bits
 */
void neoq_set_int32(neorational_t *r, int32_t a, uint32_t b) {
  uint32_t abs_a;
  mpq_t *q;
  bool a_positive;

  assert(b > 0);

  if (a == 0 || (b == 1 && MIN_NUMERATOR <= a && a <= MAX_NUMERATOR)) {
    if(is_ratgmp(r)){ release_mpq(r); }
    r->s.num = a;
    r->s.den = ONE_DEN;
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
    if(is_ratgmp(r)){ release_mpq(r); }
    r->s.num = (int32_t) a;
    r->s.den = ((uint32_t)b << 1);
  } else {
    if (is_ratgmp(r)) {
      q = get_gmp(r);
    } else {
      q = new_mpq();
      set_ratgmp(r, q);
    }
    mpq_set_int32(*q, a, b);
  }
}

/*
 * Normalization: construct rational a/b when
 * a and b are two 64bit numbers.
 * - b must be non-zero
 */
void neoq_set_int64(neorational_t *r, int64_t a, uint64_t b) {
  uint64_t abs_a;
  mpq_t *q;
  bool a_positive;

  assert(b > 0);

  if (a == 0 || (b == 1 && MIN_NUMERATOR <= a && a <= MAX_NUMERATOR)) {
    if(is_ratgmp(r)){ release_mpq(r); }
    r->s.num = a;
    r->s.den = ONE_DEN;
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

  // assing to r
  if (abs_a <= MAX_NUMERATOR && b <= MAX_DENOMINATOR) {
    if(is_ratgmp(r)){ release_mpq(r); }
    r->s.num = (int32_t) a;
    r->s.den = ((uint32_t)b << 1);
  } else {
    if (is_ratgmp(r)) {
      q = get_gmp(r);
    } else {
      q = new_mpq();
      set_ratgmp(r, q);
    }
    mpq_set_int64(*q, a, b);
  }
}

/*
 * Construct r = a/1
 */
void neoq_set32(neorational_t *r, int32_t a) {
  mpq_t * q;

  if (MIN_NUMERATOR <= a && a <= MAX_NUMERATOR) {
    if(is_ratgmp(r)){ release_mpq(r); }
    r->s.num = a;
    r->s.den = ONE_DEN;
  } else {
    if (!is_ratgmp(r)) {
      q = new_mpq();
      set_ratgmp(r, q);
    } else {
      q = get_gmp(r);
    }
    mpq_set_int32(*q, a, 1);
  }
}


void neoq_set64(neorational_t *r, int64_t a) {
  mpq_t * q;


  if (MIN_NUMERATOR <= a && a <= MAX_NUMERATOR) {
    if(is_ratgmp(r)){ release_mpq(r); }
    r->s.num = (int32_t) a;
    r->s.den = ONE_DEN;
  } else {
    if (!is_ratgmp(r)) {
      q = new_mpq();
      set_ratgmp(r, q);
    } else {
      q = get_gmp(r);
    }
    mpq_set_int64(*q, a, 1);
  }
}

/*
 * Convert r to a gmp number.
 * r->num and r->den must have no common factor
 * and r->den must be non-zero.
 */
static void neoconvert_to_gmp(neorational_t *r) {
  mpq_t *q;

  assert(!is_ratgmp(r));

  q = new_mpq();
  mpq_set_int32(*q, get_num(r), get_den(r));
  set_ratgmp(r, q);
}


/*
 * Set r to a gmp with value = a.
 */
static void neoset_to_gmp64(neorational_t *r, int64_t a) {
  mpq_t *q;

  assert(!is_ratgmp(r));

  q = new_mpq();
  mpq_set_int64(*q, a, 1);
  set_ratgmp(r, q);
}

/*
 * Prepare to assign an mpq number to r
 * - if r is not a mpq number, allocate it
 */
static inline void neoq_prepare(neorational_t *r) {
  if (!is_ratgmp(r)) {
    set_ratgmp(r, new_mpq());
  }
}

/*
 * assign r:= z/1
 */
void neoq_set_mpz(neorational_t *r, const mpz_t z) {
  mpq_t *q;
  neoq_prepare(r);
  q = get_gmp(r);
  mpq_set_z(*q, z);
  neoq_normalize(r);
}

/*
 * Copy q into r
 */
void neoq_set_mpq(neorational_t *r, const mpq_t q) {
  mpq_t *qt;
  neoq_prepare(r);
  qt = get_gmp(r);
  mpq_set(*qt, q);
  neoq_normalize(r);
}

/*
 * Copy r2 into r1
 */
void neoq_set(neorational_t *r1, const neorational_t *r2) {
  if (is_ratgmp(r2)) {
    mpq_t *q1;
    mpq_t *q2;
    neoq_prepare(r1);
    q1 = get_gmp(r1);
    q2 = get_gmp(r2);
    mpq_set(*q1, *q2);
  } else {
    if(is_ratgmp(r1)){ release_mpq(r1); }
    r1->s.num = r2->s.num;
    r1->s.den = r2->s.den;
  }
}

/*
 * Copy opposite of r2 into r1
 */
void neoq_set_neg(neorational_t *r1, const neorational_t *r2) {
  if (is_ratgmp((neorational_t *)r2)) {
    mpq_t *q1;
    mpq_t *q2;
    neoq_prepare(r1);
    q1 = get_gmp(r1);
    q2 = get_gmp((neorational_t *)r2);
    mpq_neg(*q1, *q2);
  } else {
    if(is_ratgmp(r1)){ release_mpq(r1); }
    r1->s.num = - r2->s.num;
    r1->s.den = r2->s.den;
  }
}

/*
 * Copy the absolute value of r2 into r1
 */
void neoq_set_abs(neorational_t *r1, const neorational_t *r2) {
  if (is_ratgmp((neorational_t *)r2)) {
    mpq_t *q1;
    mpq_t *q2;
    neoq_prepare(r1);
    q1 = get_gmp(r1);
    q2 = get_gmp((neorational_t *)r2);
    mpq_abs(*q1, *q2);
  } else {
    if(is_ratgmp(r1)){ release_mpq(r1); }
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
void neoq_get_num(neorational_t *r1, const neorational_t *r2) {
  mpq_t *q1;
  mpq_t *q2;
  long num;

  if (is_ratgmp((neorational_t *)r2)) {
    q2 = get_gmp((neorational_t *)r2);
    if (mpz_fits_slong_p(mpq_numref(*q2))) {
      num = mpz_get_si(mpq_numref(*q2));
      if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR) {
        if(is_ratgmp(r1)){ release_mpq(r1); }
        r1->s.num = num;
        r1->s.den = ONE_DEN;
        return;
      }
    }
    neoq_prepare(r1);
    q1 = get_gmp(r1);
    mpq_set_z(*q1,  mpq_numref(*q2));
  } else {
    if(is_ratgmp(r1)){ release_mpq(r1); }
    r1->s.num = r2->s.num;
    r1->s.den = ONE_DEN;
  }
}


/*
 * Copy the denominator of r2 into r1
 * - r1 must be initialized
 * - r1 and r2 must be different objects
 */
void neoq_get_den(neorational_t *r1, const neorational_t *r2) {
  mpq_t *q1;
  mpq_t *q2;
  unsigned long den;

  if (is_ratgmp((neorational_t *)r2)) {
    q2 = get_gmp((neorational_t *)r2);
    if (mpz_fits_ulong_p(mpq_denref(*q2))) {
      den = mpz_get_ui(mpq_denref(*q2));
      if (den <= MAX_DENOMINATOR) {
        if(is_ratgmp(r1)){ release_mpq(r1); }
        r1->s.num = den;
        r1->s.den = ONE_DEN;
        return;
      }
    }
    neoq_prepare(r1);
    q1 = get_gmp(r1);
    mpq_set_z(*q1, mpq_denref(*q2));

  } else {
    if(is_ratgmp(r1)){ release_mpq(r1); }
    r1->s.num = r2->s.den;
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
static int neoq_set_q0(neorational_t *r, mpq_t *q0) {
  mpq_t *q;
  unsigned long den;
  long num;

  // try to store q0 as a pair num/den
  if (mpz_fits_ulong_p(mpq_denref(*q0)) && mpz_fits_slong_p(mpq_numref(*q0))) {
    num = mpz_get_si(mpq_numref(*q0));
    den = mpz_get_ui(mpq_denref(*q0));
    if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR && den <= MAX_DENOMINATOR) {
      if(is_ratgmp(r)){ release_mpq(r); }
      r->s.num = (int32_t) num;
      r->s.den = (uint32_t) den << 1;
      return 0;
    }
  }

  // copy q0
  if (!is_ratgmp(r)) {
    neoq_prepare(r);
  }
  q = get_gmp(r);
  mpq_set(*q, *q0);
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
int neoq_set_from_string(neorational_t *r, const char *s) {
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
  retval = neoq_set_q0(r, &q0);

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
int neoq_set_from_string_base(neorational_t *r, const char *s, int32_t base) {
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
  retval = neoq_set_q0(r, &q0);

 clean_up:

  mpq_clear(q0);
  return retval;
  
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
static int _o_neoq_set_from_float_string(neorational_t *r, const char *s) {
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
    errno = 0;  // strtol sets errno on error
    exponent = strtol(s, (char **) NULL, 10);
    if (errno != 0){
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

  retval = neoq_set_q0(r, &q0);

 clean_up:
  
  mpz_clear(z0);
  mpq_clear(q0);

  return retval;

}

int neoq_set_from_float_string(neorational_t *r, const char *s) {
  MT_PROTECT(int, string_buffer_lock, _o_neoq_set_from_float_string(r, s));
}


/****************
 *  ARITHMETIC  *
 ***************/

/*
 * Add r2 to r1
 */
void neoq_add(neorational_t *r1, const neorational_t *r2) {
  uint64_t den;
  int64_t num;

  if (is_rat32(r1) && r1->s.den == ONE_DEN && is_rat32(r2) && r2->s.den == ONE_DEN) {
    r1->s.num += r2->s.num;
    if (r1->s.num < MIN_NUMERATOR || r1->s.num > MAX_NUMERATOR) {
      neoconvert_to_gmp(r1);
    }
    return;
  }

  if (is_ratgmp(r2)) {
    if (!is_ratgmp(r1)) neoconvert_to_gmp(r1) ;
    mpq_t *q1;
    mpq_t *q2;
    q1 = get_gmp(r1);
    q2 = get_gmp(r2);

    mpq_add(*q1, *q1, *q2);

  } else if (is_ratgmp(r1)) {
    mpq_t *q1;
    q1 = get_gmp(r1);
    mpq_add_si(*q1, get_num(r2), get_den(r2));

  } else {
    den = get_den(r1) * ((uint64_t) get_den(r2));
    num = get_den(r1) * ((int64_t) get_num(r2)) + get_den(r2) * ((int64_t) get_num(r1));
    neoq_set_int64(r1, num, den);
  }
}

/*
 * Subtract r2 from r1
 */
void neoq_sub(neorational_t *r1, const neorational_t *r2) {
  uint64_t den;
  int64_t num;

  if (is_rat32(r1) && r1->s.den == ONE_DEN && is_rat32(r2)&& r2->s.den == ONE_DEN) {
    r1->s.num -= r2->s.num;
    if (r1->s.num < MIN_NUMERATOR || r1->s.num > MAX_NUMERATOR) {
      neoconvert_to_gmp(r1);
    }
    return;
  }

  if (is_ratgmp(r2)) {
    if (!is_ratgmp(r1)) neoconvert_to_gmp(r1);
    mpq_t *q1;
    mpq_t *q2;

    q1 = get_gmp(r1);
    q2 = get_gmp(r2);

    mpq_sub(*q1, *q1, *q2);

  } else if (is_ratgmp(r1)) {
    mpq_t *q1;

    q1 = get_gmp(r1);
    mpq_sub_si(*q1, get_num(r2), get_den(r2));

  } else {
    den = get_den(r1) * ((uint64_t) get_den(r2));
    num = get_den(r2) * ((int64_t) get_num(r1)) - get_den(r1) * ((int64_t)get_num(r2));
    neoq_set_int64(r1, num, den);
  }
}

/*
 * Negate r
 */
void neoq_neg(neorational_t *r) {
  if (is_ratgmp(r)){
    mpq_t *q;

    q = get_gmp(r);
    mpq_neg(*q, *q);
  } else {
    r->s.num = - r->s.num;
  }
}

/*
 * Invert r    //IAM: this looks dodgey if num is big
 */
void neoq_inv(neorational_t *r) {
  uint32_t abs_num;

  if (is_ratgmp(r)) {
    mpq_t *q;

    q = get_gmp(r);
    mpq_inv(*q, *q);

  } else if (r->s.num < 0) {
    abs_num = (uint32_t) - r->s.num;
    r->s.num = (int32_t) - (r->s.den >> 1);
    r->s.den = abs_num << 1;

  } else if (r->s.num > 0) {
    abs_num = (uint32_t) r->s.num;
    r->s.num = (uint32_t) (r->s.den >> 1);
    r->s.den = abs_num << 1;

  } else {
    division_by_zero();
  }
}

/*
 * Multiply r1 by r2
 */
void neoq_mul(neorational_t *r1, const neorational_t *r2) {
  uint64_t den;
  int64_t num;

  if (is_rat32(r1) && r1->s.den == ONE_DEN && is_rat32(r2) && r2->s.den == ONE_DEN) {
    num = r1->s.num * ((int64_t) r2->s.num);
    if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR) {
      r1->s.num = (int32_t) num;
    } else {
      neoset_to_gmp64(r1, num);
    }
    return;
  }

  if (is_ratgmp(r2)) {
    mpq_t *q1;
    mpq_t *q2;

    if (is_rat32(r1)) neoconvert_to_gmp(r1);

    q1 = get_gmp(r1);
    q2 = get_gmp(r2);

    mpq_mul(*q1, *q1, *q2);

  } else if (is_ratgmp(r1)){
    mpq_t *q1;

    q1 = get_gmp(r1);
    mpq_mul_si(*q1, get_num(r2), get_den(r2));

  } else {
    den = get_den(r1) * ((uint64_t) get_den(r2));
    num = get_num(r1) * ((int64_t) get_num(r2));
    neoq_set_int64(r1, num, den);
  }
}

/*
 * Divide r1 by r2
 */
void neoq_div(neorational_t *r1, const neorational_t *r2) {
  uint64_t den;
  int64_t num;

  if (is_ratgmp(r2)) {
    mpq_t *q1;
    mpq_t *q2;

    if (is_rat32(r1)) neoconvert_to_gmp(r1);

    q1 = get_gmp(r1);
    q2 = get_gmp(r2);


    mpq_div(*q1, *q1, *q2);

  } else if (is_ratgmp(r1)){
    if (get_num(r2) == 0) {
      division_by_zero();
    } else {
      mpq_t *q1;

      q1 = get_gmp(r1);
      mpq_div_si(*q1, get_num(r2), get_den(r2));
    }

  } else if (get_num(r2) > 0) {
    den = get_den(r1) * ((uint64_t) get_num(r2));
    num = get_num(r1) * ((int64_t) get_den(r2));
    neoq_set_int64(r1, num, den);

  } else if (get_num(r2) < 0) {
    den = get_den(r1) * ((uint64_t) (- get_num(r2)));
    num = get_num(r1) * ( - ((int64_t) get_den(r2)));
    neoq_set_int64(r1, num, den);

  } else {
    division_by_zero();
  }
}

/*
 * Add r2 * r3 to  r1
 */
void neoq_addmul(neorational_t *r1, const neorational_t *r2, const neorational_t *r3) {
  int64_t num;
  neorational_t tmp;

  if (is_rat32(r1) && r1->s.den == ONE_DEN && is_rat32(r2) && r2->s.den == ONE_DEN && is_rat32(r3) && r3->s.den == ONE_DEN) {
    num = get_num(r1) + get_num(r2) * ((int64_t) get_num(r3));
    if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR) {
      r1->s.num = (int32_t) num;
    } else {
      neoset_to_gmp64(r1, num);
    }
    return;
  }

  neoq_init(&tmp);
  neoq_set(&tmp, r2);
  neoq_mul(&tmp, r3);
  neoq_add(r1, &tmp);
  neoq_clear(&tmp);
}


/*
 * Subtract r2 * r3 from r1
 */
void neoq_submul(neorational_t *r1, const neorational_t *r2, const neorational_t *r3) {
  int64_t num;
  neorational_t tmp;

  if (is_rat32(r1) && r1->s.den == ONE_DEN && is_rat32(r2) && r2->s.den == ONE_DEN && is_rat32(r3) && r3->s.den == ONE_DEN) {
    num = get_num(r1) - get_num(r2) * ((int64_t) get_num(r3));
    if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR) {
      r1->s.num = (int32_t) num;
    } else {
      neoset_to_gmp64(r1, num);
    }
    return;
  }

  neoq_init(&tmp);
  neoq_set(&tmp, r2);
  neoq_mul(&tmp, r3);
  neoq_sub(r1, &tmp);
  neoq_clear(&tmp);
}

/*
 * Increment: add one to r1
 */
void neoq_add_one(neorational_t *r1) {

  if (is_ratgmp(r1)) {
    mpq_t *q;

    q = get_gmp(r1);
    mpz_add(mpq_numref(*q), mpq_numref(*q), mpq_denref(*q));
  } else {
    r1->s.num += get_den(r1);
    if (r1->s.num > MAX_NUMERATOR) {
      neoconvert_to_gmp(r1);
    }
  }
}

/*
 * Decrement: subtract one from r1
 */
void neoq_sub_one(neorational_t *r1) {

  if (is_ratgmp(r1)) {
    mpq_t *q;

    q = get_gmp(r1);

    mpz_sub(mpq_numref(*q), mpq_numref(*q), mpq_denref(*q));
  } else {
    r1->s.num -= get_den(r1);
    if (r1->s.num < MIN_NUMERATOR) {
      neoconvert_to_gmp(r1);
    }
  }
}



/***********************
 *  CEILING AND FLOOR  *
 **********************/


// set r to floor(r);
void neoq_floor(neorational_t *r) {
  int32_t n;

  if (neoq_is_integer(r)) return;

  if (is_ratgmp(r)) {
    mpq_t *q;

    q = get_gmp(r);

    mpz_fdiv_q(mpq_numref(*q), mpq_numref(*q), mpq_denref(*q));
    mpz_set_ui(mpq_denref(*q), 1UL);
  } else {
    n = r->s.num / (int32_t) get_den(r);
    if (r->s.num < 0) n --;
    r->s.num = n;
    r->s.den = ONE_DEN;
  }
}

// set r to ceil(r)
void neoq_ceil(neorational_t *r) {
  int32_t n;

  if (neoq_is_integer(r)) return;

  if (is_ratgmp(r)) {
    mpq_t *q;

    q = get_gmp(r);

    mpz_cdiv_q(mpq_numref(*q), mpq_numref(*q), mpq_denref(*q));
    mpz_set_ui(mpq_denref(*q), 1UL);
  } else {
    n = r->s.num / (int32_t) get_den(r);
    if (r->s.num > 0) n ++;
    r->s.num = n;
    r->s.den = ONE_DEN;
  }
}



/*******************
 *  EXPONENTATION  *
 ******************/

/*
 * Store r1 * (r2 ^ n) into r1
 */
void neoq_mulexp(neorational_t *r1, const neorational_t *r2, uint32_t n) {
  neorational_t aux;

  if (n <= 3) {
    // small exponent:
    switch (n) {
    case 3: neoq_mul(r1, r2);
    case 2: neoq_mul(r1, r2);
    case 1: neoq_mul(r1, r2);
    case 0: break; // do nothing
    }

  } else {
    neoq_init(&aux);
    neoq_set(&aux, r2);

    // compute r1 * aux^n
    for (;;) {
      assert(n > 0);
      if ((n & 1) != 0) {
        neoq_mul(r1, &aux);
      }
      n >>= 1;
      if (n == 0) break;
      neoq_mul(&aux, &aux); // this should work
    }

    neoq_clear(&aux);
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
void neoq_lcm(neorational_t *r1, const neorational_t *r2) {
  uint32_t a, b;
  uint64_t d;
  mpq_t *q1;
  mpq_t *q2;

  if (is_rat32(r2)) {
    if (is_rat32(r1)) {
      // both r1 and r2 are 32bit integers
      a = abs32(r1->s.num);
      b = abs32(r2->s.num);
      d = ((uint64_t) a) * ((uint64_t) (b/gcd32(a, b)));
      if (d <= MAX_NUMERATOR) {
        r1->s.num = d;
        r1->s.den = ONE_DEN;
      } else {
        neoset_to_gmp64(r1, d);
      }
    } else {
      // r2 is 32bits, r1 is gmp
      b = abs32(r2->s.num);
      q1 = get_gmp(r1);
      mpz_lcm_ui(mpq_numref(*q1), mpq_numref(*q1), b);
    }
  } else {
    // r2 is a gmp rational
    if (is_rat32(r1)) neoconvert_to_gmp(r1);
    q1 = get_gmp(r1);
    q2 = get_gmp(r2);
    mpz_lcm(mpq_numref(*q1), mpq_numref(*q1), mpq_numref(*q2));
  }

  assert(neoq_is_pos(r1));
}


/*
 * Store gcd(r1, r2) into r1
 * - r1 and r2 must be integer and non-zero
 * - the result is positive
 */
void neoq_gcd(neorational_t *r1, const neorational_t *r2) {
  uint32_t a, b, d;  //IAM: isn't this bad bruno-style?
  mpq_t *q1;
  mpq_t *q2;

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
      d = mpz_gcd_ui(NULL, mpq_numref(*q1), b);
      release_mpq(r1);
    }
    assert(d <= MAX_NUMERATOR);
    r1->s.num = d;
    r1->s.den = ONE_DEN;
  } else {
    if (is_rat32(r1)) {
      // r1 is a small integer, r2 is a gmp number
      a = abs32(r1->s.num);
      q2 = get_gmp(r2);
      d = mpz_gcd_ui(NULL, mpq_numref(*q2), a);
      assert(d <= MAX_NUMERATOR);
      r1->s.num = d;
      r1->s.den = ONE_DEN;
    } else {
      // both are gmp numbers
      q1 = get_gmp(r1);
      q2 = get_gmp(r2);
      mpz_gcd(mpq_numref(*q1), mpq_numref(*q1), mpq_numref(*q2));
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
void neoq_integer_div(neorational_t *r1, neorational_t *r2) {
  int32_t n;
  mpq_t *q1;
  mpq_t *q2;

  neoq_normalize(r2);

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
      mpz_fdiv_q_ui(mpq_numref(*q1), mpq_numref(*q1), r2->s.num);
      assert(mpq_is_integer(*q1));
    }
  } else {
    q2 = get_gmp(r2);
    assert(mpq_is_integer(*q2) && mpq_sgn(*q2) > 0);
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
      mpz_fdiv_q(mpq_numref(*q1), mpq_numref(*q1), mpq_numref(*q2));
      assert(mpq_is_integer(*q1));
    }
  }
}


/*
 * Assign the remainder of r1 divided by r2 to r1
 * - both r1 and r2 must be integer
 * - r2 must be positive
 */
void neoq_integer_rem(neorational_t *r1, neorational_t *r2) {
  int32_t n;
  mpq_t *q1;
  mpq_t *q2;

  neoq_normalize(r2);

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
      n = mpz_fdiv_ui(mpq_numref(*q1), r2->s.num);
      assert(0 <= n && n <= MAX_NUMERATOR);
      release_mpq(r1);
      r1->s.num = n;
      r1->s.den = ONE_DEN;
    }
  } else {
    q2 = get_gmp(r2);

    assert(mpq_is_integer(*q2) && mpq_sgn(*q2) > 0);
    if (is_rat32(r1)) {
      /*
       * r1 is a small integer, r2 is a gmp rational
       * since r2 is normalized and positive, we have r2 > abs(r1)
       * so r1 mod r2 = r1 if r1 >= 0
       * or r1 mod r2 = (r2 + r1) if r1 < 0
       */
      assert(r1->s.den == ONE_DEN);
      if (r1->s.num < 0) {
        mpq_t *q = new_mpq();
        mpq_set_si(*q, r1->s.num, 1UL);
        mpz_add(mpq_numref(*q), mpq_numref(*q), mpq_numref(*q2));
        set_ratgmp(r1, q);
        assert(mpq_is_integer(*q) && mpq_sgn(*q) > 0);
      }

    } else {
      // both r1 and r2 are gmp rationals
      q1 = get_gmp(r1);
      mpz_fdiv_r(mpq_numref(*q1), mpq_numref(*q1), mpq_numref(*q2));
      assert(mpq_is_integer(*q1));
    }
  }
}

/*
 * Check whether r1 divides r2
 *
 * Both r1 and r2 must be integers and r1 must be non-zero
 */
bool neoq_integer_divides(neorational_t *r1, const neorational_t *r2) {
  uint32_t aux;
  mpq_t *q1;
  mpq_t *q2;

  neoq_normalize(r1);

  if (is_ratgmp(r1)) {
    if (is_ratgmp(r2)) {
      q1 = get_gmp(r1);
      q2 = get_gmp(r2);
      return mpz_divisible_p(mpq_numref(*q2), mpq_numref(*q1));
    } else {
      return false;  // abs(r1) > abs(r2) so r1 can't divide r2
    }

  } else {
    assert(r1->s.den == ONE_DEN);
    aux = abs32(r1->s.num);
    if (is_ratgmp(r2)) {
      q2 = get_gmp(r2);
      return mpz_divisible_ui_p(mpq_numref(*q2), aux);
    } else {
      return abs32(r2->s.num) % aux == 0;
    }
  }
}

/*
 * Check whether r2/r1 is an integer
 * - r1 must be non-zero
 */
bool neoq_divides(const neorational_t *r1, const neorational_t *r2) {
  neorational_t aux;
  bool divides;

  if (is_rat32(r1) && r1->s.den == ONE_DEN && (r1->s.num == 1 || r1->s.num == -1)) {
    // r1 is +1 or -1
    return true;
  }

  neoq_init(&aux);
  neoq_set(&aux, r2);
  neoq_div(&aux, r1);
  divides = neoq_is_integer(&aux);
  neoq_clear(&aux);

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
bool neoq_smt2_divides(const neorational_t *r1, const neorational_t *r2) {
  if (neoq_is_zero(r1)) {
    return neoq_is_zero(r2);
  } else {
    return neoq_divides(r1, r2);
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
void neoq_generalized_lcm(neorational_t *r1, neorational_t *r2) {
  neorational_t a1, b1;
  neorational_t a2, b2;

  if (neoq_is_integer(r1) && neoq_is_integer(r2)) {
    neoq_lcm(r1, r2);
  } else {
    neoq_init(&a1);
    neoq_get_num(&a1, r1);
    neoq_init(&b1);
    neoq_get_den(&b1, r1);

    neoq_init(&a2);
    neoq_get_num(&a2, r2);
    neoq_init(&b2);
    neoq_get_den(&b2, r2);

    neoq_lcm(&a1, &a2); // a1 := lcm(a1, a2)
    neoq_gcd(&b1, &b2); // b1 := gcd(b1, b2)

    // copy the result in r1
    neoq_set(r1, &a1);
    neoq_div(r1, &b1);

    neoq_clear(&a1);
    neoq_clear(&b1);
    neoq_clear(&a2);
    neoq_clear(&b2);
  }
}


/*
 * This computes the GCD of r1 and r2 for arbitrary non-zero rationals:
 * - if r1 is (a1/b1) and r2 is (a2/b2) then the result is
 *    gcd(a1, a2)/lcm(b1, b2).
 * - the result is stored in r1
 */
void neoq_generalized_gcd(neorational_t *r1, neorational_t *r2) {
  neorational_t a1, b1;
  neorational_t a2, b2;

  if (neoq_is_integer(r1) && neoq_is_integer(r2)) {
    neoq_lcm(r1, r2);
  } else {
    neoq_init(&a1);
    neoq_get_num(&a1, r1);
    neoq_init(&b1);
    neoq_get_den(&b1, r1);

    neoq_init(&a2);
    neoq_get_num(&a2, r2);
    neoq_init(&b2);
    neoq_get_den(&b2, r2);

    neoq_gcd(&a1, &a2); // a1 := gcd(a1, a2)
    neoq_lcm(&b1, &b2); // b1 := lcm(b1, b2)

    // copy the result in r1
    neoq_set(r1, &a1);
    neoq_div(r1, &b1);

    neoq_clear(&a1);
    neoq_clear(&b1);
    neoq_clear(&a2);
    neoq_clear(&b2);
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
void neoq_smt2_div(neorational_t *q, const neorational_t *x, const neorational_t *y) {
  assert(neoq_is_nonzero(y));

  neoq_set(q, x);
  neoq_div(q, y); // q := x/y
  if (neoq_is_pos(y)) {
    neoq_floor(q);  // round down
  } else {
    neoq_ceil(q);  // round up
  }
}

/*
 * For debugging: check that 0 <= r < abs(y)
 */
#ifndef NDEBUG
static bool plausible_mod(const neorational_t *r, const neorational_t *y) {
  neorational_t aux;
  bool ok;

  assert(neoq_is_nonzero(y));

  neoq_init(&aux);
  if (neoq_is_pos(y)) {
    neoq_set(&aux, y);
  } else {
    neoq_set_neg(&aux, y);
  }
  neoq_normalize(&aux);

  ok = neoq_is_nonneg(r) && neoq_lt(r, &aux);

  neoq_clear(&aux);

  return ok;
}
#endif


void neoq_smt2_mod(neorational_t *q, const neorational_t *x, const neorational_t *y) {
  assert(neoq_is_nonzero(y));

  neoq_smt2_div(q, x, y); // q := (div x y)
  neoq_mul(q, y);         // q := y * (div x y)
  neoq_sub(q, x);         // q := - x + y * (div x y)
  neoq_neg(q);            // q := x - y * (div x y) = (mod x y)

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
int neoq_cmp(const neorational_t *r1, const neorational_t *r2) {
  int64_t num;
  mpq_t *q1;
  mpq_t *q2;

  if (is_rat32(r1) && r1->s.den == ONE_DEN && is_rat32(r2) && r2->s.den == ONE_DEN) {
    return r1->s.num - r2->s.num;
  }

  if (is_ratgmp(r1)) {
    if (is_ratgmp(r2)) {
      q1 = get_gmp(r1);
      q2 = get_gmp(r2);
      return mpq_cmp(*q1, *q2);
    } else {
      q1 = get_gmp(r1);
      return mpq_cmp_si(*q1, r2->s.num, get_num(r2));
    }
  } else {
    if (is_ratgmp(r2)) {
      q2 = get_gmp(r2);
      return - mpq_cmp_si(*q2, r1->s.num, get_num(r1));
    } else {
      num = get_num(r2) * ((int64_t) r1->s.num) - get_num(r1) * ((int64_t) r2->s.num);
      return (num < 0 ? -1 : (num > 0));
    }
  }
}

/*
 * Compare r1 and num/den
 */
int neoq_cmp_int32(const neorational_t *r1, int32_t num, uint32_t den) {
  int64_t nn;
  mpq_t *q1;

  if (is_ratgmp(r1)) {
    q1 = get_gmp(r1);
    return mpq_cmp_si(*q1, num, den);
  } else {
    nn = den * ((int64_t) r1->s.num) - get_den(r1) * ((int64_t) num);
    return (nn < 0 ? -1 : (nn > 0));
  }
}

int neoq_cmp_int64(const neorational_t *r1, int64_t num, uint64_t den) {
  int retval;
  mpq_t q0;

  mpq_init2(q0, 64);

  mpq_set_int64(q0, num, den);
  mpq_canonicalize(q0);
  if (is_ratgmp(r1)){
    mpq_t *q1;

    q1 = get_gmp(r1);
    retval = mpq_cmp(*q1, q0);
  } else {
    retval = - mpq_cmp_si(q0, r1->s.num, get_den(r1));
  }

  mpq_clear(q0);
  return retval;
  
}

/*
 * Check whether r1 and r2 are opposite
 */
bool neoq_opposite(const neorational_t *r1, const neorational_t *r2) {
  neorational_t aux;
  bool result;

  if (is_rat32(r1) && r1->s.den == ONE_DEN && is_rat32(r2) && r2->s.den == ONE_DEN) {
    return r1->s.num + r2->s.num == 0;
  }

  neoq_init(&aux);
  neoq_set(&aux, r1);
  neoq_add(&aux, r2);
  result = neoq_is_zero(&aux);
  neoq_clear(&aux);

  return result;
}


/***********************************************
 *  CONVERSIONS FROM RATIONALS TO OTHER TYPES  *
 **********************************************/

/*
 * Convert r to a 32bit signed integer
 * - return false if r is not an integer or does not fit in 32 bits
 */
bool neoq_get32(neorational_t *r, int32_t *v) {
  uint32_t d;
  mpq_t *q;


  if (is_rat32(r) && r->s.den == ONE_DEN) {
    *v = r->s.num;
    return true;
  } else if (is_ratgmp(r)){
    q = get_gmp(r);
    if(mpq_fits_int32(*q)) {
      mpq_get_int32(*q, v, &d);
      return d == 1;
    }
  }
  return false;
}

/*
 * Convert r to a 64bit signed integer v
 * - return false if r is not an integer or does not fit in 64bits
 */
bool neoq_get64(neorational_t *r, int64_t *v) {
  uint64_t d;
  mpq_t *q;

  if (is_rat32(r) && r->s.den == ONE_DEN) {
    *v = r->s.num;
    return true;
  } else if (is_ratgmp(r)){
    q = get_gmp(r);
    if(mpq_fits_int64(*q)) {
      mpq_get_int64(*q, v, &d);
      return d == 1;
    }
  }
  return false;
}


/*
 * Convert r to a pair of 32 bit integers num/den
 * - return false if the numerator or denominator doesn't fit in 32bits
 */
bool neoq_get_int32(neorational_t *r, int32_t *num, uint32_t *den) {
  if (is_rat32(r)) {
    *num = r->s.num;
    *den = get_den(r);
    return true;
  } else {
    mpq_t *q;

    q = get_gmp(r);
    if (mpq_fits_int32(*q)) {
      mpq_get_int32(*q, num, den);
      if(*den > MAX_DENOMINATOR){  //IAM: hacky
	return false;
      }
      return true;
    }
  }
  return false;
}


/*
 * Convert r to a pair of 64bit integers num/den
 * - return false if the numerator or denominator doesn't fit in 64bits
 */
bool neoq_get_int64(neorational_t *r, int64_t *num, uint64_t *den) {
  if (is_rat32(r)) {
    *num = r->s.num;
    *den = get_den(r);
    return true;
  } else {
    mpq_t *q;

    q = get_gmp(r);
    if (mpq_fits_int64(*q)) {
      mpq_get_int64(*q, num, den);
      return true;
    }
  }
  return false;
}


/*
 * Check whether r can be converted to a 32bit integer,
 * a 64bit integer, or two a pair num/den of 32bit or 64bit integers.
 */
bool neoq_is_int32(neorational_t *r) {
  return (is_rat32(r) && r->s.den == ONE_DEN) || (is_ratgmp(r) && mpq_is_int32(*get_gmp(r)));
}

bool neoq_is_int64(neorational_t *r) {
  return (is_rat32(r) && r->s.den == ONE_DEN) || (is_ratgmp(r) && mpq_is_int64(*get_gmp(r)));
}

bool neoq_fits_int32(neorational_t *r) {  //IAM: do we really want this?
  if(is_rat32(r)){
    return true;
  } else if(mpq_fits_int32(*get_gmp(r))){
    int32_t num;
    uint32_t den;
    mpq_get_int32(*get_gmp(r), &num, &den);
    return den <= MAX_DENOMINATOR;
  } else {
    return false;
  }
  //return is_rat32(r) || mpq_fits_int32(*get_gmp(r));
}

bool neoq_fits_int64(neorational_t *r) {
  return is_rat32(r) || mpq_fits_int64(*get_gmp(r));
}


/*
 * Size estimate
 * - r must be an integer
 * - this returns approximately the number of bits to represent r
 */
uint32_t neoq_size(neorational_t *r) {
  size_t n;

  n = 32;
  if (is_ratgmp(r)) {
    n = mpz_size(mpq_numref(*get_gmp(r))) * mp_bits_per_limb;
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
bool neoq_get_mpz(neorational_t *r, mpz_t z) {
  if (is_rat32(r) && r->s.den == ONE_DEN) {
    mpz_set_si(z, r->s.num);
    return true;
  } else if (is_ratgmp(r)){
    mpq_t *q;

    q = get_gmp(r);
    if(mpq_is_integer(*q)) {
      mpz_set(z, mpq_numref(*q));
      return true;
    }
  }
  return false;
}

/*
 * Convert r to a GMP rational
 */
void neoq_get_mpq(neorational_t *r, mpq_t q) {
  if (is_ratgmp(r)) {
    mpq_set(q, *get_gmp(r));
  } else {
    mpq_set_int32(q, r->s.num, get_den(r));
  }
}

/*
 * Convert to a double
 */
double neoq_get_double(neorational_t *r) {
  double retval;
  mpq_t q0;

  mpq_init2(q0, 64);

  neoq_get_mpq(r, q0);
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
void neoq_print(FILE *f, const neorational_t *r) {
  if (is_ratgmp(r)) {
    mpq_out_str(f, 10, *get_gmp(r));
  } else if (r->s.den != ONE_DEN) {
    fprintf(f, "%" PRId32 "/%" PRIu32, r->s.num, get_den(r));
  } else {
    fprintf(f, "%" PRId32, r->s.num);
  }
}

/*
 * Print r's absolute value
 */
void neoq_print_abs(FILE *f, const neorational_t *r) {
  mpq_ptr q;
  int32_t abs_num;

  if (is_ratgmp(r)) {
    q = (mpq_ptr)get_gmp(r);  //IAM: need to check that this is kosher!
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
uint32_t neoq_hash_numerator(const neorational_t *r) {
  if (is_ratgmp(r)) {
    return (uint32_t) mpz_fdiv_ui(mpq_numref(*get_gmp(r)), HASH_MODULUS);
  } else if (r->s.num >= 0) {
      return (uint32_t) r->s.num;
  } else {
    return ((uint32_t) r->s.num) + ((uint32_t) HASH_MODULUS);
  }
}

uint32_t neoq_hash_denominator(const neorational_t *r) {
  if (is_ratgmp(r)) {
    return (uint32_t) mpz_fdiv_ui(mpq_denref(*get_gmp(r)), HASH_MODULUS);
  }
  return get_den(r);
}

void neoq_hash_decompose(const neorational_t *r, uint32_t *h_num, uint32_t *h_den) {
  if (is_ratgmp(r)) {
    mpq_t *q;

    q = get_gmp(r);
    *h_num = (uint32_t) mpz_fdiv_ui(mpq_numref(*q), HASH_MODULUS);
    *h_den = (uint32_t) mpz_fdiv_ui(mpq_denref(*q), HASH_MODULUS);
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
neorational_t *new_neorational_array(uint32_t n) {
  neorational_t *a;
  uint32_t i;

  if (n > MAX_RATIONAL_ARRAY_SIZE) {
    out_of_memory();
  }

  a = (neorational_t *) safe_malloc(n * sizeof(neorational_t));
  for (i=0; i<n; i++) {
    neoq_init(a + i);
  }

  return a;
}

/*
 * Delete an array created by the previous function
 */
void free_neorational_array(neorational_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    neoq_clear(a + i);
  }
  safe_free(a);
}
