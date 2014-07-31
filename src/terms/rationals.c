/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Operations on rational numbers
 * - rationals are represented as pairs of 32bit integers
 * or if they are too large as gmp rationals.
 * - the representation used is coded via the
 * denominator. If denominator > 0 then the
 * the rational is num/den, otherwise, numerator
 * is used as an index in the global table of
 * gmp rationals (mpq_t).
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

#include "utils/memalloc.h"
#include "terms/rationals.h"
#include "utils/gcd.h"



/****************************
 *  POOL OF GMP RATIONALS   *
 ***************************/

/*
 * Bank of mpq numbers
 * - bank_q[] = mpq_rationals (all initialized)
 * - bank_free = index of the first unused elements in mpq
 *   (start of free list)
 * - bank_capacity = size of arrays mpq_bank
 * - bank_size = number of rationals currently stored
 *
 * The free list is encoded via the numerators:
 * succ(i) = mpz_get_si(mpq_numref(bank_q[i]))
 */
mpq_t *bank_q = NULL;

static int32_t bank_free = -1;
static uint32_t bank_capacity = 0;
static uint32_t bank_size = 0;


/*
 * Maximal size.
 */
#define MAX_BANK_SIZE (UINT32_MAX/sizeof(mpq_t))

/*
 * Initialize bank for initial capacity n.
 * (n must be positive).
 */
static void init_bank(uint32_t n) {
  uint32_t i;

  if (n >= MAX_BANK_SIZE) {
    out_of_memory();
  }

  bank_q = (mpq_t *) safe_malloc(n * sizeof(mpq_t));
  bank_free = -1;
  bank_capacity = n;
  bank_size = 0;

  // initialize all the rationals with room
  // for a 64bit numerator and a 64bit denominator
  for (i=0; i<n; i++) {
    mpq_init2(bank_q[i], 64);
  }
}


/*
 * Increase bank capacity to n.
 */
static void resize_bank(uint32_t n) {
  uint32_t i, old_n;

  old_n = bank_capacity;
  if (n > old_n) {
    if (n >= MAX_BANK_SIZE) {
      out_of_memory();
    }

    bank_q = (mpq_t *) safe_realloc(bank_q, n * sizeof(mpq_t));
    bank_capacity = n;

    for (i=old_n; i<n; i++) {
      mpq_init2(bank_q[i], 64);
    }
  }
}


/*
 * Free the bank
 */
static void clear_bank() {
  uint32_t i, n;

  n = bank_capacity;
  for (i=0; i<n; i++) {
    mpq_clear(bank_q[i]);
  }

  free(bank_q);
}


/*
 * Free-list operations
 */
static inline int32_t free_list_next(int32_t i) {
  return mpz_get_si(mpq_numref(bank_q[i]));
}

/*
 * Allocate an mpq number: return the index
 */
static int32_t alloc_mpq() {
  int32_t n;

  n = bank_free;
  if (n >= 0) {
    bank_free = free_list_next(n);
  } else {
    n = bank_size;
    if (n >= bank_capacity) {
      resize_bank(2 * n);
    }
    bank_size = n + 1;
    assert(-1 <= bank_free && bank_free < (int32_t) bank_capacity);
  }
  return n;
}



/*
 * Free allocated mpq number of index i
 */
void free_mpq(int32_t i) {
  assert(0 <= i && i < bank_capacity);
  assert(-1 <= bank_free && bank_free < (int32_t) bank_capacity);
  mpz_set_si(mpq_numref(bank_q[i]), bank_free);
  bank_free = i;
}


/*
 * Get gmp number of index i
 */
mpq_ptr get_mpq(int32_t i) {
  return bank_q[i];
}



/*******************************
 * INITIALIZATION AND CLEANUP  *
 ******************************/

/*
 * Global gmp variables used for intermediate computations
 */
static mpz_t z0;
static mpq_t q0;

/*
 * String buffer for parsing.
 */
static char* string_buffer;
static uint32_t string_buffer_length;


#define INITIAL_BANK_CAPACITY 1024

void init_rationals() {
  init_mpq_aux();
  init_bank(INITIAL_BANK_CAPACITY);
  string_buffer = NULL;
  string_buffer_length = 0;
  mpz_init2(z0, 64);
  mpq_init2(q0, 64);
}

void cleanup_rationals() {
  cleanup_mpq_aux();
  clear_bank();
  safe_free(string_buffer);
  mpz_clear(z0);
  mpq_clear(q0);
}

static void division_by_zero() {
  fprintf(stderr, "\nRationals: division by zero\n");
  abort();
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
 * Normalization: construct rational a/b when
 * a and b are two 64bit numbers.
 * - b must be non-zero
 */
void q_set_int64(rational_t *r, int64_t a, uint64_t b) {
  uint64_t abs_a;
  int32_t i;
  bool a_positive;

  assert(b > 0);

  if (a == 0 || (b == 1 && MIN_NUMERATOR <= a && a <= MAX_NUMERATOR)) {
    if (r->den == 0) free_mpq(r->num);
    r->num = a;
    r->den = 1;
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
    if (r->den == 0) free_mpq(r->num);
    r->num = (int32_t) a;
    r->den = (uint32_t) b;
  } else {
    if (r->den != 0) {
      i = alloc_mpq();
      r->den = 0;
      r->num = i;
    } else {
      i = r->num;
    }
    mpq_set_int64(bank_q[i], a, b);
  }
}


/*
 * Normalization: construct a/b when a and b are 32 bits
 */
void q_set_int32(rational_t *r, int32_t a, uint32_t b) {
  uint32_t abs_a;
  int32_t i;
  bool a_positive;

  assert(b > 0);

  if (a == 0 || (b == 1 && MIN_NUMERATOR <= a && a <= MAX_NUMERATOR)) {
    if (r->den == 0) free_mpq(r->num);
    r->num = a;
    r->den = 1;
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
    if (r->den == 0) free_mpq(r->num);
    r->num = a;
    r->den = b;
  } else {
    if (r->den != 0) {
      i = alloc_mpq();
      r->den = 0;
      r->num = i;
    } else {
      i = r->num;
    }
    mpq_set_int32(bank_q[i], a, b);
  }
}


/*
 * Construct r = a/1
 */
void q_set64(rational_t *r, int64_t a) {
  int32_t i;

  if (MIN_NUMERATOR <= a && a <= MAX_NUMERATOR) {
    if (r->den == 0) free_mpq(r->num);
    r->num = (int32_t) a;
    r->den = 1;
  } else {
    if (r->den != 0) {
      i = alloc_mpq();
      r->den = 0;
      r->num = i;
    } else {
      i = r->num;
    }
    mpq_set_int64(bank_q[i], a, 1);
  }
}


void q_set32(rational_t *r, int32_t a) {
  int32_t i;

  if (MIN_NUMERATOR <= a && a <= MAX_NUMERATOR) {
    if (r->den == 0) free_mpq(r->num);
    r->num = a;
    r->den = 1;
  } else {
    if (r->den != 0) {
      i = alloc_mpq();
      r->den = 0;
      r->num = i;
    } else {
      i = r->num;
    }
    mpq_set_int32(bank_q[i], a, 1);
  }
}



/*
 * Convert r to a gmp number.
 * r->num and r->den must have no common factor
 * and r->den must be non-zero.
 */
static void convert_to_gmp(rational_t *r) {
  int32_t i;

  assert(r->den != 0);
  i = alloc_mpq();
  mpq_set_int32(bank_q[i], r->num, r->den);
  r->num = i;
  r->den = 0;
}

/*
 * Set r to a gmp with value = a.
 */
static void set_to_gmp64(rational_t *r, int64_t a) {
  int32_t i;

  assert(r->den != 0);
  i = alloc_mpq();
  mpq_set_int64(bank_q[i], a, 1);
  r->num = i;
  r->den = 0;
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

  if (r->den == 0) {
    q = bank_q[r->num];
    if (mpz_fits_ulong_p(mpq_denref(q)) && mpz_fits_slong_p(mpq_numref(q))) {
      num = mpz_get_si(mpq_numref(q));
      den = mpz_get_ui(mpq_denref(q));
      if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR && den <= MAX_DENOMINATOR) {
        free_mpq(r->num);
        r->num = (int32_t) num;
        r->den = (uint32_t) den;
      }
    }
  }
}



/*
 * Prepare to assign an mpq number to r
 * - if r is not attached to an mpq number in bank_q, then allocate one
 */
static inline void q_prepare(rational_t *r) {
  if (r->den != 0) {
    r->den = 0;
    r->num = alloc_mpq();
  }
}

/*
 * assign r:= z/1
 */
void q_set_mpz(rational_t *r, const mpz_t z) {
  q_prepare(r);
  mpq_set_z(bank_q[r->num], z);
}


/*
 * Copy q into r
 */
void q_set_mpq(rational_t *r, const mpq_t q) {
  q_prepare(r);
  mpq_set(bank_q[r->num], q);
}


/*
 * Copy r2 into r1
 */
void q_set(rational_t *r1, const rational_t *r2) {
  if (r2->den == 0) {
    //    q_set_mpq(r1, bank_q[r2->num]); BUG HERE
    q_prepare(r1);
    mpq_set(bank_q[r1->num], bank_q[r2->num]);
  } else {
    if (r1->den == 0) free_mpq(r1->num);
    r1->num = r2->num;
    r1->den = r2->den;
  }
}


/*
 * Copy opposite of r2 into r1
 */
void q_set_neg(rational_t *r1, const rational_t *r2) {
  if (r2->den == 0) {
    q_prepare(r1);
    mpq_neg(bank_q[r1->num], bank_q[r2->num]);
  } else {
    if (r1->den == 0) free_mpq(r1->num);
    r1->num = - r2->num;
    r1->den = r2->den;
  }
}


/*
 * Copy the absolute value of r2 into r1
 */
void q_set_abs(rational_t *r1, const rational_t *r2) {
  if (r2->den == 0) {
    q_prepare(r1);
    mpq_abs(bank_q[r1->num], bank_q[r2->num]);
  } else {
    if (r1->den == 0) free_mpq(r1->num);
    r1->den = r2->den;
    if (r2->num < 0) {
      r1->num = - r2->num;
    } else {
      r1->num = r2->num;
    }
  }
}


/*
 * Copy the numerator of r2 into r1
 * - r1 must be initialized
 * - r2 and r1 must be different objects
 */
void q_get_num(rational_t *r1, const rational_t *r2) {
  mpq_ptr q;
  long num;

  if (r2->den == 0) {
    q = bank_q[r2->num];
    if (mpz_fits_slong_p(mpq_numref(q))) {
      num = mpz_get_si(mpq_numref(q));
      if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR) {
        if (r1->den == 0) free_mpq(r1->num);
        r1->num = num;
        r1->den = 1;
        return;
      }
    }
    // BUG:    q_set_mpz(r1, mpq_numref(q));
    q_prepare(r1);
    mpq_set_z(bank_q[r1->num], mpq_numref(bank_q[r2->num]));

  } else {
    if (r1->den == 0) free_mpq(r1->num);
    r1->num = r2->num;
    r1->den = 1;
  }
}


/*
 * Copy the denominator of r2 into r1
 * - r1 must be initialized
 * - r1 and r2 must be different objects
 */
void q_get_den(rational_t *r1, const rational_t *r2) {
  mpq_ptr q;
  unsigned long den;

  if (r2->den == 0) {
    q = bank_q[r2->num];
    if (mpz_fits_ulong_p(mpq_denref(q))) {
      den = mpz_get_ui(mpq_denref(q));
      if (den <= MAX_DENOMINATOR) {
        if (r1->den == 0) free_mpq(r1->num);
        r1->num = den;
        r1->den = 1;
        return;
      }
    }
    // BUG    q_set_mpz(r1, mpq_denref(q));
    q_prepare(r1);
    mpq_set_z(bank_q[r1->num], mpq_denref(bank_q[r2->num]));

  } else {
    if (r1->den == 0) free_mpq(r1->num);
    r1->num = r2->den;
    r1->den = 1;
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
static int q_set_q0(rational_t *r) {
  int32_t i;
  unsigned long den;
  long num;

  // try to store q0 as a pair num/den
  if (mpz_fits_ulong_p(mpq_denref(q0)) && mpz_fits_slong_p(mpq_numref(q0))) {
    num = mpz_get_si(mpq_numref(q0));
    den = mpz_get_ui(mpq_denref(q0));
    if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR && den <= MAX_DENOMINATOR) {
      if (r->den == 0) free_mpq(r->num);
      r->num = (int32_t) num;
      r->den = (uint32_t) den;
      return 0;
    }
  }

  // copy q0
  if (r->den != 0) {
    i = alloc_mpq();
    r->den = 0;
    r->num = i;
  } else {
    i = r->num;
  }
  mpq_set(bank_q[i], q0);

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
  // GMP rejects an initial '+' so skip it
  if (*s == '+') s ++;
  if (mpq_set_str(q0, s, 10) < 0) return -1;
  if (mpz_sgn(mpq_denref(q0)) == 0) return -2; // the denominator is zero
  mpq_canonicalize(q0);
  return q_set_q0(r);
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
  // GMP rejects an initial '+' so skip it
  if (*s == '+') s ++;
  assert(0 == base || (2 <= base && base <= 36));
  if (mpq_set_str(q0, s, base) < 0) return -1;
  if (mpz_sgn(mpq_denref(q0)) == 0) return -2; // the denominator is zero
  mpq_canonicalize(q0);
  return q_set_q0(r);
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
int q_set_from_float_string(rational_t *r, const char *s) {
  size_t len;
  int frac_len, sign;
  long int exponent;
  char *b, c;

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
    if (errno != 0) return -1;
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
    return -1;
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

  return q_set_q0(r);
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

  if (r1->den == 1 && r2->den == 1) {
    r1->num += r2->num;
    if (r1->num < MIN_NUMERATOR || r1->num > MAX_NUMERATOR) {
      convert_to_gmp(r1);
    }
    return;
  }

  if (r2->den == 0) {
    if (r1->den != 0) convert_to_gmp(r1) ;
    mpq_add(bank_q[r1->num], bank_q[r1->num], bank_q[r2->num]);

  } else if (r1->den == 0) {
    mpq_add_si(bank_q[r1->num], r2->num, r2->den);

  } else {
    den = r1->den * ((uint64_t) r2->den);
    num = r1->den * ((int64_t) r2->num) + r2->den * ((int64_t) r1->num);
    q_set_int64(r1, num, den);
  }
}


/*
 * Subtract r2 from r1
 */
void q_sub(rational_t *r1, const rational_t *r2) {
  uint64_t den;
  int64_t num;

  if (r1->den == 1 && r2->den == 1) {
    r1->num -= r2->num;
    if (r1->num < MIN_NUMERATOR || r1->num > MAX_NUMERATOR) {
      convert_to_gmp(r1);
    }
    return;
  }

  if (r2->den == 0) {
    if (r1->den != 0) convert_to_gmp(r1) ;
    mpq_sub(bank_q[r1->num], bank_q[r1->num], bank_q[r2->num]);

  } else if (r1->den == 0) {
    mpq_sub_si(bank_q[r1->num], r2->num, r2->den);

  } else {
    den = r1->den * ((uint64_t) r2->den);
    num = r2->den * ((int64_t) r1->num) - r1->den * ((int64_t) r2->num);
    q_set_int64(r1, num, den);
  }
}


/*
 * Negate r
 */
void q_neg(rational_t *r) {
  if (r->den == 0) {
    mpq_neg(bank_q[r->num], bank_q[r->num]);
  } else {
    r->num = - r->num;
  }
}



/*
 * Invert r
 */
void q_inv(rational_t *r) {
  uint32_t abs_num;

  if (r->den == 0) {
    mpq_inv(bank_q[r->num], bank_q[r->num]);

  } else if (r->num < 0) {
    abs_num = (uint32_t) - r->num;
    r->num = (int32_t) - r->den;
    r->den = abs_num;

  } else if (r->num > 0) {
    abs_num = (uint32_t) r->num;
    r->num = (uint32_t) r->den;
    r->den = abs_num;

  } else {
    division_by_zero();
  }
}


/*
 * Multiply r1 by r2
 */
void q_mul(rational_t *r1, const rational_t *r2) {
  uint64_t den;
  int64_t num;

  if (r1->den == 1 && r2->den == 1) {
    num = r1->num * ((int64_t) r2->num);
    if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR) {
      r1->num = (int32_t) num;
    } else {
      set_to_gmp64(r1, num);
    }
    return;
  }

  if (r2->den == 0) {
    if (r1->den != 0) convert_to_gmp(r1);
    mpq_mul(bank_q[r1->num], bank_q[r1->num], bank_q[r2->num]);

  } else if (r1->den == 0) {
    mpq_mul_si(bank_q[r1->num], r2->num, r2->den);

  } else {
    den = r1->den * ((uint64_t) r2->den);
    num = r1->num * ((int64_t) r2->num);
    q_set_int64(r1, num, den);
  }
}


/*
 * Divide r1 by r2
 */
void q_div(rational_t *r1, const rational_t *r2) {
  uint64_t den;
  int64_t num;

  if (r2->den == 0) {
    if (r1->den != 0) convert_to_gmp(r1);
    mpq_div(bank_q[r1->num], bank_q[r1->num], bank_q[r2->num]);

  } else if (r1->den == 0) {
    if (r2->num == 0) {
      division_by_zero();
    } else {
      mpq_div_si(bank_q[r1->num], r2->num, r2->den);
    }

  } else if (r2->num > 0) {
    den = r1->den * ((uint64_t) r2->num);
    num = r1->num * ((int64_t) r2->den);
    q_set_int64(r1, num, den);

  } else if (r2->num < 0) {
    den = r1->den * ((uint64_t) (- r2->num));
    num = r1->num * ( - ((int64_t) r2->den));
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

  if (r1->den == 1 && r2->den == 1 && r3->den == 1) {
    num = r1->num + r2->num * ((int64_t) r3->num);
    if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR) {
      r1->num = (int32_t) num;
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

  if (r1->den == 1 && r2->den == 1 && r3->den == 1) {
    num = r1->num - r2->num * ((int64_t) r3->num);
    if (MIN_NUMERATOR <= num && num <= MAX_NUMERATOR) {
      r1->num = (int32_t) num;
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
  int32_t n;
  if (r1->den == 0) {
    n = r1->num;
    mpz_add(mpq_numref(bank_q[n]), mpq_numref(bank_q[n]), mpq_denref(bank_q[n]));
  } else {
    r1->num += r1->den;
    if (r1->num > MAX_NUMERATOR) {
      convert_to_gmp(r1);
    }
  }
}

/*
 * Decrement: subtract one from r1
 */
void q_sub_one(rational_t *r1) {
  int32_t n;
  if (r1->den == 0) {
    n = r1->num;
    mpz_sub(mpq_numref(bank_q[n]), mpq_numref(bank_q[n]), mpq_denref(bank_q[n]));
  } else {
    r1->num -= r1->den;
    if (r1->num < MIN_NUMERATOR) {
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

  if (r->den == 0) {
    n = r->num;
    mpz_fdiv_q(mpq_numref(bank_q[n]), mpq_numref(bank_q[n]), mpq_denref(bank_q[n]));
    mpz_set_ui(mpq_denref(bank_q[n]), 1UL);
  } else {
    n = r->num / (int32_t) r->den;
    if (r->num < 0) n --;
    r->num = n;
    r->den = 1;
  }
}

// set r to ceil(r)
void q_ceil(rational_t *r) {
  int32_t n;

  if (q_is_integer(r)) return;

  if (r->den == 0) {
    n = r->num;
    mpz_cdiv_q(mpq_numref(bank_q[n]), mpq_numref(bank_q[n]), mpq_denref(bank_q[n]));
    mpz_set_ui(mpq_denref(bank_q[n]), 1UL);
  } else {
    n = r->num / (int32_t) r->den;
    if (r->num > 0) n ++;
    r->num = n;
    r->den = 1;
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

  if (r2->den != 0) {
    if (r1->den != 0) {
      // both r1 and r2 are 32bit integers
      a = abs32(r1->num);
      b = abs32(r2->num);
      d = ((uint64_t) a) * ((uint64_t) (b/gcd32(a, b)));
      if (d <= MAX_NUMERATOR) {
        r1->num = d;
        r1->den = 1;
      } else {
        set_to_gmp64(r1, d);
      }
    } else {
      // r2 is 32bits, r1 is gmp
      b = abs32(r2->num);
      mpz_lcm_ui(mpq_numref(bank_q[r1->num]), mpq_numref(bank_q[r1->num]), b);
    }

  } else {
    // r2 is a gmp rational
    if (r1->den != 0) convert_to_gmp(r1);
    mpz_lcm(mpq_numref(bank_q[r1->num]), mpq_numref(bank_q[r1->num]), mpq_numref(bank_q[r2->num]));
  }

}


/*
 * Store gcd(r1, r2) into r1
 * - r1 and r2 must be integer and non-zero
 * - the result is positive
 */
void q_gcd(rational_t *r1, const rational_t *r2) {
  uint32_t a, b, d;

  if (r2->den != 0) {
    if (r1->den != 0) {
      // r1 and r2 are small integers
      a = abs32(r1->num);
      b = abs32(r2->num);
      d = gcd32(a, b);
    } else {
      // r1 is gmp, r2 is a small integer
      b = abs32(r2->num);
      d = mpz_gcd_ui(NULL, mpq_numref(bank_q[r1->num]), b);
      free_mpq(r1->num);
    }
    assert(d <= MAX_NUMERATOR);
    r1->num = d;
    r1->den = 1;
  } else {
    if (r1->den != 0) {
      // r1 is a small integer, r2 is a gmp number
      a = abs32(r1->num);
      d = mpz_gcd_ui(NULL, mpq_numref(bank_q[r2->num]), a);
      assert(d <= MAX_NUMERATOR);
      r1->num = d;
      r1->den = 1;
    } else {
      // both are gmp numbers
      mpz_gcd(mpq_numref(bank_q[r1->num]), mpq_numref(bank_q[r1->num]), mpq_numref(bank_q[r2->num]));
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

  q_normalize(r2);

  if (r2->den != 0) {
    assert(r2->den == 1 && r2->num > 0);
    if (r1->den != 0) {
      // both r1 and r2 are small integers
      n = r1->num % r2->num; // remainder: n has the same sign as r1 (or n == 0)
      r1->num /= r2->num;    // quotient: same sign as r1, rounded towards 0
      if (n < 0) {
        r1->num --;
      }
    } else {
      // r1 is gmp, r2 is a small integer
      mpz_fdiv_q_ui(mpq_numref(bank_q[r1->num]), mpq_numref(bank_q[r1->num]), r2->num);
      assert(mpq_is_integer(bank_q[r1->num]));
    }
  } else {
    assert(mpq_is_integer(bank_q[r2->num]) && mpq_sgn(bank_q[r2->num]) > 0);
    if (r1->den != 0) {
      /*
       * r1 is a small integer, r2 is a gmp rational
       * since r2 is normalized and positive, we have r2 > abs(r1)
       * so r1 div r2 = 0 if r1 >= 0 or -1 if r1 < 0
       */
      assert(r1->den == 1);
      if (r1->num >= 0) {
        r1->num = 0;
      } else {
        r1->num = -1;
      }
    } else {
      // both r1 and r2 are gmp rationals
      mpz_fdiv_q(mpq_numref(bank_q[r1->num]), mpq_numref(bank_q[r1->num]),
                 mpq_numref(bank_q[r2->num]));
      assert(mpq_is_integer(bank_q[r1->num]));
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

  q_normalize(r2);

  if (r2->den != 0) {
    assert(r2->den == 1 && r2->num > 0);
    if (r1->den != 0) {
      /*
       * both r1 and r2 are small integers
       * Note: the result of (r1->num % r2->num) has the same sign as r1->num
       */
      n = r1->num % r2->num;
      if (n < 0) {
        n += r2->num;
      }
      assert(0 <= n && n < r2->num);
      r1->num = n;
    } else {
      // r1 is gmp, r2 is a small integer
      n = mpz_fdiv_ui(mpq_numref(bank_q[r1->num]), r2->num);
      assert(0 <= n && n <= MAX_NUMERATOR);
      free_mpq(r1->num);
      r1->num = n;
      r1->den = 1;
    }
  } else {
    assert(mpq_is_integer(bank_q[r2->num]) && mpq_sgn(bank_q[r2->num]) > 0);
    if (r1->den != 0) {
      /*
       * r1 is a small integer, r2 is a gmp rational
       * since r2 is normalized and positive, we have r2 > abs(r1)
       * so r1 mod r2 = r1 if r1 >= 0
       * or r1 mod r2 = (r2 + r1) if r1 < 0
       */
      assert(r1->den == 1);
      if (r1->num < 0) {
        n = alloc_mpq();
        mpq_set_si(bank_q[n], r1->num, 1UL);
        mpz_add(mpq_numref(bank_q[n]), mpq_numref(bank_q[n]), mpq_numref(bank_q[r2->num]));
        r1->num = n;
        r1->den = 0;
        assert(mpq_is_integer(bank_q[n]) && mpq_sgn(bank_q[n]) > 0);
      }

    } else {
      // both r1 and r2 are gmp rationals
      mpz_fdiv_r(mpq_numref(bank_q[r1->num]), mpq_numref(bank_q[r1->num]),
                 mpq_numref(bank_q[r2->num]));
      assert(mpq_is_integer(bank_q[r1->num]));
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

  q_normalize(r1);

  if (r1->den == 0) {
    if (r2->den == 0) {
      return mpz_divisible_p(mpq_numref(bank_q[r2->num]), mpq_numref(bank_q[r1->num]));
    } else {
      return false;  // abs(r1) > abs(r2) so r1 can't divide r2
    }

  } else {
    assert(r1->den == 1);
    aux = abs32(r1->num);
    if (r2->den == 0) {
      return mpz_divisible_ui_p(mpq_numref(bank_q[r2->num]), aux);
    } else {
      return abs32(r2->num) % aux == 0;
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

  if (r1->den == 1 && (r1->num == 1 || r1->num == -1)) {
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



/*****************
 *  COMPARISONS  *
 ****************/

/*
 * Compare r1 and r2
 * - returns a negative number if r1 < r2
 * - returns 0 if r1 = r2
 * - returns a positive number if r1 > r2
 */
int q_cmp(rational_t *r1, rational_t *r2) {
  int64_t num;

  if (r1->den == 1 && r2->den == 1) {
    return r1->num - r2->num;
  }

  if (r1->den == 0) {
    if (r2->den == 0) {
      return mpq_cmp(bank_q[r1->num], bank_q[r2->num]);
    } else {
      return mpq_cmp_si(bank_q[r1->num], r2->num, r2->den);
    }
  } else {
    if (r2->den == 0) {
      return - mpq_cmp_si(bank_q[r2->num], r1->num, r1->den);
    } else {
      num = r2->den * ((int64_t) r1->num) - r1->den * ((int64_t) r2->num);
      return (num < 0 ? -1 : (num > 0));
    }
  }
}


/*
 * Compare r1 and num/den
 */
int q_cmp_int32(rational_t *r1, int32_t num, uint32_t den) {
  int64_t nn;

  if (r1->den == 0) {
    return mpq_cmp_si(bank_q[r1->num], num, den);
  } else {
    nn = den * ((int64_t) r1->num) - r1->den * ((int64_t) num);
    return (nn < 0 ? -1 : (nn > 0));
  }
}

int q_cmp_int64(rational_t *r1, int64_t num, uint64_t den) {
  mpq_set_int64(q0, num, den);
  mpq_canonicalize(q0);
  if (r1->den == 0) {
    return mpq_cmp(bank_q[r1->num], q0);
  } else {
    return - mpq_cmp_si(q0, r1->num, r1->den);
  }
}



/*
 * Check whether r1 and r2 are opposite
 */
bool q_opposite(rational_t *r1, rational_t *r2) {
  rational_t aux;
  bool result;

  if (r1->den == 1 && r2->den == 1) {
    return r1->num + r2->num == 0;
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

  if (r->den == 1) {
    *v = r->num;
    return true;
  } else if (r->den == 0 && mpq_fits_int32(bank_q[r->num])) {
    mpq_get_int32(bank_q[r->num], v, &d);
    return d == 1;
  } else {
    return false;
  }
}


/*
 * Convert r to a 64bit signed integer v
 * - return false if r is not an integer or does not fit in 64bits
 */
bool q_get64(rational_t *r, int64_t *v) {
  uint64_t d;

  if (r->den == 1) {
    *v = r->num;
    return true;
  } else if (r->den == 0 && mpq_fits_int64(bank_q[r->num])) {
    mpq_get_int64(bank_q[r->num], v, &d);
    return d == 1;
  } else {
    return false;
  }
}


/*
 * Convert r to a pair of 32 bit integers num/den
 * - return false if the numerator or denominator doesn't fit in 32bits
 */
bool q_get_int32(rational_t *r, int32_t *num, uint32_t *den) {
  if (r->den != 0) {
    *num = r->num;
    *den = r->den;
    return true;
  } else if (mpq_fits_int32(bank_q[r->num])) {
    mpq_get_int32(bank_q[r->num], num, den);
    return true;
  } else {
    return false;
  }
}

/*
 * Convert r to a pair of 64bit integers num/den
 * - return false if the numerator or denominator doesn't fit in 64bits
 */
bool q_get_int64(rational_t *r, int64_t *num, uint64_t *den) {
  if (r->den != 0) {
    *num = r->num;
    *den = r->den;
    return true;
  } else if (mpq_fits_int64(bank_q[r->num])) {
    mpq_get_int64(bank_q[r->num], num, den);
    return true;
  } else {
    return false;
  }
}



/*
 * Check whether r can be converted to a 32bit integer,
 * a 64bit integer, or two a pair num/den of 32bit or 64bit integers.
 */
bool q_is_int32(rational_t *r) {
  return r->den == 1 || (r->den == 0 && mpq_is_int32(bank_q[r->num]));
}

bool q_is_int64(rational_t *r) {
  return r->den == 1 || (r->den == 0 && mpq_is_int64(bank_q[r->num]));
}

bool q_fits_int32(rational_t *r) {
  return r->den != 0 || mpq_fits_int32(bank_q[r->num]);
}

bool q_fits_int64(rational_t *r) {
  return r->den != 0 || mpq_fits_int64(bank_q[r->num]);
}




/*
 * Convert r to a GMP integer
 * - return false if r is not an integer
 */
bool q_get_mpz(rational_t *r, mpz_t z) {
  if (r->den == 1) {
    mpz_set_si(z, r->num);
    return true;
  } else if (r->den == 0 && mpq_is_integer(bank_q[r->num])) {
    mpz_set(z, mpq_numref(bank_q[r->num]));
    return true;
  } else {
    return false;
  }
}


/*
 * Convert r to a GMP rational
 */
void q_get_mpq(rational_t *r, mpq_t q) {
  if (r->den == 0) {
    mpq_set(q, bank_q[r->num]);
  } else {
    mpq_set_int32(q, r->num, r->den);
  }
}



/*
 * Convert to a double
 */
double q_get_double(rational_t *r) {
  q_get_mpq(r, q0);
  return mpq_get_d(q0);
}




/**************
 *  PRINTING  *
 *************/

/*
 * Print r
 */
void q_print(FILE *f, rational_t *r) {
  if (r->den == 0) {
    mpq_out_str(f, 10, bank_q[r->num]);
  } else if (r->den != 1) {
    fprintf(f, "%" PRId32 "/%" PRIu32, r->num, r->den);
  } else {
    fprintf(f, "%" PRId32, r->num);
  }
}

/*
 * Print r's absolute value
 */
void q_print_abs(FILE *f, rational_t *r) {
  mpq_ptr q;
  int32_t abs_num;

  if (r->den == 0) {
    q = bank_q[r->num];
    if (mpq_sgn(q) < 0) {
      mpq_neg(q, q);
      mpq_out_str(f, 10, bank_q[r->num]);
      mpq_neg(q, q);
    } else {
      mpq_out_str(f, 10, bank_q[r->num]);
    }
  } else {
    abs_num = r->num;
    if (abs_num < 0) abs_num = - abs_num;

    if (r->den != 1) {
      fprintf(f, "%" PRId32 "/%" PRIu32, abs_num, r->den);
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
uint32_t q_hash_numerator(rational_t *r) {
  if (r->den == 0) {
    return (uint32_t) mpz_fdiv_ui(mpq_numref(bank_q[r->num]), HASH_MODULUS);
  } else if (r->num >= 0) {
    return (uint32_t) r->num;
  } else {
    return ((uint32_t) r->num) + ((uint32_t) HASH_MODULUS);
  }
}

uint32_t q_hash_denominator(rational_t *r) {
  if (r->den == 0) {
    return (uint32_t) mpz_fdiv_ui(mpq_denref(bank_q[r->num]), HASH_MODULUS);
  }
  return r->den;
}

void q_hash_decompose(rational_t *r, uint32_t *h_num, uint32_t *h_den) {
  if (r->den == 0) {
    *h_num = (uint32_t) mpz_fdiv_ui(mpq_numref(bank_q[r->num]), HASH_MODULUS);
    *h_den = (uint32_t) mpz_fdiv_ui(mpq_denref(bank_q[r->num]), HASH_MODULUS);
  } else if (r->num >= 0) {
    *h_num = (uint32_t) r->num;
    *h_den = r->den;
  } else {
    *h_num = ((uint32_t) r->num) + ((uint32_t) HASH_MODULUS);
    *h_den = r->den;
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

