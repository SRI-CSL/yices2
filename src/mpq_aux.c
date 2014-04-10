/*
 * Extra functions for computing with gmp
 * rational numbers.
 */

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <gmp.h>

#include "mpq_aux.h"
#include "mpq_pool.h"
#include "mpz_pool.h"

#define DEBUG 1

/*
 * Global variable for intermediate computations.
 */
//static mpz_t z0;


/*
 * Debug code: double check results
 */
#ifdef DEBUG

//static mpq_t check, aux;

static inline void check_result(mpq_t q, mpq_t check) {
  if (! mpq_equal(q, check)) {
    fprintf(stderr, "**** ERROR IN mpq_aux.c\n");
    abort();
  }
}

#else

static inline void check_result(mpq_t q, mpq_t check) {}

#endif



/*
 * Initialization: allocate and initialize the
 * global variables.
 */
void init_mpq_aux() {
#if 0
  printf("GMP Version %s\n", gmp_version);
  printf("bits per limb: %d\n\n", mp_bits_per_limb);
  fflush(stdout);
#endif
  if (ULONG_SIZE != sizeof(unsigned long)) {
    printf("*** BUG: Bad configuration: ULONG_SIZE = %u, should be %u\n",
           (unsigned int) ULONG_SIZE, (unsigned int) sizeof(unsigned long));
    fflush(stdout);
    abort();
  }

  //mpz_init(z0);

#ifdef DEBUG
  //mpq_init(check);
  //mpq_init(aux);
#endif
}


/*
 * Cleanup
 */
void cleanup_mpq_aux() {
  //mpz_clear(z0);

#ifdef DEBUG
  //mpq_clear(check);
  //mpq_clear(aux);
#endif
}



/*
 * Initialize q with enough room for numerator
 * and denominator with n bits. Not to be used
 * if q is already initialized.
 */
void mpq_init2(mpq_t q, unsigned long n) {
  mpz_ptr num_q, den_q;

  num_q = mpq_numref(q);
  den_q = mpq_denref(q);
  mpz_init2(num_q, n);
  mpz_init2(den_q, n);
  mpz_set_ui(den_q, 1UL);
}



/*
 * Add rational num/den to q.
 * - den must be non zero
 * - num and den must have no common factor
 * rational 0 must be given as num=0/den=1
 */
void mpq_add_si(mpq_t q, long num, unsigned long den) {
  mpz_ptr num_q, den_q;
  unsigned long gcd;


  int retcode;
  int32_t icheck, iaux;
  mpq_ptr check, aux;
  int32_t iz0;
  mpz_ptr z0;

  retcode = mpq_pool_borrow(&icheck, &check);
  if(retcode != 0){
    fprintf(stderr, "mpq_add_si: mpq_pool_borrow failed");
    abort();
  }

  retcode = mpq_pool_borrow(&iaux, &aux);
  if(retcode != 0){
    fprintf(stderr, "mpq_add_si: mpq_pool_borrow failed");
    abort();
  }

  retcode = mpz_pool_borrow(&iz0, &z0);
  if(retcode != 0){
    fprintf(stderr, "mpq_add_si: mpz_pool_borrow failed");
    abort();
  }



#ifdef DEBUG
  mpq_set_si(aux, num, den);
  mpq_add(check, q, aux);
#endif

  num_q = mpq_numref(q);
  den_q = mpq_denref(q);

  // special cases: den = 1 should be common
  //                num = 0 should be rare
  if (den == 1) {
    // a/b + d --> (a + bd)/b
    mpz_mul_si(z0, den_q, num);
    mpz_add(num_q, num_q, z0);

    check_result(q, check);
    goto clean_up;
  }

  gcd = mpz_gcd_ui(NULL, den_q, den);
  //  printf("gcd = %lu\n", gcd);

  if (gcd == 1) {
    // a/b + c/d  --> (a d + b c) / bd
    mpz_mul_si(z0, den_q, num);
    mpz_mul_ui(num_q, num_q, den);
    mpz_add(num_q, num_q, z0);
    mpz_mul_ui(den_q, den_q, den);

    check_result(q, check);
    goto clean_up;
  }

  mpz_divexact_ui(den_q, den_q, gcd); // b0 = b/gcd
  mpz_mul_si(z0, den_q, num);     // z0 = b0 * num

  mpz_mul_ui(num_q, num_q, den/gcd);
  mpz_add(num_q, num_q, z0);      // num_q := (den_q/gcd) * num + (den/gcd) * num_q

  gcd = mpz_gcd_ui(NULL, num_q, gcd);
  if (gcd == 1) {
    mpz_mul_ui(den_q, den_q, den);
  } else {
    mpz_divexact_ui(num_q, num_q, gcd);
    mpz_mul_ui(den_q, den_q, den/gcd);
  }

  check_result(q, check);

 clean_up:

    retcode = mpq_pool_return(icheck);
    if(retcode != 0){
      fprintf(stderr, "mpq_add_si: mpq_pool_return failed");
      abort();
    }

    retcode = mpq_pool_return(iaux);
    if(retcode != 0){
      fprintf(stderr, "mpq_add_si: mpq_pool_return failed");
      abort();
    }

    retcode = mpz_pool_return(iz0);
    if(retcode != 0){
      fprintf(stderr, "mpq_add_si: mpz_pool_return failed");
      abort();
    }


}




/*
 * Multiply q by num/den
 * - num must be more than LONG_MIN
 * - den must be non-zero
 * - num and den must have no common factor
 */
void mpq_mul_si(mpq_t q, long num, unsigned long den) {
  mpz_ptr num_q, den_q;
  unsigned long gcd, abs_num;

  int retcode;
  int32_t icheck, iaux;
  mpq_ptr check, aux;

  retcode = mpq_pool_borrow(&icheck, &check);
  if(retcode != 0){
    fprintf(stderr, "mpq_mul_si: mpq_pool_borrow failed");
    abort();
  }

  retcode = mpq_pool_borrow(&iaux, &aux);
  if(retcode != 0){
    fprintf(stderr, "mpq_mul_si: mpq_pool_borrow failed");
    abort();
  }

#ifdef DEBUG
  mpq_set_si(aux, num, den);
  mpq_mul(check, q, aux);
#endif

  if (num == 0) {
    mpq_set_ui(q, 0, 1);
    check_result(q, check);
    goto clean_up;
  }

  num_q = mpq_numref(q);
  den_q = mpq_denref(q);
  abs_num = (unsigned long) labs(num);

  if (abs_num != 1) {
    gcd = mpz_gcd_ui(NULL, den_q, abs_num);
    abs_num /= gcd;
    mpz_divexact_ui(den_q, den_q, gcd);
  }

  if (den != 1) {
    gcd = mpz_gcd_ui(NULL, num_q, den);
    den /= gcd;
    mpz_divexact_ui(num_q, num_q, gcd);
  }

  mpz_mul_ui(num_q, num_q, abs_num);
  mpz_mul_ui(den_q, den_q, den);
  if (num < 0) {
    mpz_neg(num_q, num_q);
  }

  check_result(q, check);

 clean_up:

  retcode = mpq_pool_return(icheck);
  if(retcode != 0){
    fprintf(stderr, "mpq_mul_si: mpq_pool_return failed");
    abort();
  }

  retcode = mpq_pool_return(iaux);
  if(retcode != 0){
    fprintf(stderr, "mpq_mul_si: mpq_pool_return failed");
    abort();
  }


}



/*
 * Divide q by num/den
 * - num must be more than LONG_MIN
 * - den must be non-zero
 * - num and den must have no common factor
 */
void mpq_div_si(mpq_t q, long num, unsigned long den) {
  mpz_ptr num_q, den_q;
  unsigned long gcd, abs_num;

  int retcode;
  int32_t icheck, iaux;
  mpq_ptr check, aux;

  retcode = mpq_pool_borrow(&icheck, &check);
  if(retcode != 0){
    fprintf(stderr, "mpq_div_si: mpq_pool_borrow failed");
    abort();
  }

  retcode = mpq_pool_borrow(&iaux, &aux);
  if(retcode != 0){
    fprintf(stderr, "mpq_div_si: mpq_pool_borrow failed");
    abort();
  }

#ifdef DEBUG
  mpq_set_si(aux, num, den);
  mpq_div(check, q, aux);
#endif

  num_q = mpq_numref(q);
  den_q = mpq_denref(q);
  abs_num = (unsigned long) labs(num);

  if (abs_num != 1) {
    gcd = mpz_gcd_ui(NULL, num_q, abs_num);
    abs_num /= gcd;
    mpz_divexact_ui(num_q, num_q, gcd);
  }

  if (den != 1) {
    gcd = mpz_gcd_ui(NULL, den_q, den);
    den /= gcd;
    mpz_divexact_ui(den_q, den_q, gcd);
  }

  mpz_mul_ui(num_q, num_q, den);
  mpz_mul_ui(den_q, den_q, abs_num);
  if (num < 0) {
    mpz_neg(num_q, num_q);
  }

  check_result(q, check);

  retcode = mpq_pool_return(icheck);
  if(retcode != 0){
    fprintf(stderr, "mpq_div_si: mpq_pool_return failed");
    abort();
  }

  retcode = mpq_pool_return(iaux);
  if(retcode != 0){
    fprintf(stderr, "mpq_div_si: mpq_pool_return failed");
    abort();
  }
}



#if ULONG_SIZE == 4

/*
 * FOR 32BIT LONG
 */

/*
 * Assignment from 64bit integers: assign num/den to q
 * - den must be non-zero
 * - if num and den have common factors, then q must be
 * made canonical using mpq_canonicalize.
 * This needs to be defined only if longs/unsigned longs
 * are 32bits. Otherwise, mpq_set_si works fine.
 */
void mpq_set_int64(mpq_t q, int64_t num, uint64_t den) {
  uint64_t absnum;

  int retcode;
  int32_t iz0;
  mpz_ptr z0;

  retcode = mpz_pool_borrow(&iz0, &z0);
  if(retcode != 0){
    fprintf(stderr, "mpq_set_int64: mpz_pool_borrow failed");
    abort();
  }

  /*
   * Note: the following assignment works even when num = INT64_MIN
   * in this case, we get
   *     num = - (2^63)
   *  (- num) = - (2^63) (because of overflow)
   * but when interpreted as an unsigned number,
   *  (uint64_t) (- num) = 2^63, which is correct.
   *
   * Note: the C standard does guarantee that - (2^63) is - (2^63)
   * but it seems to be the case on all machines I've tried.
   */
  absnum = (num >= 0) ? (uint64_t) num : (uint64_t) (- num);

  //  printf("- num = %lld, absnum = %llu\n", - num, absnum);

  mpz_set_ui(z0, (long) (absnum >> 32)); // high order bits of absnum
  mpz_mul_2exp(z0, z0, 32);
  mpz_add_ui(mpq_numref(q), z0, (unsigned long)(absnum & (~ 0))); // mask high order bits

  if (num < 0) {
    mpz_neg(mpq_numref(q), mpq_numref(q));
  }

  mpz_set_ui(z0, (unsigned long) (den >> 32));
  mpz_mul_2exp(z0, z0, 32);
  mpz_add_ui(mpq_denref(q), z0, (unsigned long)(den & (~ 0)));

  retcode = mpz_pool_return(iz0);
  if(retcode != 0){
    fprintf(stderr, "mpq_set_int64: mpz_pool_return failed");
    abort();
  }


}


/*
 * Converse operation: convert q to num/den
 * - num = 64bit signed integer
 * - den = 64bit unsigned integer
 */
void mpq_get_int64(mpq_t q, int64_t *num, uint64_t *den) {
  unsigned long a, b;
  uint64_t aux;

  int retcode;
  int32_t iz0;
  mpz_ptr z0;

  retcode = mpz_pool_borrow(&iz0, &z0);
  if(retcode != 0){
    fprintf(stderr, "mpq_get_int64: mpz_pool_borrow failed");
    abort();
  }


  // convert the numerator
  mpz_abs(z0, mpq_numref(q));
  a = mpz_get_ui(z0);            // a = 32 lower order bits
  mpz_fdiv_q_2exp(z0, z0, 32);   // arithmetic shift
  b = mpz_get_ui(z0);            // b = 32 higher order bits
  aux = (((uint64_t) b) << 32) | ((uint64_t) a);
  if (mpq_is_neg(q)) {
    *num = -aux;
  } else {
    *num = aux;
  }

  // convert the denominator
  mpz_set(z0, mpq_denref(q));
  a = mpz_get_ui(z0);
  mpz_fdiv_q_2exp(z0, z0, 32);
  b = mpz_get_ui(z0);
  *den = (((uint64_t) b) << 32) | ((uint64_t) a);

  retcode = mpz_pool_return(iz0);
  if(retcode != 0){
    fprintf(stderr, "mpq_get_int64: mpz_pool_return failed");
    abort();
  }
}


/*
 * Check whether num/den fit into 32 bit numbers
 */
bool mpq_fits_int32(mpq_t q) {
  return mpz_fits_slong_p(mpq_numref(q)) && mpz_fits_ulong_p(mpq_denref(q));
}


/*
 * Check whether q can be converted into two 64bit integers num/den
 */
bool mpq_fits_int64(mpq_t q) {
  bool retval;
  int retcode;
  int32_t iz0;
  mpz_ptr z0;

  retcode = mpz_pool_borrow(&iz0, &z0);
  if(retcode != 0){
    fprintf(stderr, "mpq_add_si: mpz_pool_borrow failed");
    abort();
  }


  mpz_fdiv_q_2exp(z0, mpq_numref(q), 32); // z0 = numerator>>32
  if (mpz_fits_slong_p(z0)) {
    mpz_fdiv_q_2exp(z0, mpq_denref(q), 32); // denominator >> 32
    retval = mpz_fits_ulong_p(z0);
  } else {
    retval = false;
  }

  retcode = mpz_pool_return(iz0);
  if(retcode != 0){
    fprintf(stderr, "mpq_add_si: mpz_pool_return failed");
    abort();
  }

  return retval;
}


/*
 * Check whether q is convertible to a 32bit integer
 * - the numerator fits into a 32bit number and the denominator is 1
 */
bool mpq_is_int32(mpq_t q) {
  return mpz_fits_slong_p(mpq_numref(q)) && mpz_cmp_ui(mpq_denref(q), 1UL) == 0;
}


/*
 * Check whether q is convertible to a 64bit integer
 * - i.e., the numerator fits into a 64bit number and the denominator is 1
 */
bool mpq_is_int64(mpq_t q) {
  bool retval;
  int retcode;
  int32_t iz0;
  mpz_ptr z0;

  retcode = mpz_pool_borrow(&iz0, &z0);
  if(retcode != 0){
    fprintf(stderr, "mpq_is_int64: mpz_pool_borrow failed");
    abort();
  }

  if (mpz_cmp_ui(mpq_denref(q), 1UL) == 0) {
    mpz_fdiv_q_2exp(z0, mpq_numref(q), 32); // z0 = numerator >> 32
    retval = mpz_fits_slong_p(z0);
  } else {
    retval = false;
  }


  retcode = mpz_pool_return(iz0);
  if(retcode != 0){
    fprintf(stderr, "mpq_is_int64: mpz_pool_return failed");
    abort();
  }
  return retval;
}


#else

/*
 * FOR 64BIT LONG
 */

bool mpq_fits_int32(mpq_t q) {
  signed long num;
  unsigned long den;

  if (mpz_fits_slong_p(mpq_numref(q)) && mpz_fits_ulong_p(mpq_denref(q))) {
    num = mpz_get_si(mpq_numref(q));
    den = mpz_get_ui(mpq_denref(q));
    return INT32_MIN <= num && num <= INT32_MAX && den <= UINT32_MAX;
  } else {
    return false;
  }
}

bool mpq_fits_int64(mpq_t q) {
  return mpz_fits_slong_p(mpq_numref(q)) && mpz_fits_ulong_p(mpq_denref(q));
}


/*
 * Check whether q is convertible to a 32bit integer
 * - the numerator fits into a 32bit number and the denominator is 1
 */
bool mpq_is_int32(mpq_t q) {
  signed long num;

  if (mpz_fits_slong_p(mpq_numref(q)) && mpz_cmp_ui(mpq_denref(q), 1UL) == 0) {
    num = mpz_get_si(mpq_numref(q));
    return INT32_MIN <= num && num <= INT32_MAX;
  } else {
    return false;
  }
}


/*
 * Check whether q is convertible to a 64bit integer
 * - i.e., the numerator fits into a 64bit number and the denominator is 1
 */
bool mpq_is_int64(mpq_t q) {
  return mpz_fits_slong_p(mpq_numref(q)) && mpz_cmp_ui(mpq_denref(q), 1UL) == 0;
}



#endif
