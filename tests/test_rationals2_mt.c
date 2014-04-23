/*
 * More test of rational functions
 */

#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <inttypes.h>
#include <assert.h>
#include <gmp.h>

#include "assert_utils.h"
#include "rationals.h"
#include "mpq_aux.h"
#include "mpq_pool.h"
#include "mpz_pool.h"
#include "threads.h"


#define MAX_NUMERATOR (INT32_MAX>>1)
#define MIN_NUMERATOR (-MAX_NUMERATOR)
#define MAX_DENOMINATOR MAX_NUMERATOR



/*
 * Tests
 */
static void q_check_equal(FILE* output, rational_t *r, mpq_t q) {
  int32_t equal;
  if (r->den == 0) {
    equal = mpq_equal(fetch_mpq(r->num), q);
  } else {
    equal = (mpq_cmp_si(q, r->num, r->den) == 0);
  }
  if (! equal) {
    fprintf(output, "q_check_error\n");
    fprintf(output, "  r = ");
    q_print(output, r);
    fprintf(output, "\n");
    fprintf(output, "  q = ");
    mpq_out_str(output, 10, q);
    fprintf(output, "\n");
    fflush(output);
    abort();
  }
}



static void test_equal(FILE* output, rational_t *r, mpz_t z) {
  //  fprintf(output, "  r = "); q_print(output, r); fprintf(output, "\n");
  //  fprintf(output, "  q = "); mpq_out_str(output, 10, q); fprintf(output, "\n");
  //  fflush(output);

  int32_t iq0;
  mpq_ptr q0;

  mpq_pool_borrow(&iq0, &q0);

  mpq_set_z(q0, z);
  q_check_equal(output, r, q0);


  mpq_pool_return(iq0);

}


/*
 * Non-zero integers to use for testing
 */
static int32_t num[48] = {
  1, -1, -23, 23, 112, -112, 126, -126,
  INT32_MAX, INT32_MIN, INT32_MAX-1, INT32_MIN + 1,
  MAX_NUMERATOR, MIN_NUMERATOR,
  MAX_NUMERATOR - 1, MIN_NUMERATOR + 1, MAX_NUMERATOR + 1,
  MIN_NUMERATOR - 1, MAX_NUMERATOR + 2, MIN_NUMERATOR - 2,
  6, 12, 15, 30, 60, 90, 150, 270, 300, 432, 500,
  -6, -12, -15, -30, -60, -90, -150, -270, -300, -432, -500,
  7, -49, 343, -6517, 148877, -148877,
};


// large numbers
static char *big_num[14] = {
  "42674688000",
  "624800107008000",
  "1008826757081171875",
  "39212228123683729",
  "5992830235524142758386850633773258681119",
  "64495327731887693539738558691066839103388567300449",
  "470287785858076441566723507866751092927015824834881906763507",
  "6010808726230715186662011185674578457162357",
  "47286313109628773476339035575625855931454528239",
  "35184372088832",
  "712483534798848",
  "15199648742375424",
  "18446744073709551616",
  "9223372036854775808",
};


/*
 * Test of gcd code
 */
static void test_gcd(FILE* output) {
  uint32_t i, j;
  int32_t code;
  rational_t r0, r1;

  int32_t iz0, iz1, iz2;
  mpz_ptr z0, z1, z2;

  q_init(&r0);
  q_init(&r1);


  mpz_pool_borrow(&iz0, &z0);
  mpz_pool_borrow(&iz1, &z1);
  mpz_pool_borrow(&iz2, &z2);


  // gcd(num[i], num[j])
  for (i=0; i<48; i++) {
    for (j=0; j<48; j++) {
      q_set32(&r0, num[i]);
      q_set32(&r1, num[j]);
      q_gcd(&r0, &r1);
      // print result
      fprintf(output, "gcd(%"PRId32", %"PRId32") = ", num[i], num[j]);
      q_print(output, &r0);
      fprintf(output, "\n");
      // check
      mpz_set_si(z0, num[i]);
      mpz_set_si(z1, num[j]);
      mpz_gcd(z2, z0, z1);
      test_equal(output, &r0, z2);
    }
  }

  // gcd(num[i], big_num[j])
  for (i=0; i<48; i++) {
    for (j=0; j<14; j++) {
      q_set32(&r0, num[i]);
      code = q_set_from_string(&r1, big_num[j]);
      assert_true(code == 0);
      q_gcd(&r0, &r1);
      // print
      fprintf(output, "gcd(%"PRId32", %s) = ", num[i], big_num[j]);
      q_print(output, &r0);
      fprintf(output, "\n");
      // check
      mpz_set_si(z0, num[i]);
      mpz_set_str(z1, big_num[j], 10);
      mpz_gcd(z2, z0, z1);
      test_equal(output, &r0, z2);
    }
  }

  // gcd(big_num[i], num[j])
  for (i=0; i<14; i++) {
    for (j=0; j<48; j++) {
      code = q_set_from_string(&r0, big_num[i]);
      assert_true(code == 0);
      q_set32(&r1, num[j]);
      q_gcd(&r0, &r1);
      // print
      fprintf(output, "gcd(%s, %"PRId32") = ", big_num[i], num[j]);
      q_print(output, &r0);
      fprintf(output, "\n");
      // check
      mpz_set_str(z0, big_num[i], 10);
      mpz_set_si(z1, num[j]);
      mpz_gcd(z2, z0, z1);
      test_equal(output, &r0, z2);
    }
  }

  // gcd(big_num[i], big_num[j])
  for (i=0; i<14; i++) {
    for (j=0; j<14; j++) {
      code = q_set_from_string(&r0, big_num[i]);
      assert_true(code == 0);
      code = q_set_from_string(&r1, big_num[j]);
      assert_true(code == 0);
      q_gcd(&r0, &r1);
      // print
      fprintf(output, "gcd(%s, %s) = ", big_num[i], big_num[j]);
      q_print(output, &r0);
      fprintf(output, "\n");
      // check
      mpz_set_str(z0, big_num[i], 10);
      mpz_set_str(z1, big_num[j], 10);
      mpz_gcd(z2, z0, z1);
      test_equal(output, &r0, z2);
    }
  }

  mpz_pool_return(iz0);
  mpz_pool_return(iz1);
  mpz_pool_return(iz2);

}


/*
 * Test of lcm code
 */
static void test_lcm(FILE* output) {
  uint32_t i, j;
  int32_t code;
  rational_t r0, r1;
  int32_t iz0, iz1, iz2;
  mpz_ptr z0, z1, z2;

  q_init(&r0);
  q_init(&r1);

  mpz_pool_borrow(&iz0, &z0);
  mpz_pool_borrow(&iz1, &z1);
  mpz_pool_borrow(&iz2, &z2);

  // lcm(num[i], num[j])
  for (i=0; i<48; i++) {
    for (j=0; j<48; j++) {
      q_set32(&r0, num[i]);
      q_set32(&r1, num[j]);
      q_lcm(&r0, &r1);
      // print result
      fprintf(output, "lcm(%"PRId32", %"PRId32") = ", num[i], num[j]);
      q_print(output, &r0);
      fprintf(output, "\n");
      // check
      mpz_set_si(z0, num[i]);
      mpz_set_si(z1, num[j]);
      mpz_lcm(z2, z0, z1);
      test_equal(output, &r0, z2);
    }
  }

  // lcm(num[i], big_num[j])
  for (i=0; i<48; i++) {
    for (j=0; j<14; j++) {
      q_set32(&r0, num[i]);
      code = q_set_from_string(&r1, big_num[j]);
      assert_true(code == 0);
      q_lcm(&r0, &r1);
      // print
      fprintf(output, "lcm(%"PRId32", %s) = ", num[i], big_num[j]);
      q_print(output, &r0);
      fprintf(output, "\n");
      // check
      mpz_set_si(z0, num[i]);
      mpz_set_str(z1, big_num[j], 10);
      mpz_lcm(z2, z0, z1);
      test_equal(output, &r0, z2);
    }
  }

  // lcm(big_num[i], num[j])
  for (i=0; i<14; i++) {
    for (j=0; j<48; j++) {
      code = q_set_from_string(&r0, big_num[i]);
      assert_true(code == 0);
      q_set32(&r1, num[j]);
      q_lcm(&r0, &r1);
      // print
      fprintf(output, "lcm(%s, %"PRId32") = ", big_num[i], num[j]);
      q_print(output, &r0);
      fprintf(output, "\n");
      // check
      mpz_set_str(z0, big_num[i], 10);
      mpz_set_si(z1, num[j]);
      mpz_lcm(z2, z0, z1);
      test_equal(output, &r0, z2);
    }
  }

  // lcm(big_num[i], big_num[j])
  for (i=0; i<14; i++) {
    for (j=0; j<14; j++) {
      code = q_set_from_string(&r0, big_num[i]);
      assert_true(code == 0);
      code = q_set_from_string(&r1, big_num[j]);
      assert_true(code == 0);
      q_lcm(&r0, &r1);
      // print
      fprintf(output, "lcm(%s, %s) = ", big_num[i], big_num[j]);
      q_print(output, &r0);
      fprintf(output, "\n");
      // check
      mpz_set_str(z0, big_num[i], 10);
      mpz_set_str(z1, big_num[j], 10);
      mpz_lcm(z2, z0, z1);
      test_equal(output, &r0, z2);
    }
  }

  mpz_pool_return(iz0);
  mpz_pool_return(iz1);
  mpz_pool_return(iz2);

}


/*
 * Test of divides
 */
static void test_divides(FILE* output) {
  uint32_t i, j;
  int32_t code;
  bool result;
  rational_t r0, r1;
  int32_t iz0, iz1;
  mpz_ptr z0, z1;

  q_init(&r0);
  q_init(&r1);

  mpz_pool_borrow(&iz0, &z0);
  mpz_pool_borrow(&iz1, &z1);

  // divides(num[i], num[j])
  for (i=0; i<48; i++) {
    for (j=0; j<48; j++) {
      q_set32(&r0, num[i]);
      q_set32(&r1, num[j]);
      result = q_divides(&r0, &r1);
      // print result
      if (result) {
	fprintf(output, "%"PRId32" divides %"PRId32"\n", num[i], num[j]);
      } else {
	fprintf(output, "%"PRId32" does not divide %"PRId32"\n", num[i], num[j]);
      }
      // check
      mpz_set_si(z0, num[i]);
      mpz_set_si(z1, num[j]);
      if (mpz_divisible_p(z1, z0)) {
	assert(result);
      } else {
	assert(! result);
      }
    }
  }

  // divides(num[i], big_num[j])
  for (i=0; i<48; i++) {
    for (j=0; j<14; j++) {
      q_set32(&r0, num[i]);
      code = q_set_from_string(&r1, big_num[j]);
      assert_true(code == 0);
      result = q_divides(&r0, &r1);
      // print
      if (result) {
	fprintf(output, "%"PRId32" divides %s\n", num[i], big_num[j]);
      } else {
	fprintf(output, "%"PRId32" does not divide %s\n", num[i], big_num[j]);
      }
      // check
      mpz_set_si(z0, num[i]);
      mpz_set_str(z1, big_num[j], 10);
      if (mpz_divisible_p(z1, z0)) {
	assert(result);
      } else {
	assert(! result);
      }
    }
  }

  // gcd(big_num[i], num[j])
  for (i=0; i<14; i++) {
    for (j=0; j<48; j++) {
      code = q_set_from_string(&r0, big_num[i]);
      assert_true(code == 0);
      q_set32(&r1, num[j]);
      result = q_divides(&r0, &r1);
      // print
      if (result) {
	fprintf(output, "%s divides %"PRId32"\n", big_num[i], num[j]);
      } else {
	fprintf(output, "%s does not divide %"PRId32"\n", big_num[i], num[j]);
      }
      // check
      mpz_set_str(z0, big_num[i], 10);
      mpz_set_si(z1, num[j]);
      if (mpz_divisible_p(z1, z0)) {
	assert(result);
      } else {
	assert(! result);
      }
    }
  }

  // gcd(big_num[i], big_num[j])
  for (i=0; i<14; i++) {
    for (j=0; j<14; j++) {
      code = q_set_from_string(&r0, big_num[i]);
      assert_true(code == 0);
      code = q_set_from_string(&r1, big_num[j]);
      assert_true(code == 0);
      result = q_divides(&r0, &r1);
      // print
      if (result) {
	fprintf(output, "%s divides %s\n", big_num[i], big_num[j]);
      } else {
	fprintf(output, "%s does not divide %s\n", big_num[i], big_num[j]);
      }
      // check
      mpz_set_str(z0, big_num[i], 10);
      mpz_set_str(z1, big_num[j], 10);
      if (mpz_divisible_p(z1, z0)) {
	assert(result);
      } else {
	assert(! result);
      }
    }
  }

  mpz_pool_return(iz0);
  mpz_pool_return(iz1);

}



yices_thread_result_t YICES_THREAD_ATTR test_thread(void* arg){
  thread_data_t* tdata = (thread_data_t *)arg;
  FILE* output = tdata->output;

  fprintf(stderr, "Starting: %s\n", "test_gcd");
  test_gcd(output);
  fprintf(stderr, "Starting: %s\n", "test_lcm");
  test_lcm(output);
  fprintf(stderr, "Starting: %s\n", "test_divides");
  test_divides(output);
  fprintf(stderr, "Done.\n");
  return yices_thread_exit();
}


int main(int argc, char* argv[]) {

  if(argc != 2){
    mt_test_usage(argc, argv);
    return 0;
  } else {
    int32_t nthreads = atoi(argv[1]);

    init_rationals();

    if(nthreads < 0){
      fprintf(stderr, "thread number must be positive!\n");
      exit(EXIT_FAILURE);
    } else if(nthreads == 0){
      thread_data_t tdata = {0, stdout};
      test_thread(&tdata);
    } else {
      launch_threads(nthreads, "test_rationals2_mt", test_thread);
    }

    cleanup_rationals();
  }

  return 0;
}
