/*
 * (Multithreaded) Test of rational functions
 */

#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <inttypes.h>
#include <gmp.h>

#include "rationals.h"
#include "mpq_aux.h"
#include "mpq_pool.h"
#include "mpz_pool.h"
#include "threads.h"

#define MAX_NUMERATOR (INT32_MAX>>1)
#define MIN_NUMERATOR (-MAX_NUMERATOR)
#define MAX_DENOMINATOR MAX_NUMERATOR


static int32_t num[24] = {
  0, 1, -1, -23, 23,
  112, -112, 126, -126, INT32_MAX,
  INT32_MIN, MAX_NUMERATOR, MIN_NUMERATOR, MAX_NUMERATOR - 1, MIN_NUMERATOR + 1,
  MAX_NUMERATOR + 1, MIN_NUMERATOR - 1, MAX_NUMERATOR + 2, MIN_NUMERATOR - 2,
  INT32_MAX-1, INT32_MIN + 1, 100, 1000, 10000,
};

static uint32_t den[16] = {
  1, 100, 1000, 10000, 126, 112, 23, 25, UINT32_MAX,
  INT32_MAX, INT32_MAX - 1, ((uint32_t) INT32_MAX) + 1, ((uint32_t) INT32_MAX) + 2,
  MAX_DENOMINATOR, MAX_DENOMINATOR - 1, MAX_DENOMINATOR + 1,
};

static char* test_strings[12] = {
  "1/10", "+1/10", "-1/10",
  "1889139832988/137873278932897", "8eeee/8792183jeebag",
  "00001893821/000031278781238", "",
  "+11398990", "-1893983982", "819230982139",
  "46878952/46878952", "-46878952/46878952",
};

static char* test_strings2[22] = {
  "1.10", "+1.10", "-1.10",
  "100e0", "100e-2", "100e+2",
  "10.6e0", "10.6e-2", "10.6e+2",
  "+10.6e0", "+10.6e-2", "+10.6e+2",
  "-10.6e0", "-10.6e-2", "-10.6e+2",
  "1889139832988.137873278932897e-4", "8.eee",
  "00001893821/000031278781238", "",
  "46878952/46878952", "+46878952/46878952", "-46878952/46878952",
};


/*
 * Tests
 */
static void q_export(rational_t *r, mpq_t q) {
  if (r->den == 0) {
    mpq_set(q, fetch_mpq(r->num));
  } else {
    mpq_set_int32(q, r->num, r->den);
  }
}

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


static void test_equal(FILE* output, rational_t *r, mpq_t q) {
  //  printf("  r = "); q_print(stdout, r); printf("\n");
  //  printf("  q = "); mpq_out_str(stdout, 10, q); printf("\n");
  //  fflush(stdout);
  q_check_equal(output, r, q);
}

// set r0 = num/den
static void test_assign(FILE* output, int32_t num, uint32_t den) {
  rational_t r0;

  int32_t iq0;
  mpq_ptr q0;

  q_init(&r0);

  mpq_pool_borrow(&iq0, &q0);

  q_set_int32(&r0, num, den);
  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  fprintf(output, "test assign: %"PRId32"/%"PRIu32"\n", num, den);
  test_equal(output, &r0, q0);

  mpq_pool_return(iq0);

}

// compute r0 = r1 + num/den
static void test_add(FILE* output, int32_t num, uint32_t den) {
  rational_t r0, r1;

  int32_t iq0, iq1;
  mpq_ptr q0, q1;

  q_init(&r0);
  q_init(&r1);

  mpq_pool_borrow(&iq0, &q0);
  mpq_pool_borrow(&iq1, &q1);

  q_set_int32(&r0, num, den);
  q_add(&r0, &r1);
  fprintf(output, "test add: %"PRId32"/%"PRIu32" + ", num, den);
  q_print(output, &r1);
  fprintf(output, " = ");
  q_print(output, &r0);
  fprintf(output, "\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  q_export(&r1, q1);
  mpq_canonicalize(q1);
  mpq_add(q0, q0, q1);
  test_equal(output, &r0, q0);


  mpq_pool_return(iq0);
  mpq_pool_return(iq1);

}



// compute r0 = num/den - r1
static void test_sub(FILE* output, int32_t num, uint32_t den) {
  rational_t r0, r1;

  int32_t iq0, iq1;
  mpq_ptr q0, q1;

  q_init(&r0);
  q_init(&r1);

  mpq_pool_borrow(&iq0, &q0);
  mpq_pool_borrow(&iq1, &q1);

  q_set_int32(&r0, num, den);
  q_sub(&r0, &r1);
  fprintf(output, "test sub: %"PRId32"/%"PRIu32" - ", num, den);
  q_print(output, &r1);
  fprintf(output, " = ");
  q_print(output, &r0);
  fprintf(output, "\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  q_export(&r1, q1);
  mpq_canonicalize(q1);
  mpq_sub(q0, q0, q1);
  test_equal(output, &r0, q0);

  mpq_pool_return(iq0);
  mpq_pool_return(iq1);


}

// compute r0 = r1 - num/den
static void test_sub2(FILE* output, int32_t num, uint32_t den) {
  rational_t r0, r1, r2;


  int32_t iq0, iq1;
  mpq_ptr q0, q1;

  q_init(&r0);
  q_init(&r1);
  q_init(&r2);

  mpq_pool_borrow(&iq0, &q0);
  mpq_pool_borrow(&iq1, &q1);

  q_set(&r0, &r1);
  q_set_int32(&r2, num, den);
  q_sub(&r0, &r2);
  fprintf(output, "test sub2: ");
  q_print(output, &r1);
  fprintf(output, " - %"PRId32"/%"PRIu32" = ", num, den);
  q_print(output, &r0);
  fprintf(output, "\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  q_export(&r1, q1);
  mpq_canonicalize(q1);
  mpq_sub(q0, q1, q0);
  test_equal(output, &r0, q0);

  mpq_pool_return(iq0);
  mpq_pool_return(iq1);
}



// r0 = num/den * r1
static void test_mul(FILE* output, int32_t num, uint32_t den) {
  rational_t r0, r1;

  int32_t iq0, iq1;
  mpq_ptr q0, q1;

  q_init(&r0);
  q_init(&r1);

  mpq_pool_borrow(&iq0, &q0);
  mpq_pool_borrow(&iq1, &q1);

  q_set_int32(&r0, num, den);
  q_mul(&r0, &r1);
  fprintf(output, "test mul: %"PRId32"/%"PRIu32" * ", num, den);
  q_print(output, &r1);
  fprintf(output, " = ");
  q_print(output, &r0);
  fprintf(output, "\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  q_export(&r1, q1);
  mpq_canonicalize(q1);
  mpq_mul(q0, q0, q1);
  test_equal(output, &r0, q0);

  mpq_pool_return(iq0);
  mpq_pool_return(iq1);

}

// r0 = (num/den) / r1
static void test_div(FILE* output, int32_t num, uint32_t den, rational_t r1) {
  rational_t r0;

  int32_t iq0, iq1;
  mpq_ptr q0, q1;
  fprintf(output, "test div: >(num = %"PRId32" den = %"PRIu32") / ", num, den);

  q_init(&r0);

  mpq_pool_borrow(&iq0, &q0);
  mpq_pool_borrow(&iq1, &q1);

  q_set_int32(&r0, num, den);
  q_div(&r0, &r1);
  fprintf(output, "test div: <(%"PRId32"/%"PRIu32") / ", num, den);
  q_print(output, &r1);
  fprintf(output, " = ");
  q_print(output, &r0);
  fprintf(output, "\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  q_export(&r1, q1);
  mpq_div(q0, q0, q1);
  test_equal(output, &r0, q0);

  mpq_pool_return(iq0);
  mpq_pool_return(iq1);

}

// r0 = r1 / (num/den)
static void test_div2(FILE* output, int32_t num, uint32_t den, rational_t r1) {
  rational_t r0, r2;

  int32_t iq0, iq1;
  mpq_ptr q0, q1;

  q_init(&r0);
  q_init(&r2);

  mpq_pool_borrow(&iq0, &q0);
  mpq_pool_borrow(&iq1, &q1);

  q_set(&r0, &r1);
  q_set_int32(&r2, num, den);
  q_div(&r0, &r2);
  fprintf(output, "test div: ");
  q_print(output, &r1);
  fprintf(output, " / (%"PRId32"/%"PRIu32") = ", num, den);
  q_print(output, &r0);
  fprintf(output, "\n");

  mpq_set_si(q0, num, den);
  mpq_canonicalize(q0);
  q_export(&r1, q1);
  mpq_div(q0, q1, q0);
  test_equal(output, &r0, q0);

  mpq_pool_return(iq0);
  mpq_pool_return(iq1);

}

// r0 = (num1/den1) + r1 * (num2/den2)
static void test_addmul(FILE* output, int32_t num1, uint32_t den1, int32_t num2, uint32_t den2) {
  rational_t r0, r1, r2;

  int32_t iq0, iq1, iq2;
  mpq_ptr q0, q1, q2;


  q_init(&r0);
  q_init(&r1);
  q_init(&r2);

  mpq_pool_borrow(&iq0, &q0);
  mpq_pool_borrow(&iq1, &q1);
  mpq_pool_borrow(&iq2, &q2);

  q_set_int32(&r0, num1, den1);
  q_set_int32(&r2, num2, den2);
  q_addmul(&r0, &r1, &r2);
  fprintf(output, "test_addmul: %"PRId32"/%"PRIu32" + ", num1, den1);
  q_print(output, &r1);
  fprintf(output, " * %"PRId32"/%"PRIu32" = ", num2, den2);
  q_print(output, &r0);
  fprintf(output, "\n");

  mpq_set_si(q0, num1, den1);
  mpq_canonicalize(q0);
  mpq_set_si(q2, num2, den2);
  mpq_canonicalize(q2);
  q_export(&r1, q1);
  mpq_mul(q1, q1, q2);
  mpq_add(q0, q0, q1);
  test_equal(output, &r0, q0);

  mpq_pool_return(iq0);
  mpq_pool_return(iq1);
  mpq_pool_return(iq2);

}



static void assignment_tests(FILE* output) {
  int32_t i, j, a;
  uint32_t b;

  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      test_assign(output, a, b);
    }
  }
}

static void addition_test(FILE* output, int32_t num1, uint32_t den1) {
  int32_t i, j, a;
  uint32_t b;
  rational_t r1;
  q_init(&r1);

  q_set_int32(&r1, num1, den1);
  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      test_add(output, a, b);
    }
  }
}

static void addition_tests(FILE* output) {
  int32_t i, j, a;
  uint32_t b;

  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      addition_test(output, a, b);
    }
  }
}

static void subtraction_test(FILE* output, int32_t num1, uint32_t den1) {
  int32_t i, j, a;
  uint32_t b;
  rational_t r1;
  q_init(&r1);

  q_set_int32(&r1, num1, den1);
  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      test_sub(output, a, b);
      test_sub2(output, a, b);
    }
  }
}

static void subtraction_tests(FILE* output) {
  int32_t i, j, a;
  uint32_t b;

  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      subtraction_test(output, a, b);
    }
  }
}




static void product_test(FILE* output, int32_t num1, uint32_t den1) {
  int32_t i, j, a;
  uint32_t b;
  rational_t r1;
  q_init(&r1);

  q_set_int32(&r1, num1, den1);
  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      test_mul(output, a, b);
    }
  }
}

static void product_tests(FILE* output) {
  int32_t i, j, a;
  uint32_t b;

  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      product_test(output, a, b);
    }
  }
}

static void division_test(FILE* output, int32_t num1, uint32_t den1) {
  int32_t i, j, a;
  uint32_t b;
  rational_t r1;
  q_init(&r1);

  q_set_int32(&r1, num1, den1);
  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      if (num1 != 0) test_div(output, a, b, r1);
      if (a != 0) test_div2(output, a, b, r1);
    }
  }
}

static void division_tests(FILE* output) {
  int32_t i, j, a;
  uint32_t b;

  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      division_test(output, a, b);
    }
  }
}

static void addmul_test(FILE* output, int32_t num1, uint32_t den1) {
  int32_t i, j, a, b;
  uint32_t c, d;
  rational_t r1;
  q_init(&r1);

  q_set_int32(&r1, num1, den1);
  for (i=0; i<15; i++) {
    c = den[i];
    d = den[i+1];
    for (j=0; j<23; j++) {
      a = num[j];
      b = num[j+1];
      test_addmul(output, a, c, b, d);
    }
  }
}

static void addmul_tests(FILE* output) {
  int32_t i, j, a;
  uint32_t b;

  for (i=0; i<16; i++) {
    b = den[i];
    for (j=0; j<24; j++) {
      a = num[j];
      addmul_test(output, a, b);
    }
  }

}


void miscellaneous_tests(FILE* output){
    rational_t r0, r1, r2;
    int32_t i;

    int32_t iq0, iq1, iq2;
    mpq_ptr q0, q1, q2;


    q_init(&r0);
    q_init(&r1);
    q_init(&r2);

    mpq_pool_borrow(&iq0, &q0);
    mpq_pool_borrow(&iq1, &q1);
    mpq_pool_borrow(&iq2, &q2);

    q_set_int32(&r0, MIN_NUMERATOR-1, 23);
    fprintf(output, "r0 = ");
    q_print(output, &r0);
    fprintf(output, "\n");
    fprintf(output, "hash num = %"PRIu32"\n", q_hash_numerator(&r0));
    fprintf(output, "hash den = %"PRIu32"\n", q_hash_denominator(&r0));

    mpq_set_int32(q0, MIN_NUMERATOR-1, 23);
    mpq_canonicalize(q0);
    q_set_mpq(&r1, q0);
    fprintf(output, "r1 = ");
    q_print(output, &r1);
    fprintf(output, "\n");
    fprintf(output, "hash num = %"PRIu32"\n", q_hash_numerator(&r1));
    fprintf(output, "hash den = %"PRIu32"\n", q_hash_denominator(&r1));


    fprintf(output, "\n\n");
    for (i=0; i<12; i++) {
      fprintf(output, "set_from_string <%s>\n", test_strings[i]);
      if (q_set_from_string(&r2, test_strings[i]) >= 0) {
        fprintf(output, "r2 = ");
        q_print(output, &r2);
      } else {
        fprintf(output, "format error\n");
        fprintf(output, "r2 = ");
        q_print(output, &r2);
      }
      fprintf(output, "\n\n");
    }

    fprintf(output, "\n");
    for (i=0; i<22; i++) {
      fprintf(output, "set_from_float_string <%s>\n", test_strings2[i]);
      if (q_set_from_float_string(&r2, test_strings2[i]) >= 0) {
        fprintf(output, "r2 = ");
        q_print(output, &r2);
      } else {
        fprintf(output, "format error\n");
        fprintf(output, "r2 = ");
        q_print(output, &r2);
      }
      fprintf(output, "\n\n");
    }


    mpq_pool_return(iq0);
    mpq_pool_return(iq1);
    mpq_pool_return(iq2);

}

yices_thread_result_t YICES_THREAD_ATTR test_thread(void* arg){
  thread_data_t* tdata = (thread_data_t *)arg;
  FILE* output = tdata->output;

  fprintf(stderr, "Starting: %s\n", "assignment_tests");
  assignment_tests(output);
  fprintf(stderr, "Starting: %s\n", "addition_tests");
  addition_tests(output);
  fprintf(stderr, "Starting: %s\n", "subtraction_tests");
  subtraction_tests(output);
  fprintf(stderr, "Starting: %s\n", "product_tests");
  product_tests(output);
  fprintf(stderr, "Starting: %s\n", "division_tests");
  division_tests(output);
  fprintf(stderr, "Starting: %s\n", "addmul_tests");
  addmul_tests(output);
  fprintf(stderr, "Starting: %s\n", "miscellaneous_tests");
  miscellaneous_tests(output);
  fprintf(stderr, "Done.\n");

  return yices_thread_exit();
}


int main(int argc, char* argv[]) {

  if(argc != 2){
    mt_test_usage(argc, argv);
    return 0;
  } else {
    int32_t nthreads = atoi(argv[1]);

    printf("GMP %s (bits per limb = %"PRId32")\n", gmp_version, GMP_LIMB_BITS);
    printf("MAX_NUM = %d\n", MAX_NUMERATOR);
    printf("MIN_NUM = %d\n", MIN_NUMERATOR);
    printf("MAX_DEN = %d\n", MAX_DENOMINATOR);
    printf("----\n");

    init_rationals();

    if(nthreads < 0){
      fprintf(stderr, "thread number must be positive!\n");
      exit(EXIT_FAILURE);
    } else if(nthreads == 0){
      thread_data_t tdata = {0, stdout};
      test_thread(&tdata);
    } else {
      launch_threads(nthreads, "test_rationals_mt", test_thread);
    }

    cleanup_rationals();
  }

  return 0;
}



