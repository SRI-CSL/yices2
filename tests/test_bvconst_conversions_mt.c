/*
 * Test conversion of bit-vector constants to mpz
 */

#include <stdlib.h>
#include <stdio.h>
#include <gmp.h>
#include <inttypes.h>
#include <assert.h>
#include <errno.h>
#include <string.h>
#include <pthread.h>

#include "bv_constants.h"

/*
 * Initialize z and copy a into z
 * - a is interpreted as an unsigned n-bit integer
 * - a must be normalized modulo (2^n)
 */
static inline void unsigned_bv2mpz(mpz_t z, uint32_t n, uint32_t *a) {
  uint32_t k;

  k = (n + 31) >> 5;
  mpz_init(z);
  bvconst_get_mpz(a, k, z);
}

/*
 * Initialize z and copy a into z
 * - a is interpreted as a signed n-bit integer
 * - a must be normalized modulo (2^n)
 */
static void signed_bv2mpz(mpz_t z, uint32_t n, uint32_t *a) {
  mpz_t aux;
  uint32_t k;

  assert(n > 0);

  k = (n + 31) >> 5;
  mpz_init(z);
  bvconst_get_mpz(a, k, z);
  if (bvconst_tst_bit(a, n-1)) { // sign bit = 1
    mpz_init_set_si(aux, -1);
    mpz_mul_2exp(aux, aux, n);
    mpz_add(z, z, aux);
    mpz_clear(aux);
  }
}


/*
 * Test convertions to mpz
 */
static void test_signed_conversion(FILE* output, uint32_t *a, uint32_t n) {
  mpz_t z;

  fprintf(output, "Signed conversion: ");
  bvconst_print(output, a, n);
  signed_bv2mpz(z, n, a);
  fprintf(output, " = ");
  mpz_out_str(output, 10, z);
  fprintf(output, "\n");
  mpz_clear(z);
}

static void test_signed_conversions(FILE* output) {
  uint32_t a[4];

  bvconst_clear(a, 2);
  test_signed_conversion(output, a, 1);
  test_signed_conversion(output, a, 2);
  test_signed_conversion(output, a, 30);
  test_signed_conversion(output, a, 31);
  test_signed_conversion(output, a, 32);
  test_signed_conversion(output, a, 33);
  test_signed_conversion(output, a, 64);

  bvconst_set_one(a, 2);
  test_signed_conversion(output, a, 1);
  test_signed_conversion(output, a, 2);
  test_signed_conversion(output, a, 30);
  test_signed_conversion(output, a, 31);
  test_signed_conversion(output, a, 32);
  test_signed_conversion(output, a, 33);
  test_signed_conversion(output, a, 64);

  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 2);
  test_signed_conversion(output, a, 2);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 30);
  test_signed_conversion(output, a, 30);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 31);
  test_signed_conversion(output, a, 31);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 32);
  test_signed_conversion(output, a, 32);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 33);
  test_signed_conversion(output, a, 33);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 64);
  test_signed_conversion(output, a, 64);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 1);
  bvconst_normalize(a, 2);
  test_signed_conversion(output, a, 2);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 29);
  bvconst_normalize(a, 30);
  test_signed_conversion(output, a, 30);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 30);
  bvconst_normalize(a, 31);
  test_signed_conversion(output, a, 31);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 31);
  bvconst_normalize(a, 32);
  test_signed_conversion(output, a, 32);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 32);
  bvconst_normalize(a, 33);
  test_signed_conversion(output, a, 33);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 63);
  bvconst_normalize(a, 64);
  test_signed_conversion(output, a, 64);
}

/*
 * Test convertions to mpz
 */
static void test_unsigned_conversion(FILE* output, uint32_t *a, uint32_t n) {
  mpz_t z;

  fprintf(output, "Unsigned conversion: ");
  bvconst_print(output, a, n);
  unsigned_bv2mpz(z, n, a);
  fprintf(output, " = ");
  mpz_out_str(output, 10, z);
  fprintf(output, "\n");
  mpz_clear(z);
}

static void test_unsigned_conversions(FILE* output) {
  uint32_t a[4];

  bvconst_clear(a, 2);
  test_unsigned_conversion(output, a, 1);
  test_unsigned_conversion(output, a, 2);
  test_unsigned_conversion(output, a, 30);
  test_unsigned_conversion(output, a, 31);
  test_unsigned_conversion(output, a, 32);
  test_unsigned_conversion(output, a, 33);
  test_unsigned_conversion(output, a, 64);

  bvconst_set_one(a, 2);
  test_unsigned_conversion(output, a, 1);
  test_unsigned_conversion(output, a, 2);
  test_unsigned_conversion(output, a, 30);
  test_unsigned_conversion(output, a, 31);
  test_unsigned_conversion(output, a, 32);
  test_unsigned_conversion(output, a, 33);
  test_unsigned_conversion(output, a, 64);

  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 2);
  test_unsigned_conversion(output, a, 2);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 30);
  test_unsigned_conversion(output, a, 30);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 31);
  test_unsigned_conversion(output, a, 31);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 32);
  test_unsigned_conversion(output, a, 32);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 33);
  test_unsigned_conversion(output, a, 33);
  bvconst_set_minus_one(a, 2);
  bvconst_normalize(a, 64);
  test_unsigned_conversion(output, a, 64);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 1);
  bvconst_normalize(a, 2);
  test_unsigned_conversion(output, a, 2);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 29);
  bvconst_normalize(a, 30);
  test_unsigned_conversion(output, a, 30);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 30);
  bvconst_normalize(a, 31);
  test_unsigned_conversion(output, a, 31);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 31);
  bvconst_normalize(a, 32);
  test_unsigned_conversion(output, a, 32);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 32);
  bvconst_normalize(a, 33);
  test_unsigned_conversion(output, a, 33);

  bvconst_clear(a, 2);
  bvconst_set_bit(a, 63);
  bvconst_normalize(a, 64);
  test_unsigned_conversion(output, a, 64);
}

void* test_thread(void* arg){
  FILE* output = (FILE *)arg;
  fprintf(stderr, "Starting: %s\n", "test_signed_conversions");
  test_signed_conversions(output);
  fprintf(stderr, "Starting: %s\n", "test_unsigned_conversions");
  test_unsigned_conversions(output);
  fprintf(stderr, "Done.\n");
  return NULL;
}

#define NTHREADS  2


int main() {
  int retcode, thread;
  char  buff[1024];
  FILE*  outfp[NTHREADS];
  pthread_t tids[NTHREADS];

  printf("%d threads\n", NTHREADS);

  for(thread = 0; thread < NTHREADS; thread++){
    snprintf(buff, 1024, "/tmp/test_bvconst_conversions_mt_%d.txt", thread);
    printf("Logging thread %d to %s\n", thread, buff);
    outfp[thread] = fopen(buff, "w");
    if(outfp[thread] == NULL){
      fprintf(stderr, "fopen failed: %s\n", strerror(errno));
      exit(0);
    }
    retcode =  pthread_create(&tids[thread], NULL, test_thread, outfp[thread]);
    if(retcode){
      fprintf(stderr, "pthread_create failed: %s\n", strerror(retcode));
      exit(0);
    }
  }

  printf("threads away\n\n");


  for(thread = 0; thread < NTHREADS; thread++){
    retcode = pthread_join(tids[thread], NULL);
    if(retcode){
      fprintf(stderr, "pthread_join failed: %s\n", strerror(retcode));
    }
    fclose(outfp[thread]);
  }

  return 0;
}
