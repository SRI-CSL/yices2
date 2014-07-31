/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test arithmetic on bit-vector constants
 */

#include <stdlib.h>
#include <stdio.h>
#include <gmp.h>
#include <assert.h>
#include <inttypes.h>

#include "terms/bv_constants.h"
#include "utils/memalloc.h"

#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline int random(void) {
  return rand();
}

#endif

//static uint32_t a[4] = { 0x00000000, 0x00000000, 0x00000000, 0x00000000 }; //0
//static uint32_t b[4] = { 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff }; //-1
//static uint32_t c[4] = { 0x00000001, 0x00000000, 0x00000000, 0x00000000 }; //+1
//static uint32_t d[4] = { 0x80000000, 0x00000000, 0x00000000, 0x00000000 }; //2^31
//static uint32_t e[4] = { 0x00000000, 0x00000001, 0x00000000, 0x00000000 }; //2^32

static uint32_t *a, *b, *c, *d, *e;

static mpz_t z0, z1, z2;
static int32_t vector[1024];

static void random_vector(int32_t *v, int32_t n) {
  int32_t i;

  for (i=0; i<n; i++) {
    v[i] = random() & 0x1;
  }
}

static void alloc_constants() {
  uint32_t i;

  init_bvconstants();
  //  a = (uint32_t *) safe_malloc(4 * sizeof(uint32_t));
  //  b = (uint32_t *) safe_malloc(4 * sizeof(uint32_t));
  //  c = (uint32_t *) safe_malloc(4 * sizeof(uint32_t));
  //  d = (uint32_t *) safe_malloc(4 * sizeof(uint32_t));
  //  e = (uint32_t *) safe_malloc(4 * sizeof(uint32_t));
  a = bvconst_alloc(4);
  b = bvconst_alloc(4);
  c = bvconst_alloc(4);
  d = bvconst_alloc(4);
  e = bvconst_alloc(4);

  for (i=0; i<4; i++) {
    a[i] = 0;
    b[i] = 0xffffffff;
    c[i] = 0;
    d[i] = 0;
    e[i] = 0;
  }

  c[0] = 1;
  d[0] = 0x80000000;
  e[1] = 1;
}

static void free_constants() {
  //  safe_free(a);
  //  safe_free(b);
  //  safe_free(c);
  //  safe_free(d);
  //  safe_free(e);
  bvconst_free(a, 4);
  bvconst_free(b, 4);
  bvconst_free(c, 4);
  bvconst_free(d, 4);
  bvconst_free(e, 4);
  cleanup_bvconstants();
}


// convert boolean to string
static char* b2str(bool x) {
  return x ? "true" : "false";
}


static void test_set_extend(uint32_t size1, uint32_t size2) {
  uint32_t *bv1, *bv2;
  uint32_t i, w1, w2;

  assert(size1 >= size2);

  w1 = (size1 + 31) >> 5;
  w2 = (size2 + 31) >> 5;

  bv1 = bvconst_alloc(w1);
  bv2 = bvconst_alloc(w2);

  printf("=== test_set_extend: size1 = %"PRIu32", size2 = %"PRIu32" ===\n", size1, size2);

  for (i=0; i<20; i++) {
    random_vector(vector, size2);
    bvconst_set_array(bv2, vector, size2);

    printf("%"PRIu32" to %"PRIu32" bits\n", size2, size1);
    printf("bv2            = ");
    bvconst_print(stdout, bv2, size2);
    printf("\n");
    bvconst_set_extend(bv1, size1, bv2, size2, 0);
    printf("ext(bv2, %"PRIu32", 0) = ", size1);
    bvconst_print(stdout, bv1, size1);
    printf("\n");
    bvconst_set_extend(bv1, size1, bv2, size2, 1);
    printf("ext(bv2, %"PRIu32", 1) = ", size1);
    bvconst_print(stdout, bv1, size1);
    printf("\n");
    bvconst_set_extend(bv1, size1, bv2, size2, -1);
    printf("sgnext(bv2, %"PRIu32", 0) = ", size1);
    bvconst_print(stdout, bv1, size1);
    printf("\n\n");
  }

  printf("===\n");
  bvconst_free(bv1, w1);
  bvconst_free(bv2, w2);
}


int main() {
  int32_t i, j, n;

  alloc_constants();

  printf("a = ");
  bvconst_print(stdout, a, 128);
  printf("\n");
  printf("iszero(a) = %d\n", bvconst_is_zero(a, 4));

  bvconst_add_one(a, 4);
  printf("a+1 = ");
  bvconst_print(stdout, a, 128);
  printf("\n");
  printf("iszero(a+1) = %d\n", bvconst_is_zero(a, 4));

  bvconst_sub_one(a, 4);
  printf("a+1-1 = ");
  bvconst_print(stdout, a, 128);
  printf("\n");
  printf("iszero(a+1-1) = %d\n", bvconst_is_zero(a, 4));

  bvconst_sub_one(a, 4);
  printf("a+1-2 = ");
  bvconst_print(stdout, a, 128);
  printf("\n");
  printf("iszero(a+1-2) = %d\n", bvconst_is_zero(a, 4));


  printf("b = ");
  bvconst_print(stdout, b, 128);
  printf("\n");
  printf("iszero(b) = %d\n", bvconst_is_zero(b, 4));

  bvconst_add_one(b, 4);
  printf("b+1 = ");
  bvconst_print(stdout, b, 128);
  printf("\n");
  printf("iszero(b+1) = %d\n", bvconst_is_zero(b, 4));

  bvconst_sub_one(b, 4);
  bvconst_sub_one(b, 4);
  printf("b-1 = ");
  bvconst_print(stdout, b, 128);
  printf("\n");
  printf("iszero(b-1) = %d\n", bvconst_is_zero(b, 4));


  printf("c = ");
  bvconst_print(stdout, c, 128);
  printf("\n");
  printf("iszero(c) = %d\n", bvconst_is_zero(c, 4));

  printf("d = ");
  bvconst_print(stdout, d, 128);
  printf("\n");
  printf("iszero(d) = %d\n", bvconst_is_zero(d, 4));

  printf("e = ");
  bvconst_print(stdout, e, 128);
  printf("\n");
  printf("iszero(e) = %d\n", bvconst_is_zero(e, 4));

  printf("e := a * b\n");
  bvconst_mul2(e, 4, a, b);
  printf("e = ");
  bvconst_print(stdout, e, 128);
  printf("\n\n");

  random_vector(vector, 32);
  bvconst_set_array(a, vector, 32);
  printf("a            = ");
  bvconst_print(stdout, a, 32);
  printf("\n");
  random_vector(vector, 73);
  bvconst_set_array(b, vector, 73);
  printf("b            = ");
  bvconst_print(stdout, b, 73);
  printf("\n");
  bvconst_concat(c, a, 32, b, 73);
  printf("conc(a, b)   = ");
  bvconst_print(stdout, c, 105);
  printf("\n");
  bvconst_concat(d, b, 73, a, 32);
  printf("conc(b, a)   = ");
  bvconst_print(stdout, d, 105);
  printf("\n\n");

  //  random_vector(vector, 63);
  bvconst_set_minus_one(a, 4);
  //  random_vector(vector, 63);
  bvconst_clear(b, 4);
  for (n=2; n<=128; n++) {
    for (i=1; i<n; i++) {
      printf("--- n = %"PRId32", i = %"PRId32" ---\n", n, i);
      printf("a          = ");
      bvconst_print(stdout, a, i);
      printf("\n");
      printf("b          = ");
      bvconst_print(stdout, b, n - i);
      printf("\n");
      bvconst_concat(c, a, i, b, n - i);
      bvconst_concat(d, b, n - i, a, i);
      printf("conc(a, b) = ");
      bvconst_print(stdout, c, n);
      printf("\n");
      printf("conc(b, a) = ");
      bvconst_print(stdout, d, n);
      printf("\n\n");
    }
  }


  //  exit(0);

  for (n=20; n>0; n--) {
    random_vector(vector, 20);
    bvconst_set_array(a, vector, 20);
    printf("a             = ");
    bvconst_print(stdout, a, 20);
    printf("\n");

    for (i=0; i<=20-n; i++) {
      bvconst_extract(b, a, i, i+n);
      printf("a[%2"PRId32", %2"PRId32")     = ", i, i+n);
      bvconst_print(stdout, b, n);
      printf("\n");
    }
    printf("\n");
  }


  for (n=50; n>20; n--) {
    random_vector(vector, 62);
    bvconst_set_array(a, vector, 62);
    printf("a             = ");
    bvconst_print(stdout, a, 62);
    printf("\n");

    for (i=0; i<=62-n; i++) {
      bvconst_extract(b, a, i, i+n);
      printf("a[%2"PRId32", %2"PRId32")     = ", i, i+n);
      bvconst_print(stdout, b, n);
      printf("\n");
    }
    printf("\n");
  }

  random_vector(vector, 20);
  bvconst_set_array(a, vector, 20);
  printf("a             = ");
  bvconst_print(stdout, a, 20);
  printf("\n");
  bvconst_set_extend(b, 31, a, 20, 0);
  printf("ext(a, 31, 0) = ");
  bvconst_print(stdout, b, 31);
  printf("\n");
  bvconst_set_extend(b, 31, a, 20, 1);
  printf("ext(a, 31, 1) = ");
  bvconst_print(stdout, b, 31);
  printf("\n");
  bvconst_set_extend(b, 31, a, 20, -1);
  printf("sgnext(a, 31) = ");
  bvconst_print(stdout, b, 31);
  printf("\n\n");


  random_vector(vector, 20);
  bvconst_set_array(a, vector, 20);
  printf("a             = ");
  bvconst_print(stdout, a, 20);
  printf("\n");
  bvconst_set_extend(b, 31, a, 20, 0);
  printf("ext(a, 31, 0) = ");
  bvconst_print(stdout, b, 31);
  printf("\n");
  bvconst_set_extend(b, 31, a, 20, 1);
  printf("ext(a, 31, 1) = ");
  bvconst_print(stdout, b, 31);
  printf("\n");
  bvconst_set_extend(b, 31, a, 20, -1);
  printf("sgnext(a, 31) = ");
  bvconst_print(stdout, b, 31);
  printf("\n\n");


  random_vector(vector, 20);
  bvconst_set_array(a, vector, 20);
  printf("a             = ");
  bvconst_print(stdout, a, 20);
  printf("\n");
  bvconst_set_extend(b, 31, a, 20, 0);
  printf("ext(a, 31, 0) = ");
  bvconst_print(stdout, b, 31);
  printf("\n");
  bvconst_set_extend(b, 31, a, 20, 1);
  printf("ext(a, 31, 1) = ");
  bvconst_print(stdout, b, 31);
  printf("\n");
  bvconst_set_extend(b, 31, a, 20, -1);
  printf("sgnext(a, 31) = ");
  bvconst_print(stdout, b, 31);
  printf("\n\n");


  random_vector(vector, 20);
  bvconst_set_array(a, vector, 20);
  printf("a             = ");
  bvconst_print(stdout, a, 20);
  printf("\n");
  bvconst_set_extend(b, 31, a, 20, 0);
  printf("ext(a, 31, 0) = ");
  bvconst_print(stdout, b, 31);
  printf("\n");
  bvconst_set_extend(b, 31, a, 20, 1);
  printf("ext(a, 31, 1) = ");
  bvconst_print(stdout, b, 31);
  printf("\n");
  bvconst_set_extend(b, 31, a, 20, -1);
  printf("sgnext(a, 31) = ");
  bvconst_print(stdout, b, 31);
  printf("\n\n");


  for (i=20; i<=99; i++) {
    random_vector(vector, 20);
    bvconst_set_array(a, vector, 20);
    printf("a             = ");
    bvconst_print(stdout, a, 20);
    printf("\n");
    bvconst_set_extend(b, i, a, 20, 0);
    printf("ext(a, %2"PRId32", 0) = ", i);
    bvconst_print(stdout, b, i);
    printf("\n");
    bvconst_set_extend(b, i, a, 20, 1);
    printf("ext(a, %2"PRId32", 1) = ", i);
    bvconst_print(stdout, b, i);
    printf("\n");
    bvconst_set_extend(b, i, a, 20, -1);
    printf("sgnext(a, %2"PRId32") = ", i);
    bvconst_print(stdout, b, i);
    printf("\n\n");
  }


  for (i=32; i<=99; i++) {
    random_vector(vector, 32);
    bvconst_set_array(a, vector, 32);
    printf("a             = ");
    bvconst_print(stdout, a, 32);
    printf("\n");
    bvconst_set_extend(b, i, a, 32, 0);
    printf("ext(a, %2"PRId32", 0) = ", i);
    bvconst_print(stdout, b, i);
    printf("\n");
    bvconst_set_extend(b, i, a, 32, 1);
    printf("ext(a, %2"PRId32", 1) = ", i);
    bvconst_print(stdout, b, i);
    printf("\n");
    bvconst_set_extend(b, i, a, 32, -1);
    printf("sgnext(a, %2"PRId32") = ", i);
    bvconst_print(stdout, b, i);
    printf("\n\n");
  }


  random_vector(vector, 120);
  bvconst_set_array(a, vector, 120);
  printf("a         = ");
  bvconst_print(stdout, a, 120);
  printf("\n");
  for (i=0; i<=120; i++) {
    printf("rshift %3"PRId32": ", i);
    bvconst_shift_right(a, 120, i, 0);
    bvconst_print(stdout, a, 120);
    printf("\n");
    bvconst_set_array(a, vector, 120);
  }
  printf("\n");

  random_vector(vector, 120);
  bvconst_set_array(a, vector, 120);
  printf("a         = ");
  bvconst_print(stdout, a, 120);
  printf("\n");
  for (i=0; i<=120; i++) {
    printf("rshift %3"PRId32": ", i);
    bvconst_shift_right(a, 120, i, 1);
    bvconst_print(stdout, a, 120);
    printf("\n");
    bvconst_set_array(a, vector, 120);
  }
  printf("\n");


  random_vector(vector, 120);
  bvconst_set_array(a, vector, 120);
  printf("a         = ");
  bvconst_print(stdout, a, 120);
  printf("\n");
  for (i=0; i<=120; i++) {
    printf("lshift %3"PRId32": ", i);
    bvconst_shift_left(a, 120, i, 0);
    bvconst_print(stdout, a, 120);
    printf("\n");
    bvconst_set_array(a, vector, 120);
  }
  printf("\n");

  random_vector(vector, 120);
  bvconst_set_array(a, vector, 120);
  printf("a         = ");
  bvconst_print(stdout, a, 120);
  printf("\n");
  for (i=0; i<=120; i++) {
    printf("lshift %3"PRId32": ", i);
    bvconst_shift_left(a, 120, i, 1);
    bvconst_print(stdout, a, 120);
    printf("\n");
    bvconst_set_array(a, vector, 120);
  }
  printf("\n");
  //  exit(0);


  printf("c = ");
  bvconst_print(stdout, c, 128);
  printf("\n");
  printf("d = ");
  bvconst_print(stdout, d, 128);
  printf("\n");
  printf("e := c * d\n");
  bvconst_mul2(e, 4, c, d);
  printf("e = ");
  bvconst_print(stdout, e, 128);
  printf("\n");
  printf("e := d * c\n");
  bvconst_mul2(e, 4, d, c);
  printf("e = ");
  bvconst_print(stdout, e, 128);
  printf("\n\n");

  printf("b = ");
  bvconst_print(stdout, b, 128);
  printf("\n");
  printf("d = ");
  bvconst_print(stdout, d, 128);
  printf("\n");
  printf("e := b * d\n");
  bvconst_mul2(e, 4, b, d);
  printf("e = ");
  bvconst_print(stdout, e, 128);
  printf("\n\n");



  bvconst_set64(a, 4, 1372919719782793ULL);
  bvconst_set32(b, 4, 12670371);
  printf("a = ");
  bvconst_print(stdout, a, 128);
  printf("\n");
  printf("b = ");
  bvconst_print(stdout, b, 128);
  printf("\n");
  printf("e := a * b\n");
  bvconst_set(c, 4, a);
  printf("c = ");
  bvconst_print(stdout, c, 128);
  printf("\n");
  bvconst_mul(c, 4, b);
  printf("c = ");
  bvconst_print(stdout, c, 128);
  printf("\n");
  bvconst_mul2(e, 4, a, b);
  printf("e = ");
  bvconst_print(stdout, e, 128);
  printf("\n\n");

  mpz_init(z0);
  mpz_init(z1);
  mpz_init(z2);

  bvconst_get_mpz(a, 4, z0);
  printf("--> conversion a to mpz: ");
  mpz_out_str(stdout, 10, z0);
  printf("\n");
  bvconst_get_mpz(b, 4, z0);
  printf("--> conversion b to mpz: ");
  mpz_out_str(stdout, 10, z0);
  printf("\n");
  bvconst_get_mpz(e, 4, z0);
  printf("--> conversion e to mpz: ");
  mpz_out_str(stdout, 10, z0);
  printf("\n\n");

  printf("e -= a * b\n");
  bvconst_submul(e, 4, a, b);
  printf("e = ");
  bvconst_print(stdout, e, 128);
  printf("\n");
  bvconst_get_mpz(e, 4, z0);
  printf("--> conversion e to mpz: ");
  mpz_out_str(stdout, 10, z0);
  printf("\n\n");

  for (i=0; i<10; i++) {
    printf("test %"PRId32": e *= a\n", i);
    random_vector(vector, 128);
    bvconst_set_array(a, vector, 128);
    random_vector(vector, 128);
    bvconst_set_array(e, vector, 128);
    bvconst_get_mpz(e, 4, z1);

    printf("a  = ");
    bvconst_print(stdout, a, 128);
    printf("\n");
    printf("e  = ");
    bvconst_print(stdout, e, 128);
    printf("\n");
    bvconst_mul(e, 4, a);
    printf("e' = ");
    bvconst_print(stdout, e, 128);
    printf("\n");

    bvconst_get_mpz(a, 4, z0);
    printf("--> conversion a  to mpz: ");
    mpz_out_str(stdout, 10, z0);
    printf("\n");
    printf("--> conversion e  to mpz: ");
    mpz_out_str(stdout, 10, z1);
    printf("\n");
    bvconst_get_mpz(e, 4, z2);
    printf("--> conversion e' to mpz: ");
    mpz_out_str(stdout, 10, z2);
    printf("\n");

    mpz_mul(z0, z0, z1);
    mpz_fdiv_r_2exp(z0, z0, 128);
    printf("--> check:                ");
    mpz_out_str(stdout, 10, z0);
    printf("\n\n");
    assert(mpz_cmp(z0, z2) == 0);
  }

  for (i=0; i<10; i++) {
    printf("test %"PRId32", a := - a\n", i);
    random_vector(vector, 128);
    bvconst_set_array(a, vector, 128);
    bvconst_get_mpz(a, 4, z0);

    printf("a = ");
    bvconst_print(stdout, a, 128);
    printf("\n");
    bvconst_negate(a, 4);
    printf("a = ");
    bvconst_print(stdout, a, 128);
    printf("\n");

    printf("--> conversion  a to mpz: ");
    mpz_out_str(stdout, 10, z0);
    printf("\n");
    bvconst_get_mpz(a, 4, z1);
    printf("--> conversion -a to mpz: ");
    mpz_out_str(stdout, 10, z1);
    printf("\n");

    mpz_neg(z0, z0);
    mpz_fdiv_r_2exp(z0, z0, 128);
    printf("--> check:                ");
    mpz_out_str(stdout, 10, z0);
    printf("\n\n");
    assert(mpz_cmp(z0, z1) == 0);
  }

  for (i=0; i<10; i++) {
    printf("test %"PRId32": e := - a\n", i);
    random_vector(vector, 128);
    bvconst_set_array(a, vector, 128);
    printf("a = ");
    bvconst_print(stdout, a, 128);
    printf("\n");
    bvconst_negate2(e, 4, a);
    printf("e = ");
    bvconst_print(stdout, e, 128);
    printf("\n");

    printf("--> conversion a to mpz: ");
    bvconst_get_mpz(a, 4, z0);
    mpz_out_str(stdout, 10, z0);
    printf("\n");
    bvconst_get_mpz(e, 4, z1);
    printf("--> conversion e to mpz: ");
    mpz_out_str(stdout, 10, z1);
    printf("\n");

    mpz_neg(z0, z0);
    mpz_fdiv_r_2exp(z0, z0, 128);
    printf("--> check:               ");
    mpz_out_str(stdout, 10, z0);
    printf("\n\n");
    assert(mpz_cmp(z0, z1) == 0);
  }

  for (i=0; i<10; i++) {
    printf("test %"PRId32", e = a * b\n", i);
    random_vector(vector, 128);
    bvconst_set_array(a, vector, 128);
    random_vector(vector, 128);
    bvconst_set_array(b, vector, 128);

    printf("a = ");
    bvconst_print(stdout, a, 128);
    printf("\n");
    printf("b = ");
    bvconst_print(stdout, b, 128);
    printf("\n");
    bvconst_mul2(e, 4, a, b);
    printf("e = ");
    bvconst_print(stdout, e, 128);
    printf("\n");

    bvconst_get_mpz(a, 4, z0);
    printf("--> conversion a to mpz: ");
    mpz_out_str(stdout, 10, z0);
    printf("\n");
    bvconst_get_mpz(b, 4, z1);
    printf("--> conversion b to mpz: ");
    mpz_out_str(stdout, 10, z1);
    printf("\n");
    bvconst_get_mpz(e, 4, z2);
    printf("--> conversion e to mpz: ");
    mpz_out_str(stdout, 10, z2);
    printf("\n");

    mpz_mul(z0, z0, z1);
    mpz_fdiv_r_2exp(z0, z0, 128);
    printf("--> check:               ");
    mpz_out_str(stdout, 10, z0);
    printf("\n\n");
    assert(mpz_cmp(z0, z2) == 0);
  }

  for (i=0; i<10; i++) {
    printf("test %"PRId32": e = - (a * b)\n", i);
    random_vector(vector, 128);
    bvconst_set_array(a, vector, 128);
    random_vector(vector, 128);
    bvconst_set_array(b, vector, 128);

    printf("a = ");
    bvconst_print(stdout, a, 128);
    printf("\n");
    printf("b = ");
    bvconst_print(stdout, b, 128);
    printf("\n");
    bvconst_clear(e, 4);
    bvconst_submul(e, 4, a, b);
    printf("e = ");
    bvconst_print(stdout, e, 128);
    printf("\n");

    bvconst_get_mpz(a, 4, z0);
    printf("--> conversion a to mpz: ");
    mpz_out_str(stdout, 10, z0);
    printf("\n");
    bvconst_get_mpz(b, 4, z1);
    printf("--> conversion b to mpz: ");
    mpz_out_str(stdout, 10, z1);
    printf("\n");
    bvconst_get_mpz(d, 4, z2);
    printf("--> conversion d to mpz: ");
    mpz_out_str(stdout, 10, z2);
    printf("\n");
    bvconst_get_mpz(e, 4, z2);
    printf("--> conversion e to mpz: ");
    mpz_out_str(stdout, 10, z2);
    printf("\n");

    mpz_mul(z0, z0, z1);
    mpz_neg(z0, z0);
    mpz_fdiv_r_2exp(z0, z0, 128);
    printf("--> check:               ");
    mpz_out_str(stdout, 10, z0);
    printf("\n\n");
    assert(mpz_cmp(z0, z2) == 0);
  }

  for (i=0; i<10; i++) {
    printf("test %"PRId32": e = a + b\n", i);
    random_vector(vector, 128);
    bvconst_set_array(a, vector, 128);
    random_vector(vector, 128);
    bvconst_set_array(b, vector, 128);

    printf("a = ");
    bvconst_print(stdout, a, 128);
    printf("\n");
    printf("b = ");
    bvconst_print(stdout, b, 128);
    printf("\n");
    bvconst_add2(e, 4, a, b);
    printf("e = ");
    bvconst_print(stdout, e, 128);
    printf("\n");

    bvconst_get_mpz(a, 4, z0);
    printf("--> conversion a to mpz: ");
    mpz_out_str(stdout, 10, z0);
    printf("\n");
    bvconst_get_mpz(b, 4, z1);
    printf("--> conversion b to mpz: ");
    mpz_out_str(stdout, 10, z1);
    printf("\n");
    bvconst_get_mpz(e, 4, z2);
    printf("--> conversion e to mpz: ");
    mpz_out_str(stdout, 10, z2);
    printf("\n");

    mpz_add(z0, z0, z1);
    mpz_fdiv_r_2exp(z0, z0, 128);
    printf("--> check:               ");
    mpz_out_str(stdout, 10, z0);
    printf("\n\n");
    assert(mpz_cmp(z0, z2) == 0);
  }

  for (i=0; i<10; i++) {
    printf("test %"PRId32": e = a - b\n", i);
    random_vector(vector, 128);
    bvconst_set_array(a, vector, 128);
    random_vector(vector, 128);
    bvconst_set_array(b, vector, 128);

    printf("a = ");
    bvconst_print(stdout, a, 128);
    printf("\n");
    printf("b = ");
    bvconst_print(stdout, b, 128);
    printf("\n");
    bvconst_sub2(e, 4, a, b);
    printf("e = ");
    bvconst_print(stdout, e, 128);
    printf("\n");

    bvconst_get_mpz(a, 4, z0);
    printf("--> conversion a to mpz: ");
    mpz_out_str(stdout, 10, z0);
    printf("\n");
    bvconst_get_mpz(b, 4, z1);
    printf("--> conversion b to mpz: ");
    mpz_out_str(stdout, 10, z1);
    printf("\n");
    bvconst_get_mpz(e, 4, z2);
    printf("--> conversion e to mpz: ");
    mpz_out_str(stdout, 10, z2);
    printf("\n");

    mpz_sub(z0, z0, z1);
    mpz_fdiv_r_2exp(z0, z0, 128);
    printf("--> check:               ");
    mpz_out_str(stdout, 10, z0);
    printf("\n\n");
    assert(mpz_cmp(z0, z2) == 0);
  }

  for (i=0; i<10; i++) {
    printf("\ntest %"PRId32": comparisons\n", i);
    random_vector(vector, 25);
    bvconst_set_array(a, vector, 25);
    random_vector(vector, 25);
    bvconst_set_array(b, vector, 25);

    printf("a = ");
    bvconst_print(stdout, a, 25);
    printf("\n");
    printf("b = ");
    bvconst_print(stdout, b, 25);
    printf("\n");

    bvconst_normalize(a, 25);
    bvconst_normalize(b, 25);
    printf("Unsigned tests\n");
    printf(" a le b: %d\n", bvconst_le(a, b, 25));
    printf(" a ge b: %d\n", bvconst_ge(a, b, 25));
    printf(" a lt b: %d\n", bvconst_lt(a, b, 25));
    printf(" a gt b: %d\n", bvconst_gt(a, b, 25));

    printf("Signed tests\n");
    printf(" a sle b: %d\n", bvconst_sle(a, b, 25));
    printf(" a sge b: %d\n", bvconst_sge(a, b, 25));
    printf(" a slt b: %d\n", bvconst_slt(a, b, 25));
    printf(" a sgt b: %d\n", bvconst_sgt(a, b, 25));
  }


  for (i=0; i<10; i++) {
    printf("\ntest %"PRId32": comparisons\n", i);
    random_vector(vector, 32);
    bvconst_set_array(a, vector, 32);
    random_vector(vector, 32);
    bvconst_set_array(b, vector, 32);

    printf("a = ");
    bvconst_print(stdout, a, 32);
    printf("\n");
    printf("b = ");
    bvconst_print(stdout, b, 32);
    printf("\n");

    bvconst_normalize(a, 32);
    bvconst_normalize(b, 32);
    printf("Unsigned tests\n");
    printf(" a le b: %d\n", bvconst_le(a, b, 32));
    printf(" a ge b: %d\n", bvconst_ge(a, b, 32));
    printf(" a lt b: %d\n", bvconst_lt(a, b, 32));
    printf(" a gt b: %d\n", bvconst_gt(a, b, 32));

    printf("Signed tests\n");
    printf(" a sle b: %d\n", bvconst_sle(a, b, 32));
    printf(" a sge b: %d\n", bvconst_sge(a, b, 32));
    printf(" a slt b: %d\n", bvconst_slt(a, b, 32));
    printf(" a sgt b: %d\n", bvconst_sgt(a, b, 32));
  }

  for (i=0; i<10; i++) {
    printf("\ntest %"PRId32": comparisons\n", i);
    random_vector(vector, 33);
    bvconst_set_array(a, vector, 33);
    random_vector(vector, 33);
    bvconst_set_array(b, vector, 33);

    printf("a = ");
    bvconst_print(stdout, a, 33);
    printf("\n");
    printf("b = ");
    bvconst_print(stdout, b, 33);
    printf("\n");

    bvconst_normalize(a, 33);
    bvconst_normalize(b, 33);
    printf("Unsigned tests\n");
    printf(" a le b: %d\n", bvconst_le(a, b, 33));
    printf(" a ge b: %d\n", bvconst_ge(a, b, 33));
    printf(" a lt b: %d\n", bvconst_lt(a, b, 33));
    printf(" a gt b: %d\n", bvconst_gt(a, b, 33));

    printf("Signed tests\n");
    printf(" a sle b: %d\n", bvconst_sle(a, b, 33));
    printf(" a sge b: %d\n", bvconst_sge(a, b, 33));
    printf(" a slt b: %d\n", bvconst_slt(a, b, 33));
    printf(" a sgt b: %d\n", bvconst_sgt(a, b, 33));
  }

  for (i=0; i<10; i++) {
    printf("\ntest %"PRId32": comparisons\n", i);
    random_vector(vector, 63);
    bvconst_set_array(a, vector, 63);
    random_vector(vector, 63);
    bvconst_set_array(b, vector, 63);

    printf("a = ");
    bvconst_print(stdout, a, 63);
    printf("\n");
    printf("b = ");
    bvconst_print(stdout, b, 63);
    printf("\n");

    bvconst_normalize(a, 63);
    bvconst_normalize(b, 63);
    printf("Unsigned tests\n");
    printf(" a le b: %d\n", bvconst_le(a, b, 63));
    printf(" a ge b: %d\n", bvconst_ge(a, b, 63));
    printf(" a lt b: %d\n", bvconst_lt(a, b, 63));
    printf(" a gt b: %d\n", bvconst_gt(a, b, 63));

    printf("Signed tests\n");
    printf(" a sle b: %d\n", bvconst_sle(a, b, 63));
    printf(" a sge b: %d\n", bvconst_sge(a, b, 63));
    printf(" a slt b: %d\n", bvconst_slt(a, b, 63));
    printf(" a sgt b: %d\n", bvconst_sgt(a, b, 63));
  }

  for (i=0; i<10; i++) {
    printf("\ntest %"PRId32": comparisons\n", i);
    random_vector(vector, 64);
    bvconst_set_array(a, vector, 64);
    random_vector(vector, 64);
    bvconst_set_array(b, vector, 64);

    printf("a = ");
    bvconst_print(stdout, a, 64);
    printf("\n");
    printf("b = ");
    bvconst_print(stdout, b, 64);
    printf("\n");

    bvconst_normalize(a, 64);
    bvconst_normalize(b, 64);
    printf("Unsigned tests\n");
    printf(" a le b: %d\n", bvconst_le(a, b, 64));
    printf(" a ge b: %d\n", bvconst_ge(a, b, 64));
    printf(" a lt b: %d\n", bvconst_lt(a, b, 64));
    printf(" a gt b: %d\n", bvconst_gt(a, b, 64));

    printf("Signed tests\n");
    printf(" a sle b: %d\n", bvconst_sle(a, b, 64));
    printf(" a sge b: %d\n", bvconst_sge(a, b, 64));
    printf(" a slt b: %d\n", bvconst_slt(a, b, 64));
    printf(" a sgt b: %d\n", bvconst_sgt(a, b, 64));
  }

  printf("\nMore comparisons\n");
  random_vector(vector, 64);
  bvconst_set_array(a, vector, 64);
  bvconst_set_array(b, vector, 64);
  printf("a = ");
  bvconst_print(stdout, a, 64);
  printf("\n");
  printf("b = ");
  bvconst_print(stdout, b, 64);
  printf("\n");

  bvconst_normalize(a, 64);
  bvconst_normalize(b, 64);
  printf("Unsigned tests\n");
  printf(" a le b: %d\n", bvconst_le(a, b, 64));
  printf(" a ge b: %d\n", bvconst_ge(a, b, 64));
  printf(" a lt b: %d\n", bvconst_lt(a, b, 64));
  printf(" a gt b: %d\n", bvconst_gt(a, b, 64));

  printf("Signed tests\n");
  printf(" a sle b: %d\n", bvconst_sle(a, b, 64));
  printf(" a sge b: %d\n", bvconst_sge(a, b, 64));
  printf(" a slt b: %d\n", bvconst_slt(a, b, 64));
  printf(" a sgt b: %d\n", bvconst_sgt(a, b, 64));


  random_vector(vector, 65);
  bvconst_set_array(a, vector, 65);
  bvconst_set_array(b, vector, 65);
  printf("a = ");
  bvconst_print(stdout, a, 65);
  printf("\n");
  printf("b = ");
  bvconst_print(stdout, b, 65);
  printf("\n");

  bvconst_normalize(a, 65);
  bvconst_normalize(b, 65);
  printf("Unsigned tests\n");
  printf(" a le b: %d\n", bvconst_le(a, b, 65));
  printf(" a ge b: %d\n", bvconst_ge(a, b, 65));
  printf(" a lt b: %d\n", bvconst_lt(a, b, 65));
  printf(" a gt b: %d\n", bvconst_gt(a, b, 65));

  printf("Signed tests\n");
  printf(" a sle b: %d\n", bvconst_sle(a, b, 65));
  printf(" a sge b: %d\n", bvconst_sge(a, b, 65));
  printf(" a slt b: %d\n", bvconst_slt(a, b, 65));
  printf(" a sgt b: %d\n", bvconst_sgt(a, b, 65));

  random_vector(vector, 63);
  bvconst_set_array(a, vector, 63);
  bvconst_set_array(b, vector, 63);
  printf("a = ");
  bvconst_print(stdout, a, 63);
  printf("\n");
  printf("b = ");
  bvconst_print(stdout, b, 63);
  printf("\n");

  bvconst_normalize(a, 63);
  bvconst_normalize(b, 63);
  printf("Unsigned tests\n");
  printf(" a le b: %d\n", bvconst_le(a, b, 63));
  printf(" a ge b: %d\n", bvconst_ge(a, b, 63));
  printf(" a lt b: %d\n", bvconst_lt(a, b, 63));
  printf(" a gt b: %d\n", bvconst_gt(a, b, 63));

  printf("Signed tests\n");
  printf(" a sle b: %d\n", bvconst_sle(a, b, 63));
  printf(" a sge b: %d\n", bvconst_sge(a, b, 63));
  printf(" a slt b: %d\n", bvconst_slt(a, b, 63));
  printf(" a sgt b: %d\n", bvconst_sgt(a, b, 63));

  printf("\nTest powers of two\n");
  mpz_set_ui(z0, 1);
  for (i=0; i<128; i++) {
    printf("z0 = ");
    mpz_out_str(stdout, 10, z0);
    printf("\n");
    bvconst_set_mpz(a, 4, z0);
    printf("a = ");
    bvconst_print(stdout, a, 128);
    printf("\n");

    n = bvconst_is_power_of_two(a, 4);
    if (n < 0) {
      printf("--> not a power of 2\n\n");
    } else {
      printf("--> a = 2^%"PRId32"\n\n", n);
    }
    mpz_add(z0, z0, z0);
  }


  a[0] = 0;
  a[1] = 1024;
  a[2] = 0;
  a[3] = 36136287;
  printf("a = ");
  bvconst_print(stdout, a, 128);
  printf("\n");
  n = bvconst_is_power_of_two(a, 4);
  if (n < 0) {
    printf("--> not a power of 2\n\n");
  } else {
    printf("--> a = 2^%"PRId32"\n\n", n);
  }

  a[0] = 0;
  a[1] = 1024;
  a[2] = 31209;
  a[3] = 0;
  printf("a = ");
  bvconst_print(stdout, a, 128);
  printf("\n");
  n = bvconst_is_power_of_two(a, 4);
  if (n < 0) {
    printf("--> not a power of 2\n\n");
  } else {
    printf("--> a = 2^%"PRId32"\n\n", n);
  }


  a[0] = 0;
  a[1] = 1024;
  a[2] = 0;
  a[3] = 0;
  printf("a = ");
  bvconst_print(stdout, a, 128);
  printf("\n");
  n = bvconst_is_power_of_two(a, 4);
  if (n < 0) {
    printf("--> not a power of 2\n\n");
  } else {
    printf("--> a = 2^%"PRId32"\n\n", n);
  }


  a[0] = 128;
  a[1] = 1024;
  a[2] = 0;
  a[3] = 0;
  printf("a = ");
  bvconst_print(stdout, a, 128);
  printf("\n");
  n = bvconst_is_power_of_two(a, 4);
  if (n < 0) {
    printf("--> not a power of 2\n\n");
  } else {
    printf("--> a = 2^%"PRId32"\n\n", n);
  }




  bvconst_clear(a, 4);
  for (i=0; i<256; i++) {
    printf("a = ");
    bvconst_print(stdout, a, 128);
    printf("\n");

    n = bvconst_is_power_of_two(a, 4);
    if (n < 0) {
      printf("--> not a power of 2\n\n");
    } else {
      printf("--> a = 2^%"PRId32"\n\n", n);
    }
    bvconst_add_one(a, 4);
  }

  for (i=0; i<10; i++) {
    printf("test %"PRId32": power of two\n", i);
    random_vector(vector, 128);
    bvconst_set_array(a, vector, 128);

    for (j=0; j<64; j++) {
      printf("a = ");
      bvconst_print(stdout, a, 128);
      printf("\n");
      n = bvconst_is_power_of_two(a, 4);
      if (n < 0) {
	printf("--> not a power of 2\n\n");
      } else {
	printf("--> a = 2^%"PRId32"\n\n", n);
      }
      bvconst_clr_bit(a, j);
      bvconst_clr_bit(a, 127 - j);
    }
  }


  // test mulpower
  for (i=0; i<130; i++) {
    bvconst_set_one(a, 4);    // a = 1
    bvconst_set32(b, 4, 2);   // b = 2
    // compute a * b^i = 2^i
    bvconst_mulpower(a, 4, b, i);
    printf("---> mulpower: a = b^%"PRIu32" = 2^%"PRIu32"\n", i, i);
    printf("     b = ");
    bvconst_print(stdout, b, 128);
    printf("\n");
    printf("     a = ");
    bvconst_print(stdout, a, 128);
    printf("\n");
  }

  // test mulpower
  for (i=0; i<40; i++) {
    bvconst_set32(a, 4, 4);       // a = 0b0..00100
    bvconst_set_minus_one(b, 4);  // b = 0b11..1111
    // compute a * b^i = -4 or +4
    bvconst_mulpower(a, 4, b, i);
    printf("---> mulpower: a = 4 * b^%"PRIu32" = 4 * (-1)^%"PRIu32"\n", i, i);
    printf("     b = ");
    bvconst_print(stdout, b, 128);
    printf("\n");
    printf("     a = ");
    bvconst_print(stdout, a, 128);
    printf("\n");
  }

  // test mulpower
  for (i=0; i<40; i++) {
    bvconst_set32(a, 4, 4);     // a = 0b0..00100
    bvconst_clear(b, 4);        // b = 0
    // compute a * b^i = 0
    bvconst_mulpower(a, 4, b, i);
    printf("---> mulpower: a = 4 * b^%"PRIu32"\n", i);
    printf("     b = ");
    bvconst_print(stdout, b, 128);
    printf("\n");
    printf("     a = ");
    bvconst_print(stdout, a, 128);
    printf("\n");
  }


  // test is_one and is_minus_one
  printf("\n\n");
  for (i=1; i<=128; i++) {
    bvconst_set_one(a, 4);         // a = 1
    bvconst_set_minus_one(b, 4);   // b = -1
    bvconst_clear(c, 4);           // c = 0
    random_vector(vector, i);
    bvconst_set_array(d, vector, i); // d = random

    // make all i-bit length constant
    bvconst_normalize(a, i);
    bvconst_normalize(b, i);
    bvconst_normalize(c, i);
    bvconst_normalize(d, i);

    n = (i+31) >> 5;  // number of words
    printf("---> %"PRIu32" bits\n", i);
    printf("a = ");
    bvconst_print(stdout, a, i);
    printf(": is_one = %s, is_minus_one = %s\n", b2str(bvconst_is_one(a, n)), b2str(bvconst_is_minus_one(a, i)));

    printf("b = ");
    bvconst_print(stdout, b, i);
    printf(": is_one = %s, is_minus_one = %s\n", b2str(bvconst_is_one(b, n)), b2str(bvconst_is_minus_one(b, i)));

    printf("c = ");
    bvconst_print(stdout, c, i);
    printf(": is_one = %s, is_minus_one = %s\n", b2str(bvconst_is_one(c, n)), b2str(bvconst_is_minus_one(c, i)));

    printf("d = ");
    bvconst_print(stdout, d, i);
    printf(": is_one = %s, is_minus_one = %s\n", b2str(bvconst_is_one(d, n)), b2str(bvconst_is_minus_one(d, i)));

    printf("\n");
    fflush(stdout);
  }

  // test is_min_signed and is_max_signed
  printf("\n\n");
  for (i=1; i<=128; i++) {
    bvconst_clear(a, 4);           // a = 0
    bvconst_set_minus_one(b, 4);   // b = -1
    bvconst_clear(c, 4);
    bvconst_set_bit(c, i-1);       // c = 0b10000000 (smallest negative integer)
    bvconst_set_minus_one(d, 4);
    bvconst_clr_bit(d, i-1);       // d = 0b01111111 (largest positive integer)
    random_vector(vector, i);
    bvconst_set_array(e, vector, i); // e = random

    // make all i-bit length constant
    bvconst_normalize(a, i);
    bvconst_normalize(b, i);
    bvconst_normalize(c, i);
    bvconst_normalize(d, i);
    bvconst_normalize(e, i);

    printf("---> %"PRIu32" bits\n", i);
    printf("a = ");
    bvconst_print(stdout, a, i);
    printf(": is_min_signed = %s, is_max_signed = %s\n", b2str(bvconst_is_min_signed(a, i)), b2str(bvconst_is_max_signed(a, i)));

    printf("b = ");
    bvconst_print(stdout, b, i);
    printf(": is_min_signed = %s, is_max_signed = %s\n", b2str(bvconst_is_min_signed(b, i)), b2str(bvconst_is_max_signed(b, i)));

    printf("c = ");
    bvconst_print(stdout, c, i);
    printf(": is_min_signed = %s, is_max_signed = %s\n", b2str(bvconst_is_min_signed(c, i)), b2str(bvconst_is_max_signed(c, i)));

    printf("d = ");
    bvconst_print(stdout, d, i);
    printf(": is_min_signed = %s, is_max_signed = %s\n", b2str(bvconst_is_min_signed(d, i)), b2str(bvconst_is_max_signed(d, i)));

    printf("e = ");
    bvconst_print(stdout, e, i);
    printf(": is_min_signed = %s, is_max_signed = %s\n", b2str(bvconst_is_min_signed(e, i)), b2str(bvconst_is_max_signed(e, i)));

    printf("\n");
    fflush(stdout);
  }

  for (i=100; i<256; i += 10) {
    for (j=1; j<=i; j += 9) {
      test_set_extend(i, j);
    }
  }

  mpz_clear(z0);
  mpz_clear(z1);
  mpz_clear(z2);


  free_constants();

  return 0;
}
