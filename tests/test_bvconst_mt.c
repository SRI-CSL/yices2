/*
 * Test arithmetic on bit-vector constants
 */

#include <stdlib.h>
#include <stdio.h>
#include <gmp.h>
#include <assert.h>
#include <inttypes.h>

#include "bv_constants.h"
#include "memalloc.h"
#include "threads.h"

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

/*
static uint32_t *a, *b, *c, *d, *e;

static mpz_t z0, z1, z2;
static int32_t vector[128];
*/

static void random_vector(int32_t *v, int32_t n) {
  int32_t i;

  for (i=0; i<n; i++) {
    v[i] = random() & 0x1;
  }
}

static void alloc_constants(uint32_t **ap, uint32_t **bp, uint32_t **cp, uint32_t **dp, uint32_t **ep) {
  uint32_t i;
  uint32_t *a, *b, *c, *d, *e;
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


  *ap = a;
  *bp = b;
  *cp = c;
  *dp = d;
  *ep = e;


}

static void free_constants(uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d, uint32_t *e) {
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
}


// convert boolean to string
static char* b2str(bool x) {
  return x ? "true" : "false";
}





yices_thread_result_t YICES_THREAD_ATTR test_thread(void* arg){
  thread_data_t* tdata = (thread_data_t *)arg;
  FILE* output = tdata->output;

  int32_t i, j, n;

  uint32_t *a, *b, *c, *d, *e;

  int32_t vector[128];

  mpz_t z0, z1, z2;

  alloc_constants(&a, &b, &c, &d, &e);

  fprintf(output, "a = ");
  bvconst_print(output, a, 128);
  fprintf(output, "\n");
  fprintf(output, "iszero(a) = %d\n", bvconst_is_zero(a, 4));

  bvconst_add_one(a, 4);
  fprintf(output, "a+1 = ");
  bvconst_print(output, a, 128);
  fprintf(output, "\n");
  fprintf(output, "iszero(a+1) = %d\n", bvconst_is_zero(a, 4));

  bvconst_sub_one(a, 4);
  fprintf(output, "a+1-1 = ");
  bvconst_print(output, a, 128);
  fprintf(output, "\n");
  fprintf(output, "iszero(a+1-1) = %d\n", bvconst_is_zero(a, 4));

  bvconst_sub_one(a, 4);
  fprintf(output, "a+1-2 = ");
  bvconst_print(output, a, 128);
  fprintf(output, "\n");
  fprintf(output, "iszero(a+1-2) = %d\n", bvconst_is_zero(a, 4));


  fprintf(output, "b = ");
  bvconst_print(output, b, 128);
  fprintf(output, "\n");
  fprintf(output, "iszero(b) = %d\n", bvconst_is_zero(b, 4));

  bvconst_add_one(b, 4);
  fprintf(output, "b+1 = ");
  bvconst_print(output, b, 128);
  fprintf(output, "\n");
  fprintf(output, "iszero(b+1) = %d\n", bvconst_is_zero(b, 4));

  bvconst_sub_one(b, 4);
  bvconst_sub_one(b, 4);
  fprintf(output, "b-1 = ");
  bvconst_print(output, b, 128);
  fprintf(output, "\n");
  fprintf(output, "iszero(b-1) = %d\n", bvconst_is_zero(b, 4));


  fprintf(output, "c = ");
  bvconst_print(output, c, 128);
  fprintf(output, "\n");
  fprintf(output, "iszero(c) = %d\n", bvconst_is_zero(c, 4));

  fprintf(output, "d = ");
  bvconst_print(output, d, 128);
  fprintf(output, "\n");
  fprintf(output, "iszero(d) = %d\n", bvconst_is_zero(d, 4));

  fprintf(output, "e = ");
  bvconst_print(output, e, 128);
  fprintf(output, "\n");
  fprintf(output, "iszero(e) = %d\n", bvconst_is_zero(e, 4));

  fprintf(output, "e := a * b\n");
  bvconst_mul2(e, 4, a, b);
  fprintf(output, "e = ");
  bvconst_print(output, e, 128);

  fprintf(output, "\n\nRANDOMIZED\n\n");

  random_vector(vector, 32);

  bvconst_set_array(a, vector, 32);
  fprintf(output, "a            = ");
  bvconst_print(output, a, 32);
  fprintf(output, "\n");
  random_vector(vector, 73);
  bvconst_set_array(b, vector, 73);
  fprintf(output, "b            = ");
  bvconst_print(output, b, 73);
  fprintf(output, "\n");
  bvconst_concat(c, a, 32, b, 73);
  fprintf(output, "conc(a, b)   = ");
  bvconst_print(output, c, 105);
  fprintf(output, "\n");
  bvconst_concat(d, b, 73, a, 32);
  fprintf(output, "conc(b, a)   = ");
  bvconst_print(output, d, 105);
  fprintf(output, "\n\n");

  //  random_vector(vector, 63);
  bvconst_set_minus_one(a, 4);
  //  random_vector(vector, 63);
  bvconst_clear(b, 4);
  for (n=2; n<=128; n++) {
    for (i=1; i<n; i++) {
      fprintf(output, "--- n = %"PRId32", i = %"PRId32" ---\n", n, i);
      fprintf(output, "a          = ");
      bvconst_print(output, a, i);
      fprintf(output, "\n");
      fprintf(output, "b          = ");
      bvconst_print(output, b, n - i);
      fprintf(output, "\n");
      bvconst_concat(c, a, i, b, n - i);
      bvconst_concat(d, b, n - i, a, i);
      fprintf(output, "conc(a, b) = ");
      bvconst_print(output, c, n);
      fprintf(output, "\n");
      fprintf(output, "conc(b, a) = ");
      bvconst_print(output, d, n);
      fprintf(output, "\n\n");
    }
  }


  //  exit(0);

  fprintf(output, "\n\nRANDOMIZED\n\n");

  for (n=20; n>0; n--) {
    random_vector(vector, 20);
    bvconst_set_array(a, vector, 20);
    fprintf(output, "a             = ");
    bvconst_print(output, a, 20);
    fprintf(output, "\n");

    for (i=0; i<=20-n; i++) {
      bvconst_extract(b, a, i, i+n);
      fprintf(output, "a[%2"PRId32", %2"PRId32")     = ", i, i+n);
      bvconst_print(output, b, n);
      fprintf(output, "\n");
    }
    fprintf(output, "\n");
  }


  for (n=50; n>20; n--) {
    random_vector(vector, 62);
    bvconst_set_array(a, vector, 62);
    fprintf(output, "a             = ");
    bvconst_print(output, a, 62);
    fprintf(output, "\n");

    for (i=0; i<=62-n; i++) {
      bvconst_extract(b, a, i, i+n);
      fprintf(output, "a[%2"PRId32", %2"PRId32")     = ", i, i+n);
      bvconst_print(output, b, n);
      fprintf(output, "\n");
    }
    fprintf(output, "\n");
  }

  random_vector(vector, 20);
  bvconst_set_array(a, vector, 20);
  fprintf(output, "a             = ");
  bvconst_print(output, a, 20);
  fprintf(output, "\n");
  bvconst_set_extend(b, 31, a, 20, 0);
  fprintf(output, "ext(a, 31, 0) = ");
  bvconst_print(output, b, 31);
  fprintf(output, "\n");
  bvconst_set_extend(b, 31, a, 20, 1);
  fprintf(output, "ext(a, 31, 1) = ");
  bvconst_print(output, b, 31);
  fprintf(output, "\n");
  bvconst_set_extend(b, 31, a, 20, -1);
  fprintf(output, "sgnext(a, 31) = ");
  bvconst_print(output, b, 31);
  fprintf(output, "\n\n");


  random_vector(vector, 20);
  bvconst_set_array(a, vector, 20);
  fprintf(output, "a             = ");
  bvconst_print(output, a, 20);
  fprintf(output, "\n");
  bvconst_set_extend(b, 31, a, 20, 0);
  fprintf(output, "ext(a, 31, 0) = ");
  bvconst_print(output, b, 31);
  fprintf(output, "\n");
  bvconst_set_extend(b, 31, a, 20, 1);
  fprintf(output, "ext(a, 31, 1) = ");
  bvconst_print(output, b, 31);
  fprintf(output, "\n");
  bvconst_set_extend(b, 31, a, 20, -1);
  fprintf(output, "sgnext(a, 31) = ");
  bvconst_print(output, b, 31);
  fprintf(output, "\n\n");


  random_vector(vector, 20);
  bvconst_set_array(a, vector, 20);
  fprintf(output, "a             = ");
  bvconst_print(output, a, 20);
  fprintf(output, "\n");
  bvconst_set_extend(b, 31, a, 20, 0);
  fprintf(output, "ext(a, 31, 0) = ");
  bvconst_print(output, b, 31);
  fprintf(output, "\n");
  bvconst_set_extend(b, 31, a, 20, 1);
  fprintf(output, "ext(a, 31, 1) = ");
  bvconst_print(output, b, 31);
  fprintf(output, "\n");
  bvconst_set_extend(b, 31, a, 20, -1);
  fprintf(output, "sgnext(a, 31) = ");
  bvconst_print(output, b, 31);
  fprintf(output, "\n\n");


  random_vector(vector, 20);
  bvconst_set_array(a, vector, 20);
  fprintf(output, "a             = ");
  bvconst_print(output, a, 20);
  fprintf(output, "\n");
  bvconst_set_extend(b, 31, a, 20, 0);
  fprintf(output, "ext(a, 31, 0) = ");
  bvconst_print(output, b, 31);
  fprintf(output, "\n");
  bvconst_set_extend(b, 31, a, 20, 1);
  fprintf(output, "ext(a, 31, 1) = ");
  bvconst_print(output, b, 31);
  fprintf(output, "\n");
  bvconst_set_extend(b, 31, a, 20, -1);
  fprintf(output, "sgnext(a, 31) = ");
  bvconst_print(output, b, 31);
  fprintf(output, "\n\n");


  for (i=20; i<=99; i++) {
    random_vector(vector, 20);
    bvconst_set_array(a, vector, 20);
    fprintf(output, "a             = ");
    bvconst_print(output, a, 20);
    fprintf(output, "\n");
    bvconst_set_extend(b, i, a, 20, 0);
    fprintf(output, "ext(a, %2"PRId32", 0) = ", i);
    bvconst_print(output, b, i);
    fprintf(output, "\n");
    bvconst_set_extend(b, i, a, 20, 1);
    fprintf(output, "ext(a, %2"PRId32", 1) = ", i);
    bvconst_print(output, b, i);
    fprintf(output, "\n");
    bvconst_set_extend(b, i, a, 20, -1);
    fprintf(output, "sgnext(a, %2"PRId32") = ", i);
    bvconst_print(output, b, i);
    fprintf(output, "\n\n");
  }


  for (i=32; i<=99; i++) {
    random_vector(vector, 32);
    bvconst_set_array(a, vector, 32);
    fprintf(output, "a             = ");
    bvconst_print(output, a, 32);
    fprintf(output, "\n");
    bvconst_set_extend(b, i, a, 32, 0);
    fprintf(output, "ext(a, %2"PRId32", 0) = ", i);
    bvconst_print(output, b, i);
    fprintf(output, "\n");
    bvconst_set_extend(b, i, a, 32, 1);
    fprintf(output, "ext(a, %2"PRId32", 1) = ", i);
    bvconst_print(output, b, i);
    fprintf(output, "\n");
    bvconst_set_extend(b, i, a, 32, -1);
    fprintf(output, "sgnext(a, %2"PRId32") = ", i);
    bvconst_print(output, b, i);
    fprintf(output, "\n\n");
  }


  random_vector(vector, 120);
  bvconst_set_array(a, vector, 120);
  fprintf(output, "a         = ");
  bvconst_print(output, a, 120);
  fprintf(output, "\n");
  for (i=0; i<=120; i++) {
    fprintf(output, "rshift %3"PRId32": ", i);
    bvconst_shift_right(a, 120, i, 0);
    bvconst_print(output, a, 120);
    fprintf(output, "\n");
    bvconst_set_array(a, vector, 120);
  }
  fprintf(output, "\n");

  random_vector(vector, 120);
  bvconst_set_array(a, vector, 120);
  fprintf(output, "a         = ");
  bvconst_print(output, a, 120);
  fprintf(output, "\n");
  for (i=0; i<=120; i++) {
    fprintf(output, "rshift %3"PRId32": ", i);
    bvconst_shift_right(a, 120, i, 1);
    bvconst_print(output, a, 120);
    fprintf(output, "\n");
    bvconst_set_array(a, vector, 120);
  }
  fprintf(output, "\n");


  random_vector(vector, 120);
  bvconst_set_array(a, vector, 120);
  fprintf(output, "a         = ");
  bvconst_print(output, a, 120);
  fprintf(output, "\n");
  for (i=0; i<=120; i++) {
    fprintf(output, "lshift %3"PRId32": ", i);
    bvconst_shift_left(a, 120, i, 0);
    bvconst_print(output, a, 120);
    fprintf(output, "\n");
    bvconst_set_array(a, vector, 120);
  }
  fprintf(output, "\n");

  random_vector(vector, 120);
  bvconst_set_array(a, vector, 120);
  fprintf(output, "a         = ");
  bvconst_print(output, a, 120);
  fprintf(output, "\n");
  for (i=0; i<=120; i++) {
    fprintf(output, "lshift %3"PRId32": ", i);
    bvconst_shift_left(a, 120, i, 1);
    bvconst_print(output, a, 120);
    fprintf(output, "\n");
    bvconst_set_array(a, vector, 120);
  }
  fprintf(output, "\n");
  //  exit(0);


  fprintf(output, "c = ");
  bvconst_print(output, c, 128);
  fprintf(output, "\n");
  fprintf(output, "d = ");
  bvconst_print(output, d, 128);
  fprintf(output, "\n");
  fprintf(output, "e := c * d\n");
  bvconst_mul2(e, 4, c, d);
  fprintf(output, "e = ");
  bvconst_print(output, e, 128);
  fprintf(output, "\n");
  fprintf(output, "e := d * c\n");
  bvconst_mul2(e, 4, d, c);
  fprintf(output, "e = ");
  bvconst_print(output, e, 128);
  fprintf(output, "\n\n");

  fprintf(output, "b = ");
  bvconst_print(output, b, 128);
  fprintf(output, "\n");
  fprintf(output, "d = ");
  bvconst_print(output, d, 128);
  fprintf(output, "\n");
  fprintf(output, "e := b * d\n");
  bvconst_mul2(e, 4, b, d);
  fprintf(output, "e = ");
  bvconst_print(output, e, 128);
  fprintf(output, "\n\n");



  bvconst_set64(a, 4, 1372919719782793ULL);
  bvconst_set32(b, 4, 12670371);
  fprintf(output, "a = ");
  bvconst_print(output, a, 128);
  fprintf(output, "\n");
  fprintf(output, "b = ");
  bvconst_print(output, b, 128);
  fprintf(output, "\n");
  fprintf(output, "e := a * b\n");
  bvconst_set(c, 4, a);
  fprintf(output, "c = ");
  bvconst_print(output, c, 128);
  fprintf(output, "\n");
  bvconst_mul(c, 4, b);
  fprintf(output, "c = ");
  bvconst_print(output, c, 128);
  fprintf(output, "\n");
  bvconst_mul2(e, 4, a, b);
  fprintf(output, "e = ");
  bvconst_print(output, e, 128);
  fprintf(output, "\n\n");

  mpz_init(z0);
  mpz_init(z1);
  mpz_init(z2);

  bvconst_get_mpz(a, 4, z0);
  fprintf(output, "--> conversion a to mpz: ");
  mpz_out_str(output, 10, z0);
  fprintf(output, "\n");
  bvconst_get_mpz(b, 4, z0);
  fprintf(output, "--> conversion b to mpz: ");
  mpz_out_str(output, 10, z0);
  fprintf(output, "\n");
  bvconst_get_mpz(e, 4, z0);
  fprintf(output, "--> conversion e to mpz: ");
  mpz_out_str(output, 10, z0);
  fprintf(output, "\n\n");

  fprintf(output, "e -= a * b\n");
  bvconst_submul(e, 4, a, b);
  fprintf(output, "e = ");
  bvconst_print(output, e, 128);
  fprintf(output, "\n");
  bvconst_get_mpz(e, 4, z0);
  fprintf(output, "--> conversion e to mpz: ");
  mpz_out_str(output, 10, z0);
  fprintf(output, "\n\n");

  fprintf(output, "\n\nRANDOMIZED\n\n");

  for (i=0; i<10; i++) {
    fprintf(output, "test %"PRId32": e *= a\n", i);
    random_vector(vector, 128);
    bvconst_set_array(a, vector, 128);
    random_vector(vector, 128);
    bvconst_set_array(e, vector, 128);
    bvconst_get_mpz(e, 4, z1);

    fprintf(output, "a  = ");
    bvconst_print(output, a, 128);
    fprintf(output, "\n");
    fprintf(output, "e  = ");
    bvconst_print(output, e, 128);
    fprintf(output, "\n");
    bvconst_mul(e, 4, a);
    fprintf(output, "e' = ");
    bvconst_print(output, e, 128);
    fprintf(output, "\n");

    bvconst_get_mpz(a, 4, z0);
    fprintf(output, "--> conversion a  to mpz: ");
    mpz_out_str(output, 10, z0);
    fprintf(output, "\n");
    fprintf(output, "--> conversion e  to mpz: ");
    mpz_out_str(output, 10, z1);
    fprintf(output, "\n");
    bvconst_get_mpz(e, 4, z2);
    fprintf(output, "--> conversion e' to mpz: ");
    mpz_out_str(output, 10, z2);
    fprintf(output, "\n");

    mpz_mul(z0, z0, z1);
    mpz_fdiv_r_2exp(z0, z0, 128);
    fprintf(output, "--> check:                ");
    mpz_out_str(output, 10, z0);
    fprintf(output, "\n\n");
    assert(mpz_cmp(z0, z2) == 0);
  }

  fprintf(output, "\n\nRANDOMIZED\n\n");
  for (i=0; i<10; i++) {
    fprintf(output, "test %"PRId32", a := - a\n", i);
    random_vector(vector, 128);
    bvconst_set_array(a, vector, 128);
    bvconst_get_mpz(a, 4, z0);

    fprintf(output, "a = ");
    bvconst_print(output, a, 128);
    fprintf(output, "\n");
    bvconst_negate(a, 4);
    fprintf(output, "a = ");
    bvconst_print(output, a, 128);
    fprintf(output, "\n");

    fprintf(output, "--> conversion  a to mpz: ");
    mpz_out_str(output, 10, z0);
    fprintf(output, "\n");
    bvconst_get_mpz(a, 4, z1);
    fprintf(output, "--> conversion -a to mpz: ");
    mpz_out_str(output, 10, z1);
    fprintf(output, "\n");

    mpz_neg(z0, z0);
    mpz_fdiv_r_2exp(z0, z0, 128);
    fprintf(output, "--> check:                ");
    mpz_out_str(output, 10, z0);
    fprintf(output, "\n\n");
    assert(mpz_cmp(z0, z1) == 0);
  }

  fprintf(output, "\n\nRANDOMIZED\n\n");
  for (i=0; i<10; i++) {
    fprintf(output, "test %"PRId32": e := - a\n", i);
    random_vector(vector, 128);
    bvconst_set_array(a, vector, 128);
    fprintf(output, "a = ");
    bvconst_print(output, a, 128);
    fprintf(output, "\n");
    bvconst_negate2(e, 4, a);
    fprintf(output, "e = ");
    bvconst_print(output, e, 128);
    fprintf(output, "\n");

    fprintf(output, "--> conversion a to mpz: ");
    bvconst_get_mpz(a, 4, z0);
    mpz_out_str(output, 10, z0);
    fprintf(output, "\n");
    bvconst_get_mpz(e, 4, z1);
    fprintf(output, "--> conversion e to mpz: ");
    mpz_out_str(output, 10, z1);
    fprintf(output, "\n");

    mpz_neg(z0, z0);
    mpz_fdiv_r_2exp(z0, z0, 128);
    fprintf(output, "--> check:               ");
    mpz_out_str(output, 10, z0);
    fprintf(output, "\n\n");
    assert(mpz_cmp(z0, z1) == 0);
  }

  for (i=0; i<10; i++) {
    fprintf(output, "test %"PRId32", e = a * b\n", i);
    random_vector(vector, 128);
    bvconst_set_array(a, vector, 128);
    random_vector(vector, 128);
    bvconst_set_array(b, vector, 128);

    fprintf(output, "a = ");
    bvconst_print(output, a, 128);
    fprintf(output, "\n");
    fprintf(output, "b = ");
    bvconst_print(output, b, 128);
    fprintf(output, "\n");
    bvconst_mul2(e, 4, a, b);
    fprintf(output, "e = ");
    bvconst_print(output, e, 128);
    fprintf(output, "\n");

    bvconst_get_mpz(a, 4, z0);
    fprintf(output, "--> conversion a to mpz: ");
    mpz_out_str(output, 10, z0);
    fprintf(output, "\n");
    bvconst_get_mpz(b, 4, z1);
    fprintf(output, "--> conversion b to mpz: ");
    mpz_out_str(output, 10, z1);
    fprintf(output, "\n");
    bvconst_get_mpz(e, 4, z2);
    fprintf(output, "--> conversion e to mpz: ");
    mpz_out_str(output, 10, z2);
    fprintf(output, "\n");

    mpz_mul(z0, z0, z1);
    mpz_fdiv_r_2exp(z0, z0, 128);
    fprintf(output, "--> check:               ");
    mpz_out_str(output, 10, z0);
    fprintf(output, "\n\n");
    assert(mpz_cmp(z0, z2) == 0);
  }

  for (i=0; i<10; i++) {
    fprintf(output, "test %"PRId32": e = - (a * b)\n", i);
    random_vector(vector, 128);
    bvconst_set_array(a, vector, 128);
    random_vector(vector, 128);
    bvconst_set_array(b, vector, 128);

    fprintf(output, "a = ");
    bvconst_print(output, a, 128);
    fprintf(output, "\n");
    fprintf(output, "b = ");
    bvconst_print(output, b, 128);
    fprintf(output, "\n");
    bvconst_clear(e, 4);
    bvconst_submul(e, 4, a, b);
    fprintf(output, "e = ");
    bvconst_print(output, e, 128);
    fprintf(output, "\n");

    bvconst_get_mpz(a, 4, z0);
    fprintf(output, "--> conversion a to mpz: ");
    mpz_out_str(output, 10, z0);
    fprintf(output, "\n");
    bvconst_get_mpz(b, 4, z1);
    fprintf(output, "--> conversion b to mpz: ");
    mpz_out_str(output, 10, z1);
    fprintf(output, "\n");
    bvconst_get_mpz(d, 4, z2);
    fprintf(output, "--> conversion d to mpz: ");
    mpz_out_str(output, 10, z2);
    fprintf(output, "\n");
    bvconst_get_mpz(e, 4, z2);
    fprintf(output, "--> conversion e to mpz: ");
    mpz_out_str(output, 10, z2);
    fprintf(output, "\n");

    mpz_mul(z0, z0, z1);
    mpz_neg(z0, z0);
    mpz_fdiv_r_2exp(z0, z0, 128);
    fprintf(output, "--> check:               ");
    mpz_out_str(output, 10, z0);
    fprintf(output, "\n\n");
    assert(mpz_cmp(z0, z2) == 0);
  }

  for (i=0; i<10; i++) {
    fprintf(output, "test %"PRId32": e = a + b\n", i);
    random_vector(vector, 128);
    bvconst_set_array(a, vector, 128);
    random_vector(vector, 128);
    bvconst_set_array(b, vector, 128);

    fprintf(output, "a = ");
    bvconst_print(output, a, 128);
    fprintf(output, "\n");
    fprintf(output, "b = ");
    bvconst_print(output, b, 128);
    fprintf(output, "\n");
    bvconst_add2(e, 4, a, b);
    fprintf(output, "e = ");
    bvconst_print(output, e, 128);
    fprintf(output, "\n");

    bvconst_get_mpz(a, 4, z0);
    fprintf(output, "--> conversion a to mpz: ");
    mpz_out_str(output, 10, z0);
    fprintf(output, "\n");
    bvconst_get_mpz(b, 4, z1);
    fprintf(output, "--> conversion b to mpz: ");
    mpz_out_str(output, 10, z1);
    fprintf(output, "\n");
    bvconst_get_mpz(e, 4, z2);
    fprintf(output, "--> conversion e to mpz: ");
    mpz_out_str(output, 10, z2);
    fprintf(output, "\n");

    mpz_add(z0, z0, z1);
    mpz_fdiv_r_2exp(z0, z0, 128);
    fprintf(output, "--> check:               ");
    mpz_out_str(output, 10, z0);
    fprintf(output, "\n\n");
    assert(mpz_cmp(z0, z2) == 0);
  }

  for (i=0; i<10; i++) {
    fprintf(output, "test %"PRId32": e = a - b\n", i);
    random_vector(vector, 128);
    bvconst_set_array(a, vector, 128);
    random_vector(vector, 128);
    bvconst_set_array(b, vector, 128);

    fprintf(output, "a = ");
    bvconst_print(output, a, 128);
    fprintf(output, "\n");
    fprintf(output, "b = ");
    bvconst_print(output, b, 128);
    fprintf(output, "\n");
    bvconst_sub2(e, 4, a, b);
    fprintf(output, "e = ");
    bvconst_print(output, e, 128);
    fprintf(output, "\n");

    bvconst_get_mpz(a, 4, z0);
    fprintf(output, "--> conversion a to mpz: ");
    mpz_out_str(output, 10, z0);
    fprintf(output, "\n");
    bvconst_get_mpz(b, 4, z1);
    fprintf(output, "--> conversion b to mpz: ");
    mpz_out_str(output, 10, z1);
    fprintf(output, "\n");
    bvconst_get_mpz(e, 4, z2);
    fprintf(output, "--> conversion e to mpz: ");
    mpz_out_str(output, 10, z2);
    fprintf(output, "\n");

    mpz_sub(z0, z0, z1);
    mpz_fdiv_r_2exp(z0, z0, 128);
    fprintf(output, "--> check:               ");
    mpz_out_str(output, 10, z0);
    fprintf(output, "\n\n");
    assert(mpz_cmp(z0, z2) == 0);
  }

  for (i=0; i<10; i++) {
    fprintf(output, "\ntest %"PRId32": comparisons\n", i);
    random_vector(vector, 25);
    bvconst_set_array(a, vector, 25);
    random_vector(vector, 25);
    bvconst_set_array(b, vector, 25);

    fprintf(output, "a = ");
    bvconst_print(output, a, 25);
    fprintf(output, "\n");
    fprintf(output, "b = ");
    bvconst_print(output, b, 25);
    fprintf(output, "\n");

    bvconst_normalize(a, 25);
    bvconst_normalize(b, 25);
    fprintf(output, "Unsigned tests\n");
    fprintf(output, " a le b: %d\n", bvconst_le(a, b, 25));
    fprintf(output, " a ge b: %d\n", bvconst_ge(a, b, 25));
    fprintf(output, " a lt b: %d\n", bvconst_lt(a, b, 25));
    fprintf(output, " a gt b: %d\n", bvconst_gt(a, b, 25));

    fprintf(output, "Signed tests\n");
    fprintf(output, " a sle b: %d\n", bvconst_sle(a, b, 25));
    fprintf(output, " a sge b: %d\n", bvconst_sge(a, b, 25));
    fprintf(output, " a slt b: %d\n", bvconst_slt(a, b, 25));
    fprintf(output, " a sgt b: %d\n", bvconst_sgt(a, b, 25));
  }


  for (i=0; i<10; i++) {
    fprintf(output, "\ntest %"PRId32": comparisons\n", i);
    random_vector(vector, 32);
    bvconst_set_array(a, vector, 32);
    random_vector(vector, 32);
    bvconst_set_array(b, vector, 32);

    fprintf(output, "a = ");
    bvconst_print(output, a, 32);
    fprintf(output, "\n");
    fprintf(output, "b = ");
    bvconst_print(output, b, 32);
    fprintf(output, "\n");

    bvconst_normalize(a, 32);
    bvconst_normalize(b, 32);
    fprintf(output, "Unsigned tests\n");
    fprintf(output, " a le b: %d\n", bvconst_le(a, b, 32));
    fprintf(output, " a ge b: %d\n", bvconst_ge(a, b, 32));
    fprintf(output, " a lt b: %d\n", bvconst_lt(a, b, 32));
    fprintf(output, " a gt b: %d\n", bvconst_gt(a, b, 32));

    fprintf(output, "Signed tests\n");
    fprintf(output, " a sle b: %d\n", bvconst_sle(a, b, 32));
    fprintf(output, " a sge b: %d\n", bvconst_sge(a, b, 32));
    fprintf(output, " a slt b: %d\n", bvconst_slt(a, b, 32));
    fprintf(output, " a sgt b: %d\n", bvconst_sgt(a, b, 32));
  }

  for (i=0; i<10; i++) {
    fprintf(output, "\ntest %"PRId32": comparisons\n", i);
    random_vector(vector, 33);
    bvconst_set_array(a, vector, 33);
    random_vector(vector, 33);
    bvconst_set_array(b, vector, 33);

    fprintf(output, "a = ");
    bvconst_print(output, a, 33);
    fprintf(output, "\n");
    fprintf(output, "b = ");
    bvconst_print(output, b, 33);
    fprintf(output, "\n");

    bvconst_normalize(a, 33);
    bvconst_normalize(b, 33);
    fprintf(output, "Unsigned tests\n");
    fprintf(output, " a le b: %d\n", bvconst_le(a, b, 33));
    fprintf(output, " a ge b: %d\n", bvconst_ge(a, b, 33));
    fprintf(output, " a lt b: %d\n", bvconst_lt(a, b, 33));
    fprintf(output, " a gt b: %d\n", bvconst_gt(a, b, 33));

    fprintf(output, "Signed tests\n");
    fprintf(output, " a sle b: %d\n", bvconst_sle(a, b, 33));
    fprintf(output, " a sge b: %d\n", bvconst_sge(a, b, 33));
    fprintf(output, " a slt b: %d\n", bvconst_slt(a, b, 33));
    fprintf(output, " a sgt b: %d\n", bvconst_sgt(a, b, 33));
  }

  for (i=0; i<10; i++) {
    fprintf(output, "\ntest %"PRId32": comparisons\n", i);
    random_vector(vector, 63);
    bvconst_set_array(a, vector, 63);
    random_vector(vector, 63);
    bvconst_set_array(b, vector, 63);

    fprintf(output, "a = ");
    bvconst_print(output, a, 63);
    fprintf(output, "\n");
    fprintf(output, "b = ");
    bvconst_print(output, b, 63);
    fprintf(output, "\n");

    bvconst_normalize(a, 63);
    bvconst_normalize(b, 63);
    fprintf(output, "Unsigned tests\n");
    fprintf(output, " a le b: %d\n", bvconst_le(a, b, 63));
    fprintf(output, " a ge b: %d\n", bvconst_ge(a, b, 63));
    fprintf(output, " a lt b: %d\n", bvconst_lt(a, b, 63));
    fprintf(output, " a gt b: %d\n", bvconst_gt(a, b, 63));

    fprintf(output, "Signed tests\n");
    fprintf(output, " a sle b: %d\n", bvconst_sle(a, b, 63));
    fprintf(output, " a sge b: %d\n", bvconst_sge(a, b, 63));
    fprintf(output, " a slt b: %d\n", bvconst_slt(a, b, 63));
    fprintf(output, " a sgt b: %d\n", bvconst_sgt(a, b, 63));
  }

  for (i=0; i<10; i++) {
    fprintf(output, "\ntest %"PRId32": comparisons\n", i);
    random_vector(vector, 64);
    bvconst_set_array(a, vector, 64);
    random_vector(vector, 64);
    bvconst_set_array(b, vector, 64);

    fprintf(output, "a = ");
    bvconst_print(output, a, 64);
    fprintf(output, "\n");
    fprintf(output, "b = ");
    bvconst_print(output, b, 64);
    fprintf(output, "\n");

    bvconst_normalize(a, 64);
    bvconst_normalize(b, 64);
    fprintf(output, "Unsigned tests\n");
    fprintf(output, " a le b: %d\n", bvconst_le(a, b, 64));
    fprintf(output, " a ge b: %d\n", bvconst_ge(a, b, 64));
    fprintf(output, " a lt b: %d\n", bvconst_lt(a, b, 64));
    fprintf(output, " a gt b: %d\n", bvconst_gt(a, b, 64));

    fprintf(output, "Signed tests\n");
    fprintf(output, " a sle b: %d\n", bvconst_sle(a, b, 64));
    fprintf(output, " a sge b: %d\n", bvconst_sge(a, b, 64));
    fprintf(output, " a slt b: %d\n", bvconst_slt(a, b, 64));
    fprintf(output, " a sgt b: %d\n", bvconst_sgt(a, b, 64));
  }

  fprintf(output, "\nMore comparisons\n");
  random_vector(vector, 64);
  bvconst_set_array(a, vector, 64);
  bvconst_set_array(b, vector, 64);
  fprintf(output, "a = ");
  bvconst_print(output, a, 64);
  fprintf(output, "\n");
  fprintf(output, "b = ");
  bvconst_print(output, b, 64);
  fprintf(output, "\n");

  bvconst_normalize(a, 64);
  bvconst_normalize(b, 64);
  fprintf(output, "Unsigned tests\n");
  fprintf(output, " a le b: %d\n", bvconst_le(a, b, 64));
  fprintf(output, " a ge b: %d\n", bvconst_ge(a, b, 64));
  fprintf(output, " a lt b: %d\n", bvconst_lt(a, b, 64));
  fprintf(output, " a gt b: %d\n", bvconst_gt(a, b, 64));

  fprintf(output, "Signed tests\n");
  fprintf(output, " a sle b: %d\n", bvconst_sle(a, b, 64));
  fprintf(output, " a sge b: %d\n", bvconst_sge(a, b, 64));
  fprintf(output, " a slt b: %d\n", bvconst_slt(a, b, 64));
  fprintf(output, " a sgt b: %d\n", bvconst_sgt(a, b, 64));


  random_vector(vector, 65);
  bvconst_set_array(a, vector, 65);
  bvconst_set_array(b, vector, 65);
  fprintf(output, "a = ");
  bvconst_print(output, a, 65);
  fprintf(output, "\n");
  fprintf(output, "b = ");
  bvconst_print(output, b, 65);
  fprintf(output, "\n");

  bvconst_normalize(a, 65);
  bvconst_normalize(b, 65);
  fprintf(output, "Unsigned tests\n");
  fprintf(output, " a le b: %d\n", bvconst_le(a, b, 65));
  fprintf(output, " a ge b: %d\n", bvconst_ge(a, b, 65));
  fprintf(output, " a lt b: %d\n", bvconst_lt(a, b, 65));
  fprintf(output, " a gt b: %d\n", bvconst_gt(a, b, 65));

  fprintf(output, "Signed tests\n");
  fprintf(output, " a sle b: %d\n", bvconst_sle(a, b, 65));
  fprintf(output, " a sge b: %d\n", bvconst_sge(a, b, 65));
  fprintf(output, " a slt b: %d\n", bvconst_slt(a, b, 65));
  fprintf(output, " a sgt b: %d\n", bvconst_sgt(a, b, 65));

  random_vector(vector, 63);
  bvconst_set_array(a, vector, 63);
  bvconst_set_array(b, vector, 63);
  fprintf(output, "a = ");
  bvconst_print(output, a, 63);
  fprintf(output, "\n");
  fprintf(output, "b = ");
  bvconst_print(output, b, 63);
  fprintf(output, "\n");

  bvconst_normalize(a, 63);
  bvconst_normalize(b, 63);
  fprintf(output, "Unsigned tests\n");
  fprintf(output, " a le b: %d\n", bvconst_le(a, b, 63));
  fprintf(output, " a ge b: %d\n", bvconst_ge(a, b, 63));
  fprintf(output, " a lt b: %d\n", bvconst_lt(a, b, 63));
  fprintf(output, " a gt b: %d\n", bvconst_gt(a, b, 63));

  fprintf(output, "Signed tests\n");
  fprintf(output, " a sle b: %d\n", bvconst_sle(a, b, 63));
  fprintf(output, " a sge b: %d\n", bvconst_sge(a, b, 63));
  fprintf(output, " a slt b: %d\n", bvconst_slt(a, b, 63));
  fprintf(output, " a sgt b: %d\n", bvconst_sgt(a, b, 63));

  fprintf(output, "\nTest powers of two\n");
  mpz_set_ui(z0, 1);
  for (i=0; i<128; i++) {
    fprintf(output, "z0 = ");
    mpz_out_str(output, 10, z0);
    fprintf(output, "\n");
    bvconst_set_mpz(a, 4, z0);
    fprintf(output, "a = ");
    bvconst_print(output, a, 128);
    fprintf(output, "\n");

    n = bvconst_is_power_of_two(a, 4);
    if (n < 0) {
      fprintf(output, "--> not a power of 2\n\n");
    } else {
      fprintf(output, "--> a = 2^%"PRId32"\n\n", n);
    }
    mpz_add(z0, z0, z0);
  }


  a[0] = 0;
  a[1] = 1024;
  a[2] = 0;
  a[3] = 36136287;
  fprintf(output, "a = ");
  bvconst_print(output, a, 128);
  fprintf(output, "\n");
  n = bvconst_is_power_of_two(a, 4);
  if (n < 0) {
    fprintf(output, "--> not a power of 2\n\n");
  } else {
    fprintf(output, "--> a = 2^%"PRId32"\n\n", n);
  }

  a[0] = 0;
  a[1] = 1024;
  a[2] = 31209;
  a[3] = 0;
  fprintf(output, "a = ");
  bvconst_print(output, a, 128);
  fprintf(output, "\n");
  n = bvconst_is_power_of_two(a, 4);
  if (n < 0) {
    fprintf(output, "--> not a power of 2\n\n");
  } else {
    fprintf(output, "--> a = 2^%"PRId32"\n\n", n);
  }


  a[0] = 0;
  a[1] = 1024;
  a[2] = 0;
  a[3] = 0;
  fprintf(output, "a = ");
  bvconst_print(output, a, 128);
  fprintf(output, "\n");
  n = bvconst_is_power_of_two(a, 4);
  if (n < 0) {
    fprintf(output, "--> not a power of 2\n\n");
  } else {
    fprintf(output, "--> a = 2^%"PRId32"\n\n", n);
  }


  a[0] = 128;
  a[1] = 1024;
  a[2] = 0;
  a[3] = 0;
  fprintf(output, "a = ");
  bvconst_print(output, a, 128);
  fprintf(output, "\n");
  n = bvconst_is_power_of_two(a, 4);
  if (n < 0) {
    fprintf(output, "--> not a power of 2\n\n");
  } else {
    fprintf(output, "--> a = 2^%"PRId32"\n\n", n);
  }




  bvconst_clear(a, 4);
  for (i=0; i<256; i++) {
    fprintf(output, "a = ");
    bvconst_print(output, a, 128);
    fprintf(output, "\n");

    n = bvconst_is_power_of_two(a, 4);
    if (n < 0) {
      fprintf(output, "--> not a power of 2\n\n");
    } else {
      fprintf(output, "--> a = 2^%"PRId32"\n\n", n);
    }
    bvconst_add_one(a, 4);
  }

  for (i=0; i<10; i++) {
    fprintf(output, "test %"PRId32": power of two\n", i);
    random_vector(vector, 128);
    bvconst_set_array(a, vector, 128);

    for (j=0; j<64; j++) {
      fprintf(output, "a = ");
      bvconst_print(output, a, 128);
      fprintf(output, "\n");
      n = bvconst_is_power_of_two(a, 4);
      if (n < 0) {
	fprintf(output, "--> not a power of 2\n\n");
      } else {
	fprintf(output, "--> a = 2^%"PRId32"\n\n", n);
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
    fprintf(output, "---> mulpower: a = b^%"PRIu32" = 2^%"PRIu32"\n", i, i);
    fprintf(output, "     b = ");
    bvconst_print(output, b, 128);
    fprintf(output, "\n");
    fprintf(output, "     a = ");
    bvconst_print(output, a, 128);
    fprintf(output, "\n");
  }

  // test mulpower
  for (i=0; i<40; i++) {
    bvconst_set32(a, 4, 4);       // a = 0b0..00100
    bvconst_set_minus_one(b, 4);  // b = 0b11..1111
    // compute a * b^i = -4 or +4
    bvconst_mulpower(a, 4, b, i);
    fprintf(output, "---> mulpower: a = 4 * b^%"PRIu32" = 4 * (-1)^%"PRIu32"\n", i, i);
    fprintf(output, "     b = ");
    bvconst_print(output, b, 128);
    fprintf(output, "\n");
    fprintf(output, "     a = ");
    bvconst_print(output, a, 128);
    fprintf(output, "\n");
  }

  // test mulpower
  for (i=0; i<40; i++) {
    bvconst_set32(a, 4, 4);     // a = 0b0..00100
    bvconst_clear(b, 4);        // b = 0
    // compute a * b^i = 0
    bvconst_mulpower(a, 4, b, i);
    fprintf(output, "---> mulpower: a = 4 * b^%"PRIu32"\n", i);
    fprintf(output, "     b = ");
    bvconst_print(output, b, 128);
    fprintf(output, "\n");
    fprintf(output, "     a = ");
    bvconst_print(output, a, 128);
    fprintf(output, "\n");
  }


  // test is_one and is_minus_one
  fprintf(output, "\n\n");
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
    fprintf(output, "---> %"PRIu32" bits\n", i);
    fprintf(output, "a = ");
    bvconst_print(output, a, i);
    fprintf(output, ": is_one = %s, is_minus_one = %s\n", b2str(bvconst_is_one(a, n)), b2str(bvconst_is_minus_one(a, i)));

    fprintf(output, "b = ");
    bvconst_print(output, b, i);
    fprintf(output, ": is_one = %s, is_minus_one = %s\n", b2str(bvconst_is_one(b, n)), b2str(bvconst_is_minus_one(b, i)));

    fprintf(output, "c = ");
    bvconst_print(output, c, i);
    fprintf(output, ": is_one = %s, is_minus_one = %s\n", b2str(bvconst_is_one(c, n)), b2str(bvconst_is_minus_one(c, i)));

    fprintf(output, "d = ");
    bvconst_print(output, d, i);
    fprintf(output, ": is_one = %s, is_minus_one = %s\n", b2str(bvconst_is_one(d, n)), b2str(bvconst_is_minus_one(d, i)));

    fprintf(output, "\n");
    fflush(output);
  }

  // test is_min_signed and is_max_signed
  fprintf(output, "\n\n");
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

    fprintf(output, "---> %"PRIu32" bits\n", i);
    fprintf(output, "a = ");
    bvconst_print(output, a, i);
    fprintf(output, ": is_min_signed = %s, is_max_signed = %s\n", b2str(bvconst_is_min_signed(a, i)), b2str(bvconst_is_max_signed(a, i)));

    fprintf(output, "b = ");
    bvconst_print(output, b, i);
    fprintf(output, ": is_min_signed = %s, is_max_signed = %s\n", b2str(bvconst_is_min_signed(b, i)), b2str(bvconst_is_max_signed(b, i)));

    fprintf(output, "c = ");
    bvconst_print(output, c, i);
    fprintf(output, ": is_min_signed = %s, is_max_signed = %s\n", b2str(bvconst_is_min_signed(c, i)), b2str(bvconst_is_max_signed(c, i)));

    fprintf(output, "d = ");
    bvconst_print(output, d, i);
    fprintf(output, ": is_min_signed = %s, is_max_signed = %s\n", b2str(bvconst_is_min_signed(d, i)), b2str(bvconst_is_max_signed(d, i)));

    fprintf(output, "e = ");
    bvconst_print(output, e, i);
    fprintf(output, ": is_min_signed = %s, is_max_signed = %s\n", b2str(bvconst_is_min_signed(e, i)), b2str(bvconst_is_max_signed(e, i)));

    fprintf(output, "\n");
    fflush(output);
  }



  mpz_clear(z0);
  mpz_clear(z1);
  mpz_clear(z2);


  free_constants(a, b, c, d, e);


  return yices_thread_exit();
}


int main(int argc, char* argv[]) {

  if(argc != 2){
    mt_test_usage(argc, argv);
    return 0;
  } else {
    int32_t nthreads = atoi(argv[1]);

    init_bvconstants();

    if(nthreads < 0){
      fprintf(stderr, "thread number must be positive!\n");
      exit(EXIT_FAILURE);
    } else if(nthreads == 0){
      thread_data_t tdata = {0, stdout};
      test_thread(&tdata);
    } else {
      launch_threads(nthreads, NULL, 0, "test_bvconst_mt", test_thread, true);
    }

    cleanup_bvconstants();
  }

  return 0;
}


