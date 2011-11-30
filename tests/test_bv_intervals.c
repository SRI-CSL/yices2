/*
 * TEST INTERVAL OPERATIONS FOR LARGE BIT-VECTORS
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>

#include "bv_constants.h"
#include "bv_intervals.h"

#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif



/*
 * Print an interval
 */
static void show_interval_unsigned(FILE *f, bv_interval_t *intv) {
  uint32_t n;

  n = intv->nbits;
  if (bv_interval_is_triv_u(intv)) {
    fprintf(f, "[0, UMAX %"PRIu32" bits]", n);
  } else {
    fputc('[', f);
    bvconst_print(f, intv->low, n);
    fputs(", ", f);
    bvconst_print(f, intv->high, n);
    fprintf(f, " %"PRIu32" bits]", n); 
  }
}


static void show_interval_signed(FILE *f, bv_interval_t *intv) {
  uint32_t n;

  n = intv->nbits;
  if (bv_interval_is_triv_s(intv)) {
    fprintf(f, "[MIN, MAX %"PRIu32" bits]", n);
  } else {
    fputc('[', f);
    bvconst_print(f, intv->low, n);
    fputs(", ", f);
    bvconst_print(f, intv->high, n);
    fprintf(f, " %"PRIu32" bits]", n); 
  }
}



/*
 * Random 32bit unsigned integer
 */
static uint32_t random_uint32(void) {
  return (((uint32_t) (random() & 0xFFFF)) << 16) | ((uint32_t) (random() & 0xFFFF));
}

/*
 * Store a random bitvector in v
 * - n = number of bits
 */
static void random_bv(uint32_t *v, uint32_t n) {
  uint32_t i, w;

  w = (n + 31) >> 5;
  for (i=0; i<w; i++) {
    v[i] = random_uint32();
  }
  bvconst_normalize(v, n);  
}


/*
 * Initialize array b with bit-vectors of size n
 * - m = number of elements in b
 * - m must be at least 5
 */
static void init_bvconst_array(uint32_t **b, uint32_t m, uint32_t n) {
  uint32_t *v;
  uint32_t i, w;

  assert(m >= 5);

  w = (n + 31) >> 5;

  // b[0] = 0b000..00
  v = bvconst_alloc(w);
  bvconst_clear(v, w);
  b[0] = v;

  // b[1] = 0b000..01
  v = bvconst_alloc(w);
  bvconst_set_one(v, w);
  b[1] = v;

  // b[2] = 0b0111..1
  v = bvconst_alloc(w);
  bvconst_set_max_signed(v, n);
  b[2] = v;

  // b[3] = 0b100..0
  v = bvconst_alloc(w);
  bvconst_set_min_signed(v, n);
  b[3] = v;

  // b[4] = 0b1111..1
  v = bvconst_alloc(w);
  bvconst_set_minus_one(v, w);
  bvconst_normalize(v, n);
  b[4] = v;

  // for the rest: add random vectors
  for (i=5; i<m; i++) {
    v = bvconst_alloc(w);
    random_bv(v, n);
    b[i] = v;
  }
}


/*
 * Free all vectors in array b
 * - m = size of b
 * - n = number of bits in each element of b
 */
static void delete_bvconst_array(uint32_t **b, uint32_t m, uint32_t n) {
  uint32_t i, w;

  w = (n + 31) >> 5;
  for (i=0; i<m; i++) {
    bvconst_free(b[i], w);
    b[i] =  NULL;
  }
}





/*
 * TESTS OF SUM
 */

/*
 * Build the sum of [a, b] and [c, d]
 * - store the result in intv
 */
static void test_sum_unsigned(bv_interval_t *intv, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d, uint32_t n) {
  bv_interval_t aux;

  assert(bvconst_is_normalized(a, n) && bvconst_is_normalized(b, n) && bvconst_le(a, b, n));
  assert(bvconst_is_normalized(c, n) && bvconst_is_normalized(d, n) && bvconst_le(c, d, n));

  init_bv_interval(&aux);
  bv_interval_set_u(&aux, c, d, n);  // aux := [c, d]
  bv_interval_set_u(intv, a, b, n);  // intv := [a, b]

  printf("--- Test sum unsigned ---\n");
  printf("a =  ");
  show_interval_unsigned(stdout, intv);
  printf("\nb =  ");
  show_interval_unsigned(stdout, &aux);
  printf("\n");
  fflush(stdout);

  bv_interval_add_u(intv, &aux);
  printf("Sum: ");
  show_interval_unsigned(stdout, intv);
  printf("\n\n");

  delete_bv_interval(&aux);
}

static void test_sum_signed(bv_interval_t *intv, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d, uint32_t n) {
  bv_interval_t aux;

  assert(bvconst_is_normalized(a, n) && bvconst_is_normalized(b, n) && bvconst_sle(a, b, n));
  assert(bvconst_is_normalized(c, n) && bvconst_is_normalized(d, n) && bvconst_sle(c, d, n));

  init_bv_interval(&aux);
  bv_interval_set_s(&aux, c, d, n);  // aux := [c, d]
  bv_interval_set_s(intv, a, b, n);  // intv := [a, b]

  printf("--- Test sum signed ---\n");
  printf("a =  ");
  show_interval_signed(stdout, intv);
  printf("\nb =  ");
  show_interval_signed(stdout, &aux);
  printf("\n");
  fflush(stdout);

  bv_interval_add_s(intv, &aux);
  printf("Sum: ");
  show_interval_signed(stdout, intv);
  printf("\n\n");

  delete_bv_interval(&aux);
}


/*
 * Check whether x belongs to interval [a, b]
 */
static bool in_interval_u(uint32_t *x, uint32_t *a, uint32_t *b, uint32_t n) {
  assert(bvconst_is_normalized(x, n) && bvconst_is_normalized(a, n) && bvconst_is_normalized(b, n));
  return bvconst_le(a, x, n) && bvconst_le(x, b, n);
}

// signed version
static bool in_interval_s(uint32_t *x, uint32_t *a, uint32_t *b, uint32_t n) {
  assert(bvconst_is_normalized(x, n) && bvconst_is_normalized(a, n) && bvconst_is_normalized(b, n));
  return bvconst_sle(a, x, n) && bvconst_sle(x, b, n);
}

// check whether x belongs to intv
static bool member_u(uint32_t *x, bv_interval_t *intv) {
  return in_interval_u(x, intv->low, intv->high, intv->nbits);
}

static bool member_s(uint32_t *x, bv_interval_t *intv) {
  return in_interval_s(x, intv->low, intv->high, intv->nbits);
}


/*
 * Check the result of sum:
 * - go through all pairs of constants u and v in array data
 * - if u belongs to [a, b] and v belongs to [c, d], then check whether u + v belongs to a
 * - n = number of bits in all vectors
 * - m = size of the data array 
 */
static void check_sum_unsigned(bv_interval_t *intv, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d, uint32_t n,
			       uint32_t **data, uint32_t m) {
  bvconstant_t buffer;
  uint32_t *u, *v;  
  uint32_t i, j, w;

  
  init_bvconstant(&buffer);
  bvconstant_set_bitsize(&buffer, n);
  w = buffer.width;

  assert(w == (n + 31) >> 5);

  for (i=0; i<m; i++) {
    u = data[i];
    if (in_interval_u(u, a, b, n)) {
      for (j=0; j<m; j++) {
	v = data[j];
	if (in_interval_u(v, c, d, n)) {
	  // u is in [a, b] and v is in [c, d]
	  bvconst_set(buffer.data, w, u);
	  bvconst_add(buffer.data, w, v); 
	  bvconst_normalize(buffer.data, n); // buffer := u + v modulo 2^n
	  if (! member_u(buffer.data, intv)) {
	    fprintf(stderr, "FAILED\n");
	    fprintf(stderr, "u = ");
	    bvconst_print(stderr, u, n);
	    fprintf(stderr, "\n");
	    fprintf(stderr, "v = ");
	    bvconst_print(stderr, v, n);
	    fprintf(stderr, "\n");
	    fprintf(stderr, "u + v = ");
	    bvconst_print(stderr, buffer.data, n);
	    fprintf(stderr, "\n");
	    fprintf(stderr, "u + v should be in the sum interval\n");
	    fflush(stderr);
	    exit(1);
	  }
	}
      }
    }
  }

  delete_bvconstant(&buffer);
}



static void check_sum_signed(bv_interval_t *intv, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d, uint32_t n,
			     uint32_t **data, uint32_t m) {
  bvconstant_t buffer;
  uint32_t *u, *v;  
  uint32_t i, j, w;

  
  init_bvconstant(&buffer);
  bvconstant_set_bitsize(&buffer, n);
  w = buffer.width;

  assert(w == (n + 31) >> 5);

  for (i=0; i<m; i++) {
    u = data[i];
    if (in_interval_s(u, a, b, n)) {
      for (j=0; j<m; j++) {
	v = data[j];
	if (in_interval_s(v, c, d, n)) {
	  // u is in [a, b] and v is in [c, d]
	  bvconst_set(buffer.data, w, u);
	  bvconst_add(buffer.data, w, v); 
	  bvconst_normalize(buffer.data, n); // buffer := u + v modulo 2^n
	  if (! member_s(buffer.data, intv)) {
	    fprintf(stderr, "FAILED\n");
	    fprintf(stderr, "u = ");
	    bvconst_print(stderr, u, n);
	    fprintf(stderr, "\n");
	    fprintf(stderr, "v = ");
	    bvconst_print(stderr, v, n);
	    fprintf(stderr, "\n");
	    fprintf(stderr, "u + v = ");
	    bvconst_print(stderr, buffer.data, n);
	    fprintf(stderr, "\n");
	    fprintf(stderr, "u + v should be in the sum interval\n");
	    fflush(stderr);
	    exit(1);
	  }
	}
      }
    }
  }

  delete_bvconstant(&buffer);
}



/*
 * Test sum between [a, b] and all pairs of vectors in array data
 */
static void test_sum_unsigned_all_pairs(uint32_t *a, uint32_t *b, uint32_t n, uint32_t **data, uint32_t m) {
  bv_interval_t test;
  uint32_t *u, *v, *w;
  uint32_t i, j;

  init_bv_interval(&test);
  for (i=0; i<m; i++) {
    for (j=i; j<m; j++) {
      u = data[i];
      v = data[j];
      if (bvconst_gt(u, v, n)) {
	// swap
	w = u; u = v; v = w;
      }
      test_sum_unsigned(&test, a, b, u, v, n);
      check_sum_unsigned(&test, a, b, u, v, n, data, m);
    }
  }
  delete_bv_interval(&test);
}


static void test_sum_signed_all_pairs(uint32_t *a, uint32_t *b, uint32_t n, uint32_t **data, uint32_t m) {
  bv_interval_t test;
  uint32_t *u, *v, *w;
  uint32_t i, j;

  init_bv_interval(&test);
  for (i=0; i<m; i++) {
    for (j=i; j<m; j++) {
      u = data[i];
      v = data[j];
      if (bvconst_sgt(u, v, n)) {
	// swap
	w = u; u = v; v = w;
      }
      test_sum_signed(&test, a, b, u, v, n);
      check_sum_signed(&test, a, b, u, v, n, data, m);
    }
  }
  delete_bv_interval(&test);

}


/*
 * Full sum test
 */
static void full_test_sum_unsigned(uint32_t **data, uint32_t m, uint32_t n) {
  uint32_t *u, *v, *w;
  uint32_t i, j;

  printf("\n*** FULL TEST SUM UNSIGNED (bitsize = %"PRIu32") ***\n\n", n);

  for (i=0; i<m; i++) {
    for (j=i; j<m; j++) {
      u = data[i];
      v = data[j];
      if (bvconst_gt(u, v, n)) {
	// swap
	w = u; u = v; v = w;
      }
      test_sum_unsigned_all_pairs(u, v, n, data, m);
    }
  }
}


static void full_test_sum_signed(uint32_t **data, uint32_t m, uint32_t n) {
  uint32_t *u, *v, *w;
  uint32_t i, j;

  printf("\n*** FULL TEST SUM SIGNED (bitsize = %"PRIu32") ***\n\n", n);

  for (i=0; i<m; i++) {
    for (j=i; j<m; j++) {
      u = data[i];
      v = data[j];
      if (bvconst_sgt(u, v, n)) {
	// swap
	w = u; u = v; v = w;
      }
      test_sum_signed_all_pairs(u, v, n, data, m);
    }
  }
}





/*
 * Basic tests
 */
int main(void) {
  uint32_t *b[20];

  init_bvconstants();

  init_bvconst_array(b, 20, 10);
  full_test_sum_unsigned(b, 20, 10);
  full_test_sum_signed(b, 20, 10);
  delete_bvconst_array(b, 20, 10);
  

  init_bvconst_array(b, 20, 93);
  full_test_sum_unsigned(b, 20, 93);
  full_test_sum_signed(b, 20, 93);
  delete_bvconst_array(b, 20, 93);
  

  cleanup_bvconstants();

  return 0;
}
