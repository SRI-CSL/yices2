/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST INTERVAL OPERATIONS FOR LARGE BIT-VECTORS
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>

#include "terms/bv_constants.h"
#include "solvers/bv/bv_intervals.h"

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
 * Random bitvector with a small absolute value
 */
static void small_random_bv(uint32_t *v, uint32_t n) {
  uint32_t w;
  int32_t x;

  w = (n + 31) >> 5;
  x = (random() & 0xFFF) >> 4;
  assert(0 <= x && x <= 255);
  if (x >= 128) {
    x = 256 - x;
  }

  bvconst_set32_signed(v, w, x);
  bvconst_normalize(v, n);
}


/*
 * Initialize array b with bit-vectors of size n
 * - m = number of elements in b
 * - m must be at least 10
 */
static void init_bvconst_array(uint32_t **b, uint32_t m, uint32_t n) {
  uint32_t *v;
  uint32_t i, w;

  assert(m >= 10);

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

  // add vectors with a some small absolute value
  for (i=5; i<10; i++) {
    v = bvconst_alloc(w);
    small_random_bv(v, n);
    b[i] = v;
  }

  // for the rest: add random vectors
  for (i=10; i<m; i++) {
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
 * TESTS
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
 * Build the sum of [a, b] and [c, d]
 * - store the result in intv
 */
static void test_diff_unsigned(bv_interval_t *intv, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d, uint32_t n) {
  bv_interval_t aux;

  assert(bvconst_is_normalized(a, n) && bvconst_is_normalized(b, n) && bvconst_le(a, b, n));
  assert(bvconst_is_normalized(c, n) && bvconst_is_normalized(d, n) && bvconst_le(c, d, n));

  init_bv_interval(&aux);
  bv_interval_set_u(&aux, c, d, n);  // aux := [c, d]
  bv_interval_set_u(intv, a, b, n);  // intv := [a, b]

  printf("--- Test diff unsigned ---\n");
  printf("a =   ");
  show_interval_unsigned(stdout, intv);
  printf("\nb =   ");
  show_interval_unsigned(stdout, &aux);
  printf("\n");
  fflush(stdout);

  bv_interval_sub_u(intv, &aux);
  printf("Diff: ");
  show_interval_unsigned(stdout, intv);
  printf("\n\n");

  delete_bv_interval(&aux);
}

static void test_diff_signed(bv_interval_t *intv, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d, uint32_t n) {
  bv_interval_t aux;

  assert(bvconst_is_normalized(a, n) && bvconst_is_normalized(b, n) && bvconst_sle(a, b, n));
  assert(bvconst_is_normalized(c, n) && bvconst_is_normalized(d, n) && bvconst_sle(c, d, n));

  init_bv_interval(&aux);
  bv_interval_set_s(&aux, c, d, n);  // aux := [c, d]
  bv_interval_set_s(intv, a, b, n);  // intv := [a, b]

  printf("--- Test diff signed ---\n");
  printf("a =   ");
  show_interval_signed(stdout, intv);
  printf("\nb =   ");
  show_interval_signed(stdout, &aux);
  printf("\n");
  fflush(stdout);

  bv_interval_sub_s(intv, &aux);
  printf("Diff: ");
  show_interval_signed(stdout, intv);
  printf("\n\n");

  delete_bv_interval(&aux);
}



/*
 * Addmul: store [a, b] + c * [d, e] in intv
 */
static void test_addmul_unsigned(bv_interval_t *intv, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d, uint32_t *e, uint32_t n) {
  bv_interval_t aux;
  bv_aux_buffers_t buffers;

  assert(bvconst_is_normalized(a, n) && bvconst_is_normalized(b, n) && bvconst_le(a, b, n));
  assert(bvconst_is_normalized(d, n) && bvconst_is_normalized(e, n) && bvconst_le(d, e, n));
  assert(bvconst_is_normalized(c, n));

  init_bv_aux_buffers(&buffers);
  init_bv_interval(&aux);
  bv_interval_set_u(&aux, d, e, n); // aux := [d, e]
  bv_interval_set_u(intv, a, b, n); // intv := [a, b]

  printf("--- Test addmul unsigned ---\n");
  printf("a =  ");
  show_interval_unsigned(stdout, intv);
  printf("\nb =  ");
  show_interval_unsigned(stdout, &aux);
  printf("\nc =  ");
  bvconst_print(stdout, c, n);
  printf("\n");
  fflush(stdout);

  bv_interval_addmul_u(intv, &aux, c, &buffers);
  printf("result: ");
  show_interval_unsigned(stdout, intv);
  printf("\n\n");

  delete_bv_interval(&aux);
  delete_bv_aux_buffers(&buffers);
}

static void test_addmul_signed(bv_interval_t *intv, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d, uint32_t *e, uint32_t n) {
  bv_interval_t aux;
  bv_aux_buffers_t buffers;

  assert(bvconst_is_normalized(a, n) && bvconst_is_normalized(b, n) && bvconst_sle(a, b, n));
  assert(bvconst_is_normalized(d, n) && bvconst_is_normalized(e, n) && bvconst_sle(d, e, n));
  assert(bvconst_is_normalized(c, n));

  init_bv_aux_buffers(&buffers);
  init_bv_interval(&aux);
  bv_interval_set_s(&aux, d, e, n); // aux := [d, e]
  bv_interval_set_s(intv, a, b, n); // intv := [a, b]

  printf("--- Test addmul signed ---\n");
  printf("a =  ");
  show_interval_signed(stdout, intv);
  printf("\nb =  ");
  show_interval_signed(stdout, &aux);
  printf("\nc =  ");
  bvconst_print(stdout, c, n);
  printf("\n");
  fflush(stdout);

  bv_interval_addmul_s(intv, &aux, c, &buffers);
  printf("result: ");
  show_interval_signed(stdout, intv);
  printf("\n\n");

  delete_bv_interval(&aux);
  delete_bv_aux_buffers(&buffers);
}




/*
 * CHECK RESULTS
 */

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
 * Report an error then exit when check fails
 * - u = input in an interval [a, b]
 * - v = input in an interval [c, d]
 * - w = build from u and v (depending on the test) that should be in intv and was not
 */
static void report_error(uint32_t *u, uint32_t *v, uint32_t *w, uint32_t n) {
  fprintf(stderr, "FAILED\n");
  fprintf(stderr, "u = ");
  bvconst_print(stderr, u, n);
  fprintf(stderr, "\n");
  fprintf(stderr, "v = ");
  bvconst_print(stderr, v, n);
  fprintf(stderr, "\n");
  fprintf(stderr, "w = ");
  bvconst_print(stderr, w, n);
  fprintf(stderr, "\n");
  fprintf(stderr, "w not in the computed interval\n");
  fflush(stderr);
  exit(1);
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
	    report_error(u, v, buffer.data, n);
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
	    report_error(u, v, buffer.data, n);
	  }
	}
      }
    }
  }

  delete_bvconstant(&buffer);
}


/*
 * Check the result of diff:
 * - go through all pairs of constants u and v in array data
 * - if u belongs to [a, b] and v belongs to [c, d], then check whether u - v belongs to a
 * - n = number of bits in all vectors
 * - m = size of the data array
 */
static void check_diff_unsigned(bv_interval_t *intv, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d, uint32_t n,
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
	  bvconst_sub(buffer.data, w, v);
	  bvconst_normalize(buffer.data, n); // buffer := u - v modulo 2^n
	  if (! member_u(buffer.data, intv)) {
	    report_error(u, v, buffer.data, n);
	  }
	}
      }
    }
  }

  delete_bvconstant(&buffer);
}


static void check_diff_signed(bv_interval_t *intv, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d, uint32_t n,
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
	  bvconst_sub(buffer.data, w, v);
	  bvconst_normalize(buffer.data, n); // buffer := u - v modulo 2^n
	  if (! member_s(buffer.data, intv)) {
	    report_error(u, v, buffer.data, n);
	  }
	}
      }
    }
  }

  delete_bvconstant(&buffer);
}



/*
 * Check addmul: [a, b] + c * [d, e]
 */
static void check_addmul_unsigned(bv_interval_t *intv, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d, uint32_t *e, uint32_t n,
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
	if (in_interval_u(v, d, e, n)) {
	  // u is in [a, b] and v is in [d, e]
	  bvconst_set(buffer.data, w, u);
	  bvconst_addmul(buffer.data, w, c, v);
	  bvconst_normalize(buffer.data, n); // buffer := u + c * v modulo 2^n
	  if (! member_u(buffer.data, intv)) {
	    report_error(u, v, buffer.data, n);
	  }
	}
      }
    }
  }

  delete_bvconstant(&buffer);
}


static void check_addmul_signed(bv_interval_t *intv, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d, uint32_t *e, uint32_t n,
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
	if (in_interval_s(v, d, e, n)) {
	  // u is in [a, b] and v is in [d, e]
	  bvconst_set(buffer.data, w, u);
	  bvconst_addmul(buffer.data, w, c, v);
	  bvconst_normalize(buffer.data, n); // buffer := u + c * v modulo 2^n
	  if (! member_s(buffer.data, intv)) {
	    report_error(u, v, buffer.data, n);
	  }
	}
      }
    }
  }

  delete_bvconstant(&buffer);
}



/*
 * TESTS
 */

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
 * Test difference between [a, b] and all pairs of vectors in array data
 */
static void test_diff_unsigned_all_pairs(uint32_t *a, uint32_t *b, uint32_t n, uint32_t **data, uint32_t m) {
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
      test_diff_unsigned(&test, a, b, u, v, n);
      check_diff_unsigned(&test, a, b, u, v, n, data, m);
    }
  }
  delete_bv_interval(&test);
}


static void test_diff_signed_all_pairs(uint32_t *a, uint32_t *b, uint32_t n, uint32_t **data, uint32_t m) {
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
      test_diff_signed(&test, a, b, u, v, n);
      check_diff_signed(&test, a, b, u, v, n, data, m);
    }
  }
  delete_bv_interval(&test);

}



/*
 * Test addmul [a, b] + c * [d, e] for all pairs [d, e] in array data
 */
static void test_addmul_unsigned_all_pairs(uint32_t *a, uint32_t *b, uint32_t *c, uint32_t n, uint32_t **data, uint32_t m) {
  bv_interval_t test;
  uint32_t *u, *v, *w;
  uint32_t i, j;

  init_bv_interval(&test);
  for (i=0; i<m; i++) {
    for (j=i; j<m; j++) {
      u = data[i];
      v = data[j];
      if (bvconst_gt(u, v, n)) {
	w = u;  u = v; v = w;
      }
      test_addmul_unsigned(&test, a, b, c, u, v, n);
      check_addmul_unsigned(&test, a, b, c, u, v, n, data, m);
    }
  }
  delete_bv_interval(&test);
}


static void test_addmul_signed_all_pairs(uint32_t *a, uint32_t *b, uint32_t *c, uint32_t n, uint32_t **data, uint32_t m) {
  bv_interval_t test;
  uint32_t *u, *v, *w;
  uint32_t i, j;

  init_bv_interval(&test);
  for (i=0; i<m; i++) {
    for (j=i; j<m; j++) {
      u = data[i];
      v = data[j];
      if (bvconst_sgt(u, v, n)) {
	w = u;  u = v; v = w;
      }
      test_addmul_signed(&test, a, b, c, u, v, n);
      check_addmul_signed(&test, a, b, c, u, v, n, data, m);
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
 * Full diff test
 */
static void full_test_diff_unsigned(uint32_t **data, uint32_t m, uint32_t n) {
  uint32_t *u, *v, *w;
  uint32_t i, j;

  printf("\n*** FULL TEST DIFF UNSIGNED (bitsize = %"PRIu32") ***\n\n", n);

  for (i=0; i<m; i++) {
    for (j=i; j<m; j++) {
      u = data[i];
      v = data[j];
      if (bvconst_gt(u, v, n)) {
	// swap
	w = u; u = v; v = w;
      }
      test_diff_unsigned_all_pairs(u, v, n, data, m);
    }
  }
}


static void full_test_diff_signed(uint32_t **data, uint32_t m, uint32_t n) {
  uint32_t *u, *v, *w;
  uint32_t i, j;

  printf("\n*** FULL TEST DIFF SIGNED (bitsize = %"PRIu32") ***\n\n", n);

  for (i=0; i<m; i++) {
    for (j=i; j<m; j++) {
      u = data[i];
      v = data[j];
      if (bvconst_sgt(u, v, n)) {
	// swap
	w = u; u = v; v = w;
      }
      test_diff_signed_all_pairs(u, v, n, data, m);
    }
  }
}




/*
 * Random tests:
 * - data = input array where vectors are sampled (also used in check and allpairs)
 * - m = size of the data array
 * - n = bitsize
 * - nt = number of tests
 */
static void random_test_sum_unsigned(uint32_t **data, uint32_t m, uint32_t n, uint32_t nt) {
  uint32_t *u, *v, *w;
  uint32_t i, j;

  assert(m > 0);

  printf("\n*** RANDOM TESTS SUM UNSIGNED (bitsize = %"PRIu32") ***\n\n", n);

  while (nt > 0) {
    i = random() % m;
    j = random() % m;;
    u = data[i];
    v = data[j];
    if (bvconst_gt(u, v, n)) {
      w = u; u = v; v = w;
    }
    test_sum_unsigned_all_pairs(u, v, n, data, m);
    nt--;
  }
}


static void random_test_sum_signed(uint32_t **data, uint32_t m, uint32_t n, uint32_t nt) {
  uint32_t *u, *v, *w;
  uint32_t i, j;

  assert(m > 0);

  printf("\n*** RANDOM TESTS SUM SIGNED (bitsize = %"PRIu32") ***\n\n", n);

  while (nt > 0) {
    i = random() % m;
    j = random() % m;;
    u = data[i];
    v = data[j];
    if (bvconst_sgt(u, v, n)) {
      w = u; u = v; v = w;
    }
    test_sum_signed_all_pairs(u, v, n, data, m);
    nt--;
  }
}


static void random_test_diff_unsigned(uint32_t **data, uint32_t m, uint32_t n, uint32_t nt) {
  uint32_t *u, *v, *w;
  uint32_t i, j;

  assert(m > 0);

  printf("\n*** RANDOM TESTS DIFF UNSIGNED (bitsize = %"PRIu32") ***\n\n", n);

  while (nt > 0) {
    i = random() % m;
    j = random() % m;;
    u = data[i];
    v = data[j];
    if (bvconst_gt(u, v, n)) {
      w = u; u = v; v = w;
    }
    test_diff_unsigned_all_pairs(u, v, n, data, m);
    nt--;
  }
}


static void random_test_diff_signed(uint32_t **data, uint32_t m, uint32_t n, uint32_t nt) {
  uint32_t *u, *v, *w;
  uint32_t i, j;

  assert(m > 0);

  printf("\n*** RANDOM TESTS DIFF SIGNED (bitsize = %"PRIu32") ***\n\n", n);

  while (nt > 0) {
    i = random() % m;
    j = random() % m;;
    u = data[i];
    v = data[j];
    if (bvconst_sgt(u, v, n)) {
      w = u; u = v; v = w;
    }
    test_diff_signed_all_pairs(u, v, n, data, m);
    nt--;
  }
}


static void random_test_addmul_unsigned(uint32_t **data, uint32_t m, uint32_t n, uint32_t nt) {
  uint32_t *u, *v, *w;
  uint32_t i, j, k;

  assert(m > 0);

  printf("\n*** RANDOM TESTS ADDMULL UNSIGNED (bitsize = %"PRIu32") ***\n\n", n);

  while (nt > 0) {
    i = random() % m;
    j = random() % m;;
    u = data[i];
    v = data[j];
    if (bvconst_gt(u, v, n)) {
      w = u; u = v; v = w;
    }
    k = random() % m;
    w = data[k];
    test_addmul_unsigned_all_pairs(u, v, w, n, data, m);
    nt--;
  }
}


static void random_test_addmul_signed(uint32_t **data, uint32_t m, uint32_t n, uint32_t nt) {
  uint32_t *u, *v, *w;
  uint32_t i, j, k;

  assert(m > 0);

  printf("\n*** RANDOM TESTS ADDMULL SIGNED (bitsize = %"PRIu32") ***\n\n", n);

  while (nt > 0) {
    i = random() % m;
    j = random() % m;;
    u = data[i];
    v = data[j];
    if (bvconst_sgt(u, v, n)) {
      w = u; u = v; v = w;
    }
    k = random() % m;
    w = data[k];
    test_addmul_signed_all_pairs(u, v, w, n, data, m);
    nt--;
  }
}








/*
 * Basic tests
 */
int main(void) {
  uint32_t *b[50];

  init_bvconstants();

  init_bvconst_array(b, 20, 10);
  random_test_addmul_unsigned(b, 20, 10, 100);
  random_test_addmul_signed(b, 20, 10, 100);
  full_test_sum_unsigned(b, 20, 10);
  full_test_sum_signed(b, 20, 10);
  full_test_diff_unsigned(b, 20, 10);
  full_test_diff_signed(b, 20, 10);
  delete_bvconst_array(b, 20, 10);

  init_bvconst_array(b, 50, 95);
  random_test_sum_unsigned(b, 50, 95, 100);
  random_test_sum_signed(b, 50, 95, 100);
  random_test_diff_unsigned(b, 50, 95, 100);
  random_test_diff_signed(b, 50, 95, 100);
  random_test_addmul_unsigned(b, 50, 95, 100);
  random_test_addmul_signed(b, 50, 95, 100);
  delete_bvconst_array(b, 50, 95);

  init_bvconst_array(b, 50, 96);
  random_test_sum_unsigned(b, 50, 96, 100);
  random_test_sum_signed(b, 50, 96, 100);
  random_test_diff_unsigned(b, 50, 96, 100);
  random_test_diff_signed(b, 50, 96, 100);
  random_test_addmul_unsigned(b, 50, 96, 100);
  random_test_addmul_signed(b, 50, 96, 100);
  delete_bvconst_array(b, 50, 96);

  init_bvconst_array(b, 50, 97);
  random_test_sum_unsigned(b, 50, 97, 100);
  random_test_sum_signed(b, 50, 97, 100);
  random_test_diff_unsigned(b, 50, 97, 100);
  random_test_diff_signed(b, 50, 97, 100);
  random_test_addmul_unsigned(b, 50, 97, 100);
  random_test_addmul_signed(b, 50, 97, 100);
  delete_bvconst_array(b, 50, 97);

  cleanup_bvconstants();

  return 0;
}
