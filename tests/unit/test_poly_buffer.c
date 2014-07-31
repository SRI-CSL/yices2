/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <inttypes.h>

#include "terms/poly_buffer.h"
#include "terms/rationals.h"

#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline int random(void) {
  return rand();
}

#endif


/*
 * Print a monomial (copied from term_printer.c)
 */
static void print_monomial(int32_t v, rational_t *coeff, bool first) {
  bool negative;
  bool abs_one;

  negative = q_is_neg(coeff);

  if (negative) {
    if (first) {
      printf("- ");
    } else {
      printf(" - ");
    }
    abs_one = q_is_minus_one(coeff);
  } else {
    if (! first) {
      printf(" + ");
    }
    abs_one = q_is_one(coeff);
  }

  if (v == const_idx) {
    q_print_abs(stdout, coeff);
  } else {
    if (! abs_one) {
      q_print_abs(stdout, coeff);
      printf(" * ");
    }
    printf("x!%"PRId32, v);
  }
}


/*
 * Print monomial array a
 * - n = number of monomials
 */
static void print_polynomial(monomial_t *a, uint32_t n) {
  uint32_t i;

  if (n == 0) {
    printf("0");
  } else {
    for (i=0; i<n; i++) {
      print_monomial(a[i].var, &a[i].coeff, i == 0);
    }
  }
}


/*
 * Print the content of a poly_buffer b
 */
static void print_poly_buffer_details(poly_buffer_t *b) {
  int32_t i, n;

  printf("poly buffer %p\n", b);
  printf("  i_size = %"PRIu32"\n", b->i_size);
  printf("  m_size = %"PRIu32"\n", b->m_size);
  printf("  nterms = %"PRIu32"\n", b->nterms);
  printf("  poly: ");
  print_polynomial(b->mono, b->nterms);
  printf("\n");
  n = b->i_size;
  for (i=0; i<n; i++) {
    if (b->index[i] >= 0) {
      printf("  index[x!%"PRId32"] = %"PRId32"\n", i, b->index[i]);
    }
  }
  printf("\n");
}



/*
 * Global buffer
 */
static poly_buffer_t buffer;

// rational numbers
#define MAX_NUMERATOR (INT32_MAX>>1)
#define MIN_NUMERATOR (INT32_MIN>>1)
#define MAX_DENOMINATOR MAX_NUMERATOR

static int32_t num[12] = {
  1, 1, -1, 0, 120, -120, -120, 120, INT32_MAX, INT32_MIN, MIN_NUMERATOR, MAX_NUMERATOR
};

static uint32_t den[12] = {
  1, 10, 200, 72, 400, 999, INT32_MAX, MAX_DENOMINATOR, 1000, 120, 168, MAX_DENOMINATOR + 2
};


/*
 * Assign a random rational to a
 */
static void random_rational(rational_t *a) {
  q_set_int32(a, num[random() % 12], den[random() %12]);
}



/*
 * Tests
 */
int main() {
  rational_t alpha;
  uint32_t n;
  int32_t v;

  init_rationals();
  q_init(&alpha);
  init_poly_buffer(&buffer);

  printf("--- Init ---\n");
  print_poly_buffer_details(&buffer);

  reset_poly_buffer(&buffer);
  printf("--- Reset ---\n");
  print_poly_buffer_details(&buffer);

  normalize_poly_buffer(&buffer);
  printf("--- Normalize ---\n");
  print_poly_buffer_details(&buffer);

  reset_poly_buffer(&buffer);
  printf("--- Reset ---\n");
  print_poly_buffer_details(&buffer);

  random_rational(&alpha);
  poly_buffer_add_monomial(&buffer, 2, &alpha);
  printf("--- Add monomial x!2 * alpha ---\n");
  print_poly_buffer_details(&buffer);

  poly_buffer_add_const(&buffer, &alpha);
  printf("--- Add constant alpha ---\n");
  print_poly_buffer_details(&buffer);

  poly_buffer_add_monomial(&buffer, 1, &alpha);
  printf("--- Add monomial x!1 * alpha ---\n");
  print_poly_buffer_details(&buffer);

  poly_buffer_sub_monomial(&buffer, 2, &alpha);
  printf("--- Sub monomial x!2 * alpha ---\n");
  print_poly_buffer_details(&buffer);

  normalize_poly_buffer(&buffer);
  printf("--- Normalize ---\n");
  print_poly_buffer_details(&buffer);

  reset_poly_buffer(&buffer);
  printf("--- Reset ---\n");
  print_poly_buffer_details(&buffer);

  random_rational(&alpha);
  poly_buffer_sub_monomial(&buffer, 2, &alpha);
  printf("--- Sub monomial x!2 * alpha ---\n");
  print_poly_buffer_details(&buffer);

  poly_buffer_sub_const(&buffer, &alpha);
  printf("--- Sub constant alpha ---\n");
  print_poly_buffer_details(&buffer);

  poly_buffer_add_monomial(&buffer, 1, &alpha);
  printf("--- Add monomial x!1 * alpha ---\n");
  print_poly_buffer_details(&buffer);

  poly_buffer_sub_monomial(&buffer, 2, &alpha);
  printf("--- Sub monomial x!2 * alpha ---\n");
  print_poly_buffer_details(&buffer);

  poly_buffer_add_const(&buffer, &alpha);
  printf("--- Add constant alpha ---\n");
  print_poly_buffer_details(&buffer);

  poly_buffer_add_var(&buffer, 3);
  printf("--- Add var x!3 ---\n");
  print_poly_buffer_details(&buffer);

  poly_buffer_sub_var(&buffer, 3);
  printf("--- Sub var x!3 ---\n");
  print_poly_buffer_details(&buffer);

  normalize_poly_buffer(&buffer);
  printf("--- Normalize ---\n");
  print_poly_buffer_details(&buffer);

  reset_poly_buffer(&buffer);
  for (n=0; n<400; n++) {
    v = random() % 200;
    random_rational(&alpha);
    poly_buffer_add_monomial(&buffer, v, &alpha);
  }
  printf("--- 400 random monomials ---\n");
  print_poly_buffer_details(&buffer);

  normalize_poly_buffer(&buffer);
  printf("--- Normalize ---\n");
  print_poly_buffer_details(&buffer);


  delete_poly_buffer(&buffer);
  q_clear(&alpha);
  cleanup_rationals();

  return 0;
}
