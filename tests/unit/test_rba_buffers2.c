/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>

#include "terms/pprod_table.h"
#include "terms/rationals.h"
#include "terms/balanced_arith_buffers.h"



/*
 * Display power products
 */
static void print_varexp_array(FILE *f, varexp_t *a, uint32_t n) {
  uint32_t i, d;

  if (n == 0) {
    fprintf(f, "1");
    return;
  }
  d = a[0].exp;
  fprintf(f, "x_%"PRId32, a[0].var);
  if (d != 1) {
    fprintf(f, "^%"PRIu32, d);
  }
  for (i=1; i<n; i++) {
    d = a[i].exp;
    fprintf(f, " x_%"PRId32, a[i].var);
    if (d != 1) {
      fprintf(f, "^%"PRIu32, d);
    }
  }
}

static void print_pprod0(FILE *f, pprod_t *p) {
  if (pp_is_var(p)) {
    fprintf(f, "x_%"PRId32, var_of_pp(p));
  } else if (pp_is_empty(p)) {
    fprintf(f, "1");
  } else {
    print_varexp_array(f, p->prod, p->len);
  }
}




/*
 * Print buffer b
 */
static void print_monomial(FILE *f, rational_t *coeff, pprod_t *r, bool first) {
  bool negative;
  bool abs_one;

  negative = q_is_neg(coeff);
  if (negative) {
    if (first) {
      fprintf(f, "- ");
    } else {
      fprintf(f, " - ");
    }
    abs_one = q_is_minus_one(coeff);
  } else {
    if (! first) {
      fprintf(f, " + ");
    }
    abs_one = q_is_one(coeff);
  }

  if (pp_is_empty(r)) {
    q_print_abs(f, coeff);
  } else {
    if (! abs_one) {
      q_print_abs(f, coeff);
      fprintf(f, " ");
    }
    print_pprod0(f, r);
  }

}

// print subtree rooted at x
static void print_rba_tree(FILE *f, rba_buffer_t *b, uint32_t x, bool first) {
  uint32_t i, j;

  if (x != 0) {
    i = b->child[x][0];
    j = b->child[x][1];
    print_rba_tree(f, b, i, first);
    first &= (i == 0);
    print_monomial(f, &b->mono[x].coeff, b->mono[x].prod, first);
    print_rba_tree(f, b, j, false);
  }
}

static void print_rba_buffer(FILE *f, rba_buffer_t *b) {
  if (rba_buffer_is_zero(b)) {
    fprintf(f, "0");
  } else {
    print_rba_tree(f, b, b->root, true);
  }
}



/*
 * Test basic operations
 */
static void test_buffer_pred(char *s, rba_buffer_t *b, bool (*f)(rba_buffer_t *)) {
  printf("  test %s: ", s);
  if (f(b)) {
    printf("yes\n");
  } else {
    printf("no\n");
  }
}

static void test_buffer(rba_buffer_t *b) {
  int32_t x;
  mono_t *m;

  printf("Buffer %p: ", b);
  print_rba_buffer(stdout, b);
  printf("\n");

  test_buffer_pred("is_zero", b, rba_buffer_is_zero);
  test_buffer_pred("is_constant", b, rba_buffer_is_constant);
  test_buffer_pred("is_nonzero", b, rba_buffer_is_nonzero);
  test_buffer_pred("is_pos", b, rba_buffer_is_pos);
  test_buffer_pred("is_neg", b, rba_buffer_is_neg);
  test_buffer_pred("is_nonneg", b, rba_buffer_is_nonneg);
  test_buffer_pred("is_nonpos", b, rba_buffer_is_nonpos);

  printf("  size: %"PRIu32"\n", rba_buffer_num_terms(b));
  printf("  degree: %"PRIu32"\n", rba_buffer_degree(b));
  if (! rba_buffer_is_zero(b)) {
    printf("  main term: ");
    print_pprod0(stdout, rba_buffer_main_term(b));
    printf("\n");
    m = rba_buffer_main_mono(b);
    printf("  main monomial: ");
    q_print(stdout, &m->coeff);
    printf(" * ");
    print_pprod0(stdout, m->prod);
    printf("\n");
  }

  for (x=0; x<5; x++) {
    printf("  degree in x_%"PRId32": %"PRIu32"\n",
	   x, rba_buffer_var_degree(b, x));
  }
  printf("---\n");
}


/*
 * Global variables:
 * - global prod table and store
 */
static pprod_table_t prod_table;


/*
 * Initialize table
 */
static void init_globals(void) {
  init_rationals();
  init_pprod_table(&prod_table, 0);
}

/*
 * Delete table
 */
static void delete_globals(void) {
  delete_pprod_table(&prod_table);
  cleanup_rationals();
}


/*
 * Tests: one buffer
 */
static void test1(void) {
  rba_buffer_t buffer;
  rational_t q0;

  q_init(&q0);
  init_rba_buffer(&buffer, &prod_table);
  printf("Empty buffer\n");
  test_buffer(&buffer);

  printf("x_0 + x_1\n");
  rba_buffer_add_var(&buffer, 0);
  rba_buffer_add_var(&buffer, 1);
  test_buffer(&buffer);

  printf("After reset\n");
  reset_rba_buffer(&buffer);
  test_buffer(&buffer);

  printf("x_2 - x_0\n");
  rba_buffer_add_var(&buffer, 2);
  rba_buffer_sub_var(&buffer, 0);
  test_buffer(&buffer);

  printf("x_2 - x_0 + x_1 + x_0\n");
  reset_rba_buffer(&buffer);
  rba_buffer_add_var(&buffer, 2);
  rba_buffer_sub_var(&buffer, 0);
  rba_buffer_add_var(&buffer, 1);
  rba_buffer_add_var(&buffer, 0);
  test_buffer(&buffer);

  printf("Adding 3\n");
  q_set32(&q0, 3);
  rba_buffer_add_const(&buffer, &q0);
  test_buffer(&buffer);

  printf("Negating\n");
  rba_buffer_negate(&buffer);
  test_buffer(&buffer);

  printf("Negating again\n");
  rba_buffer_negate(&buffer);
  test_buffer(&buffer);

  printf("Multiplying by 2 x_4\n");
  q_set32(&q0, 2);
  rba_buffer_mul_varmono(&buffer, &q0, 4);
  test_buffer(&buffer);

  printf("Multiplying by x_1^2\n");
  rba_buffer_mul_var(&buffer, 1);
  rba_buffer_mul_var(&buffer, 1);
  test_buffer(&buffer);

  printf("Multiplying by 0\n");
  q_clear(&q0);
  rba_buffer_mul_const(&buffer, &q0);
  test_buffer(&buffer);

  printf("x_1 + 1 - x_2\n");
  reset_rba_buffer(&buffer);
  rba_buffer_add_var(&buffer, 1);
  q_set32(&q0, 1);
  rba_buffer_add_const(&buffer, &q0);
  rba_buffer_sub_var(&buffer, 2);
  test_buffer(&buffer);

  printf("Squaring\n");
  rba_buffer_square(&buffer);
  test_buffer(&buffer);

  printf("Squaring\n");
  rba_buffer_square(&buffer);
  test_buffer(&buffer);

  printf("Squaring\n");
  rba_buffer_square(&buffer);
  test_buffer(&buffer);

  q_clear(&q0);
  delete_rba_buffer(&buffer);
}


/*
 * Test2: binary operations
 */

/*
 * Array of buffers for test2
 */
#define NUM_BUFFERS 8
static rba_buffer_t aux[NUM_BUFFERS];

/*
 * Initialize the buffers
 */
static void init_test2(void) {
  rational_t q0;
  uint32_t i;

  q_init(&q0);
  for (i=0; i<8; i++) {
    init_rba_buffer(aux + i, &prod_table);
  }

  rba_buffer_add_var(&aux[0], 3); // x_3

  q_set32(&q0, 2);
  rba_buffer_add_const(&aux[1], &q0); // 2

  rba_buffer_add_var(&aux[2], 1);
  rba_buffer_sub_var(&aux[2], 2); // x_1 - x_2

  rba_buffer_add_var(&aux[3], 0);
  rba_buffer_sub_const(&aux[3], &q0); // x_0 - 2

  rba_buffer_add_pp(&aux[4], pprod_mul(&prod_table, var_pp(1), var_pp(1))); // x_1^2

  rba_buffer_add_var(&aux[5], 0);
  rba_buffer_mul_const(&aux[5], &q0); // 2 * x_0

  rba_buffer_add_varmono(&aux[6], &q0, 1); // 2 * x_1

  rba_buffer_sub_var(&aux[7], 3);
  rba_buffer_sub_var(&aux[7], 3);
  rba_buffer_add_var(&aux[7], 4);

  q_clear(&q0);
}


/*
 * Delete the buffers
 */
static void delete_test2(void) {
  uint32_t i;

  for (i=0; i<8; i++) {
    delete_rba_buffer(aux + i);
  }
}


/*
 * Test binary operations with b1 and b2
 */
static void test_ops(rba_buffer_t *b1, rba_buffer_t *b2) {
  rba_buffer_t b;

  printf("b1: ");
  print_rba_buffer(stdout, b1);
  printf("\nb2: ");
  print_rba_buffer(stdout, b2);
  printf("\n");

  printf("Equality test: ");
  if (rba_buffer_equal(b1, b2)) {
    printf("yes\n");
  } else {
    printf("no\n");
  }

  init_rba_buffer(&b, &prod_table);

  reset_rba_buffer(&b);
  rba_buffer_add_buffer(&b, b1);
  rba_buffer_add_buffer(&b, b2);
  printf("  b1 + b2: ");
  print_rba_buffer(stdout, &b);
  printf("\n");

  reset_rba_buffer(&b);
  rba_buffer_add_buffer(&b, b1);
  rba_buffer_sub_buffer(&b, b2);
  printf("  b1 - b2: ");
  print_rba_buffer(stdout, &b);
  printf("\n");

  reset_rba_buffer(&b);
  rba_buffer_add_buffer(&b, b2);
  rba_buffer_sub_buffer(&b, b1);
  printf("  b2 - b1: ");
  print_rba_buffer(stdout, &b);
  printf("\n");

  reset_rba_buffer(&b);
  rba_buffer_add_buffer(&b, b1);
  rba_buffer_mul_buffer(&b, b2);
  printf("  b1 * b2: ");
  print_rba_buffer(stdout, &b);
  printf("\n");

  reset_rba_buffer(&b);
  rba_buffer_add_buffer(&b, b2);
  rba_buffer_mul_buffer(&b, b1);
  printf("  b2 * b1: ");
  print_rba_buffer(stdout, &b);
  printf("\n");

  reset_rba_buffer(&b);
  rba_buffer_add_buffer_times_buffer(&b, b1, b2);
  printf("  b1 * b2: ");
  print_rba_buffer(stdout, &b);
  printf("\n");

  reset_rba_buffer(&b);
  rba_buffer_sub_buffer_times_buffer(&b, b1, b2);
  printf("- b1 * b2: ");
  print_rba_buffer(stdout, &b);
  printf("\n");

  delete_rba_buffer(&b);

  printf("----\n");
}


/*
 * Test 2:
 */
static void test2(void) {
  uint32_t i, j;

  init_test2();
  for (i=0; i<8; i++) {
    for (j=0; j<8; j++) {
      test_ops(aux + i, aux + j);
    }
  }
  delete_test2();
}


int main() {
  init_globals();
  test1();
  printf("\n\n");
  test2();
  delete_globals();

  return 0;
}
