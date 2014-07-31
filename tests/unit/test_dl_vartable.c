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

#include "solvers/floyd_warshall/dl_vartable.h"

#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline long int random(void) {
  return rand();
}

#endif


/*
 * Print a monomial (copied from term_printer.c)
 * - variables v is converted to vertex id i-1
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
    printf("x!%"PRId32, v-1);
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
static void print_poly_buffer(poly_buffer_t *b) {
  print_polynomial(b->mono, b->nterms);
}


/*
 * Print a triple
 */
static void print_dl_triple(dl_triple_t *t) {
  bool space;

  space = false;
  if (t->target >= 0) {
    printf("x!%"PRId32, t->target);
    space = true;
  }
  if (t->source >= 0) {
    if (space) printf(" ");
    printf("- x!%"PRId32, t->source);
  }


  if (! space) {
    q_print(stdout, &t->constant);
  } else if (q_is_pos(&t->constant)) {
    printf(" + ");
    q_print(stdout, &t->constant);
  } else if (q_is_neg(&t->constant)) {
    printf(" - ");
    q_print_abs(stdout, &t->constant);
  }
}


/*
 * Print table
 */
static void print_dl_vartable(dl_vartable_t *table) {
  uint32_t i, n;

  printf("DL vartable %p\n", table);
  printf("  nvars = %"PRIu32"\n", table->nvars);
  printf("  size = %"PRIu32"\n", table->size);
  n = table->nvars;
  if (n == 0) {
    printf("  empty table\n");
  } else {
    printf("  content:\n");
    for (i=0; i<n; i++) {
      printf("    var[%"PRIu32"]: ", i);
      print_dl_triple(dl_var_triple(table, i));
      printf("\n");
    }
  }
  printf("\n");
}



/*
 * Table of rationals for random tests
 */
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
 * Create a random index between 0 and n-1
 */
static int32_t random_vertex(uint32_t n) {
  assert(n > 0);
  return (int32_t) (random() % n);
}


/*
 * Test hash consing: add a random triple in table
 */
static void test_random_triple(dl_vartable_t *table) {
  dl_triple_t *check;
  dl_triple_t test;
  int32_t x, y;

  test.target = random_vertex(6);
  test.source = random_vertex(6);
  q_init(&test.constant);
  random_rational(&test.constant);
  if (test.target == test.source) {
    test.target = nil_vertex;
    test.source = nil_vertex;
  }

  printf("Test: add triple ");
  print_dl_triple(&test);
  printf("\n");
  x = get_dl_var(table, &test);
  printf(" ---> var = %"PRId32"\n", x);

  check = dl_var_triple(table, x);
  if (check->target == test.target &&
      check->source == test.source &&
      q_eq(&check->constant, &test.constant)) {
    printf("Checking descriptor: OK\n");
  } else {
    printf("BUG: invalid descriptor for var %"PRId32"\n", x);
    fflush(stdout);
    exit(1);
  }

  y = get_dl_var(table, &test);
  if (x == y) {
    printf("Checking hash-consing: OK\n");
  } else {
    printf("BUG: hash-consing fails for var %"PRId32"\n", x);
    fflush(stdout);
    exit(1);
  }

  printf("\n");
  q_clear(&test.constant);
}


/*
 * Test sum of triples for x and y
 */
static void test_sum(dl_vartable_t *table, int32_t x, int32_t y, dl_triple_t *aux) {
  if (sum_dl_vars(table, x, y, aux)) {
    printf("--> result = ");
    print_dl_triple(aux);
    printf("\n");
  } else {
    printf("--> result is not a triple\n");
  }
}


/*
 * Test difference of triples for x and y
 */
static void test_diff(dl_vartable_t *table, int32_t x, int32_t y, dl_triple_t *aux) {
  if (diff_dl_vars(table, x, y, aux)) {
    printf("--> result = ");
    print_dl_triple(aux);
    printf("\n");
  } else {
    printf("--> result is not a triple\n");
  }
}


/*
 * Test sum using a poly buffer
 */
static void test_sum_buffer(dl_vartable_t *table, poly_buffer_t *buffer, int32_t x, int32_t y, dl_triple_t *aux) {
  reset_poly_buffer(buffer);
  add_dl_var_to_buffer(table, buffer, x);
  add_dl_var_to_buffer(table, buffer, y);
  normalize_poly_buffer(buffer);
  printf("--> result = ");
  print_poly_buffer(buffer);
  printf("\n");
  if (convert_poly_buffer_to_dl_triple(buffer, aux)) {
    printf("--> convertible to triple: ");
    print_dl_triple(aux);
    printf("\n");
  } else {
    printf("--> not convertible to a triple\n");
  }
  if (rescale_poly_buffer_to_dl_triple(buffer, aux)) {
    printf("--> convertible by rescaling to triple: ");
    print_dl_triple(aux);
    printf("\n");
  } else {
    printf("--> not convertible to a triple by rescaling\n");
  }
}


static void test_diff_buffer(dl_vartable_t *table, poly_buffer_t *buffer, int32_t x, int32_t y, dl_triple_t *aux) {
  reset_poly_buffer(buffer);
  add_dl_var_to_buffer(table, buffer, x);
  sub_dl_var_from_buffer(table, buffer, y);
  normalize_poly_buffer(buffer);
  printf("--> result = ");
  print_poly_buffer(buffer);
  printf("\n");
  if (convert_poly_buffer_to_dl_triple(buffer, aux)) {
    printf("--> convertible to triple: ");
    print_dl_triple(aux);
    printf("\n");
  } else {
    printf("--> not convertible to a triple\n");
  }
  if (rescale_poly_buffer_to_dl_triple(buffer, aux)) {
    printf("--> convertible by rescaling to triple: ");
    print_dl_triple(aux);
    printf("\n");
  } else {
    printf("--> not convertible to a triple by rescaling\n");
  }
}



/*
 * Test sum and difference of triples
 */
static void test_add_diff(dl_vartable_t *table) {
  uint32_t i, j, n;
  dl_triple_t test;
  dl_triple_t test2;
  poly_buffer_t buffer;

  init_poly_buffer(&buffer);
  q_init(&test.constant);
  q_init(&test2.constant);

  n = table->nvars;
  for (i=0; i<n; i++) {
    for (j=0; j<n; j++) {
      printf("Testing sum: var!%"PRIu32" + var!%"PRIu32":\n", i, j);
      printf("--> var!%"PRIu32" : ", i);
      print_dl_triple(dl_var_triple(table, i));
      printf("\n");
      printf("--> var!%"PRIu32" : ", j);
      print_dl_triple(dl_var_triple(table, j));
      printf("\n");
      test_sum_buffer(table, &buffer, i, j, &test2);
      test_sum(table, i, j, &test);
      printf("\n");

      printf("Testing diff: var!%"PRIu32" - var!%"PRIu32":\n", i, j);
      printf("--> var!%"PRIu32" : ", i);
      print_dl_triple(dl_var_triple(table, i));
      printf("\n");
      printf("--> var!%"PRIu32" : ", j);
      print_dl_triple(dl_var_triple(table, j));
      printf("\n");
      test_diff_buffer(table, &buffer, i, j, &test2);
      test_diff(table, i, j, &test);
      printf("\n");
    }
  }

  q_clear(&test.constant);
  q_clear(&test2.constant);
  delete_poly_buffer(&buffer);
}



/*
 * GLOBAL VARIABLE TABLE
 */
static dl_vartable_t table;

int main() {
  uint32_t i;

  init_rationals();
  init_dl_vartable(&table);
  printf("Initial table\n");
  print_dl_vartable(&table);

  for (i=0; i<10; i++) {
    test_random_triple(&table);
  }
  printf("After 10 additions\n");
  print_dl_vartable(&table);

  test_add_diff(&table);

  printf("Push\n");
  dl_vartable_push(&table);

  for (i=0; i<10; i++) {
    test_random_triple(&table);
  }
  printf("After 10 additions\n");
  print_dl_vartable(&table);

  test_add_diff(&table);

  printf("Push\n");
  dl_vartable_push(&table);

  printf("Pop\n");
  dl_vartable_pop(&table);
  print_dl_vartable(&table);

  printf("Pop\n");
  dl_vartable_pop(&table);
  print_dl_vartable(&table);

  printf("Reset\n");
  reset_dl_vartable(&table);
  print_dl_vartable(&table);

  printf("Push\n");
  dl_vartable_push(&table);
  for (i=0; i<100; i++) {
    test_random_triple(&table);
  }
  printf("After 100 additions\n");
  print_dl_vartable(&table);

  test_add_diff(&table);

  printf("Pop\n");
  dl_vartable_pop(&table);
  print_dl_vartable(&table);

  printf("Reset\n");
  reset_dl_vartable(&table);
  print_dl_vartable(&table);

  delete_dl_vartable(&table);
  cleanup_rationals();

  return 0;
}
