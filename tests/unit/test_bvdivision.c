/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * CLAUSAL ENCODING OF BIT-VECTOR CONSTRAINTS
 */

#include <stdbool.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>

#include "solvers/cdcl/smt_core.h"
#include "solvers/bv/bit_blaster.h"
#include "solvers/cdcl/smt_core_printer.h"


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
 * Descriptors for the null theory
 */
static void do_nothing(void *t) {
}

static void null_backtrack(void *t, uint32_t back_level) {
}

static fcheck_code_t null_final_check(void *t) {
  return FCHECK_SAT;
}

static th_ctrl_interface_t null_theory_ctrl = {
  do_nothing,       // start_internalization
  do_nothing,       // start_search
  NULL,             // propagate
  null_final_check, // final_check
  do_nothing,       // increase_dlevel
  null_backtrack,   // backtrack
  do_nothing,       // push
  do_nothing,       // pop
  do_nothing,       // reset
  do_nothing,       // clear
};

static th_smt_interface_t null_theory_smt = {
  NULL,            // assert_atom
  NULL,            // expand explanation
  NULL,            // select polarity
  NULL,            // delete_atom
  NULL,            // end_deletion
};



/*
 * Global variables
 */
static smt_core_t solver;
static remap_table_t remap;
static bit_blaster_t blaster;


/*
 * Initialize all
 */
static void init(void) {
  init_smt_core(&solver, 0, NULL, &null_theory_ctrl, &null_theory_smt, SMT_MODE_BASIC);
  init_remap_table(&remap);
  init_bit_blaster(&blaster, &solver, &remap);
}

/*
 * Delete all
 */
static void cleanup(void) {
  delete_bit_blaster(&blaster);
  delete_remap_table(&remap);
  delete_smt_core(&solver);
}


/*
 * Create a new literal
 */
static inline literal_t fresh_lit(void) {
  return pos_lit(bit_blaster_new_var(&blaster));
}



/*
 * Convert x to an n-bit literal array a[0 .. n-1]
 * - if n is more than 32, the high-order bits are all 0 (false_literal)
 */
static void uint32_to_litarray(uint32_t x, uint32_t n, literal_t *a) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if ((x & 1) == 0) {
      a[i] = false_literal;
    } else {
      a[i] = true_literal;
    }
    x >>= 1;
  }
}


/*
 * Print a[0 .. n-1] as an unsigned integer
 * - n must be no more than 32
 */
static void print_litarray_as_uint32(uint32_t n, literal_t *a) {
  uint32_t i, x;

  assert(n <= 32);

  x = 0;
  i = n;
  while (i > 0) {
    i --;
    x <<= 1;
    if (a[i] == true_literal) {
      x ++;
    } else if (a[i] != false_literal) {
      printf("not an integer");
      return;
    }
  }

  printf("%"PRIu32, x);
}


/*
 * Print a[0 .. n-1] as a signed integer
 * - n must be positive and no more than 32
 */
static void print_litarray_as_int32(uint32_t n, literal_t *a) {
  uint32_t i;
  int32_t x;

  assert(0 < n && n <= 32);

  x = 0;
  i = n-1;
  while (i > 0) {
    i --;
    x <<= 1;
    if (a[i] == true_literal) {
      x ++;
    } else if (a[i] != false_literal) {
      printf("not an integer");
      return;
    }
  }

  if (a[n-1] == true_literal) {
    x -= (1 << (n-1));
  } else if (a[n-1] != false_literal) {
    printf("not an integer");
    return;
  }

  printf("%"PRId32, x);
}



/*
 * Print array as a vector
 */
static void print_bitvector(uint32_t n, literal_t *a) {
  uint32_t i;

  printf("[");
  if (n>0) {
    print_literal(stdout, a[0]);
    for (i=1; i<n; i++) {
      printf(" ");
      print_literal(stdout, a[i]);
    }
  }
  printf("]");
}




/*
 * Print an array of pseudo-literals
 */

/*
 * Replace l by its value if it's true or false
 */
static literal_t eval_literal(literal_t l) {
  switch (literal_base_value(&solver, l)) {
  case VAL_FALSE:
    return false_literal;
  case VAL_TRUE:
    return true_literal;
  case VAL_UNDEF_FALSE:
  case VAL_UNDEF_TRUE:
  default:
    return l;
  }
}

/*
 * Copy the assignment of u[0 ... n-1] into a[0 ... n-1]
 */
static void pseudo_convert(uint32_t n, literal_t *u, literal_t *a) {
  uint32_t i;

  for (i=0; i<n; i++) {
    a[i] = eval_literal(remap_table_find(&remap, u[i]));
  }
}


/*
 * Print u[0 .. n-1] as an unsigned integer
 * - n must be no more than 32
 */
static void print_pseudo_vector_as_uint32(uint32_t n, literal_t *u) {
  literal_t a[n];

  pseudo_convert(n, u, a);
  print_litarray_as_uint32(n, a);
}


/*
 * Print u[0 .. n-1] as a signed integer
 * - n must be no more than 32
 */
static void print_pseudo_vector_as_int32(uint32_t n, literal_t *u) {
  literal_t a[n];

  pseudo_convert(n, u, a);
  print_litarray_as_int32(n, a);
}


/*
 * Print u[0 .. n-1] as an array of literals
 * - n must be no more than 32
 */
static void print_pseudo_vector(uint32_t n, literal_t *u) {
  literal_t a[n];

  pseudo_convert(n, u, a);
  print_bitvector(n, a);
}





/*
 * RANDOM TESTS
 */

/*
 * Support for random tests
 * - lit = array of 30 literals
 * - used = array of 30 booleans
 */
#define MAX_SAMPLE 30

static literal_t lit[MAX_SAMPLE];
static bool used[MAX_SAMPLE];


/*
 * Create n distinct literals and store them in lit
 */
static void init_random(uint32_t n) {
  uint32_t i;

  assert(2 <= n && n < MAX_SAMPLE);

  lit[0] = true_literal;
  lit[1] = false_literal;
  for (i=2; i<n; i += 2) {
    lit[i] = fresh_lit();
    lit[i+1] = not(lit[i]);
  }

  for (i=0; i<n; i++) {
    used[i] = false;
  }
}


/*
 * Pick a random literal among lit[0 ... n-1]
 */
static literal_t pick(uint32_t n) {
  uint32_t i;

  i = (uint32_t) (random() % n);
  used[i] = true;
  return lit[i];
}


/*
 * Refresh: replace all used lit by a new literal
 * - lit[2i] and lit[2i+1] are refreshed in pairs
 */
static void refresh_random(uint32_t n) {
  uint32_t i;

  assert(2 <= n && n < MAX_SAMPLE);
  for (i=2; i<n; i += 2) {
    if (used[i] || used[i+1]) {
      lit[i] = fresh_lit();
      lit[i+1] = not(lit[i]);
      used[i] = false;
      used[i+1] = false;
    }
  }
}





/*
 * Test unsigned division of a by b: size n
 */
static void test_udiv(uint32_t n, literal_t *a, literal_t *b) {
  literal_t *q;
  literal_t *r;

  printf("a = ");
  print_bitvector(n, a);
  printf("\n");
  printf("b = ");
  print_bitvector(n, b);
  printf("\n");

  q = remap_table_fresh_array(&remap, n);
  r = remap_table_fresh_array(&remap, n);
  int_array_incref(q);
  int_array_incref(r);

  bit_blaster_make_udivision(&blaster, a, b, q, r, n);
  printf("(bvudiv a b) = ");
  print_pseudo_vector(n, q);
  printf("\n(bvurem a b) = ");
  print_pseudo_vector(n, r);
  printf("\n\n");

  remap_table_free_array(q);
  remap_table_free_array(r);
}

// constant input
static void test_udiv_const(uint32_t n, literal_t *a, literal_t *b) {
  literal_t *q;
  literal_t *r;

  q = remap_table_fresh_array(&remap, n);
  r = remap_table_fresh_array(&remap, n);
  int_array_incref(q);
  int_array_incref(r);

  bit_blaster_make_udivision(&blaster, a, b, q, r, n);

  printf("(bvudiv ");
  print_litarray_as_uint32(n, a);
  printf(" " );
  print_litarray_as_uint32(n, b);
  printf(") = ");
  print_pseudo_vector_as_uint32(n, q);
  printf("\n");

  printf("(bvurem ");
  print_litarray_as_uint32(n, a);
  printf(" " );
  print_litarray_as_uint32(n, b);
  printf(") = ");
  print_pseudo_vector_as_uint32(n, r);
  printf("\n");

  remap_table_free_array(q);
  remap_table_free_array(r);
}




/*
 * Test signed division of a by b: size n
 */
static void test_sdiv(uint32_t n, literal_t *a, literal_t *b) {
  literal_t *q;
  literal_t *r;

  printf("a = ");
  print_bitvector(n, a);
  printf("\n");
  printf("b = ");
  print_bitvector(n, b);
  printf("\n");

  q = remap_table_fresh_array(&remap, n);
  r = remap_table_fresh_array(&remap, n);
  int_array_incref(q);
  int_array_incref(r);

  bit_blaster_make_sdivision(&blaster, a, b, q, r, n);
  printf("(bvsdiv a b) = ");
  print_pseudo_vector(n, q);
  printf("\n(bvurem a b) = ");
  print_pseudo_vector(n, r);
  printf("\n\n");

  remap_table_free_array(q);
  remap_table_free_array(r);
}

// constant input
static void test_sdiv_const(uint32_t n, literal_t *a, literal_t *b) {
  literal_t *q;
  literal_t *r;

  q = remap_table_fresh_array(&remap, n);
  r = remap_table_fresh_array(&remap, n);
  int_array_incref(q);
  int_array_incref(r);

  bit_blaster_make_sdivision(&blaster, a, b, q, r, n);

  printf("(bvsdiv ");
  print_litarray_as_int32(n, a);
  printf(" " );
  print_litarray_as_int32(n, b);
  printf(") = ");
  print_pseudo_vector_as_int32(n, q);
  printf("\n");

  printf("(bvsrem ");
  print_litarray_as_int32(n, a);
  printf(" " );
  print_litarray_as_int32(n, b);
  printf(") = ");
  print_pseudo_vector_as_int32(n, r);
  printf("\n");

  remap_table_free_array(q);
  remap_table_free_array(r);
}


/*
 * Test smod of a by b: size n
 */
static void test_smod(uint32_t n, literal_t *a, literal_t *b) {
  literal_t *r;

  printf("a = ");
  print_bitvector(n, a);
  printf("\n");
  printf("b = ");
  print_bitvector(n, b);
  printf("\n");

  r = remap_table_fresh_array(&remap, n);
  int_array_incref(r);

  bit_blaster_make_smod(&blaster, a, b, r, n);
  printf("(bsmod a b) = ");
  print_pseudo_vector(n, r);
  printf("\n\n");

  remap_table_free_array(r);
}

// constant input
static void test_smod_const(uint32_t n, literal_t *a, literal_t *b) {
  literal_t *r;

  r = remap_table_fresh_array(&remap, n);
  int_array_incref(r);

  bit_blaster_make_smod(&blaster, a, b, r, n);

  printf("(bvsmod ");
  print_litarray_as_int32(n, a);
  printf(" ");
  print_litarray_as_int32(n, b);
  printf(") = ");
  print_pseudo_vector_as_int32(n, r);
  printf("\n");

  remap_table_free_array(r);
}



/*
 * Basic test: two 4-bit input
 */
static void base_test4(void (*f)(uint32_t, literal_t *, literal_t *)) {
  literal_t a[4];
  literal_t b[4];
  uint32_t i;

  for (i=0; i<4; i++) {
    a[i] = false_literal;
    b[i] = fresh_lit();
  }
  f(4, a, b);

  for (i=0; i<4; i++) {
    a[i] = fresh_lit();
    b[i] = false_literal;
  }
  f(4, a, b);

  for (i=0; i<4; i++) {
    a[i] = true_literal;
    b[i] = fresh_lit();
  }
  f(4, a, b);

  for (i=0; i<4; i++) {
    a[i] = fresh_lit();
    b[i] = true_literal;
  }
  f(4, a, b);

  for (i=0; i<4; i++) {
    a[i] = fresh_lit();
    b[i] = a[i];
  }
  f(4, a, b);

  for (i=0; i<4; i++) {
    a[i] = false_literal;
    b[i] = fresh_lit();
  }
  a[0] = true_literal;
  f(4, a, b);

  for (i=0; i<4; i++) {
    a[i] = fresh_lit();
    b[i] = false_literal;
  }
  b[0] = true_literal;
  f(4, a, b);

  for (i=0; i<4; i++) {
    a[i] = false_literal;
    b[i] = fresh_lit();
  }
  a[1] = true_literal;
  f(4, a, b);

  for (i=0; i<4; i++) {
    a[i] = fresh_lit();
    b[i] = false_literal;
  }
  b[1] = true_literal;
  f(4, a, b);

  for (i=0; i<4; i++) {
    a[i] = false_literal;
    b[i] = fresh_lit();
  }
  a[2] = true_literal;
  f(4, a, b);

  for (i=0; i<4; i++) {
    a[i] = fresh_lit();
    b[i] = false_literal;
  }
  b[2] = true_literal;
  f(4, a, b);

  for (i=0; i<4; i++) {
    a[i] = false_literal;
    b[i] = fresh_lit();
  }
  a[3] = true_literal;
  f(4, a, b);

  for (i=0; i<4; i++) {
    a[i] = fresh_lit();
    b[i] = false_literal;
  }
  b[3] = true_literal;
  f(4, a, b);
}



/*
 * Truth-table tests: all 4-input constant vectors
 */
static void truth_table_test4(void (*f)(uint32_t, literal_t *, literal_t *)) {
  literal_t a[4];
  literal_t b[4];
  uint32_t x, y;

  printf("Size 4\n");
  for (x=0; x<16; x++) {
    uint32_to_litarray(x, 4, a);
    for (y=0; y<16; y++) {
      uint32_to_litarray(y, 4, b);
      f(4, a, b);
    }
  }
  printf("\n");
}

/*
 * Random tests with two input vectors of 4 bits: n = number of tests
 */
static void random_tests4(uint32_t n, void (*f)(uint32_t, literal_t *, literal_t *)) {
  literal_t a[4];
  literal_t b[4];
  uint32_t i;

  printf("Size 4:\n");
  init_random(14);
  while (n > 0) {
    for (i=0; i<4; i++) {
      a[i] = pick(14);
      b[i] = pick(14);
    }
    f(4, a, b);
    refresh_random(14);
    n --;
  }
  printf("\n");
}





/*
 * Tests
 */
static void all_udiv_tests(void) {
  printf("\n"
	 "******************\n"
	 "*  BVUDIV TESTS  *\n"
	 "******************\n\n");

  init();
  truth_table_test4(test_udiv_const);
  base_test4(test_udiv);
  random_tests4(100, test_udiv);
  cleanup();
}


static void all_sdiv_tests(void) {
  printf("\n"
	 "******************\n"
	 "*  BVSDIV TESTS  *\n"
	 "******************\n\n");

  init();
  truth_table_test4(test_sdiv_const);
  base_test4(test_sdiv);
  random_tests4(100, test_sdiv);
  cleanup();
}


static void all_smod_tests(void) {
  printf("\n"
	 "******************\n"
	 "*  BVSMOD TESTS  *\n"
	 "******************\n\n");

  init();
  truth_table_test4(test_smod_const);
  base_test4(test_smod);
  random_tests4(100, test_smod);
  cleanup();
}


int main(void) {
  all_udiv_tests();
  all_sdiv_tests();
  all_smod_tests();

  return 0;
}
