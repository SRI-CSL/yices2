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
  do_nothing,       // reset
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
 * Initialize both
 */
static void init(void) {
  init_smt_core(&solver, 0, NULL, &null_theory_ctrl, &null_theory_smt, SMT_MODE_BASIC);
  init_remap_table(&remap);
  init_bit_blaster(&blaster, &solver, &remap);
}

/*
 * Delete both
 */
static void cleanup(void) {
  delete_bit_blaster(&blaster);
  delete_remap_table(&remap);
  delete_smt_core(&solver);
}


/*
 * Create a new literal
 */
static literal_t fresh_lit(void) {
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
 * Test comparators with two constant vectors of size n >= 0
 */
static void test_bveq_const(uint32_t n, literal_t *a, literal_t *b) {
  literal_t l;

  printf("(bveq ");
  print_litarray_as_uint32(n, a);
  printf(" ");
  print_litarray_as_uint32(n, b);
  printf(") == ");
  fflush(stdout);
  l = bit_blaster_make_bveq(&blaster, a, b, n);
  print_literal(stdout, l);
  printf("\n");
}


static void test_bvuge_const(uint32_t n, literal_t *a, literal_t *b) {
  literal_t l;

  printf("(bvuge ");
  print_litarray_as_uint32(n, a);
  printf(" ");
  print_litarray_as_uint32(n, b);
  printf(") == ");
  fflush(stdout);
  l = bit_blaster_make_bvuge(&blaster, a, b, n);
  print_literal(stdout, l);
  printf("\n");
}


static void test_bvsge_const(uint32_t n, literal_t *a, literal_t *b) {
  literal_t l;

  printf("(bvsge ");
  print_litarray_as_int32(n, a);
  printf(" ");
  print_litarray_as_int32(n, b);
  printf(") == ");
  fflush(stdout);
  l = bit_blaster_make_bvsge(&blaster, a, b, n);
  print_literal(stdout, l);
  printf("\n");
}





/*
 * Test comparators:
 * - two input vector of size n >= 0
 */
static void test_bveq(uint32_t n, literal_t *a, literal_t *b) {
  literal_t l;

  printf("--- test bveq ---\n");
  printf("a = ");
  print_bitvector(n, a);
  printf("\n");
  printf("b = ");
  print_bitvector(n, b);
  printf("\n");

  l = bit_blaster_make_bveq(&blaster, a, b, n);
  printf("(bveq a b) == ");
  print_literal(stdout, l);
  printf("\n");
}

static void test_bvuge(uint32_t n, literal_t *a, literal_t *b) {
  literal_t l;

  printf("--- test bvuge ---\n");
  printf("a = ");
  print_bitvector(n, a);
  printf("\n");
  printf("b = ");
  print_bitvector(n, b);
  printf("\n");

  l = bit_blaster_make_bvuge(&blaster, a, b, n);
  printf("(bvuge a b) == ");
  print_literal(stdout, l);
  printf("\n");
}

static void test_bvsge(uint32_t n, literal_t *a, literal_t *b) {
  literal_t l;

  printf("--- test bvsge ---\n");
  printf("a = ");
  print_bitvector(n, a);
  printf("\n");
  printf("b = ");
  print_bitvector(n, b);
  printf("\n");

  l = bit_blaster_make_bvsge(&blaster, a, b, n);
  printf("(bvsge a b) == ");
  print_literal(stdout, l);
  printf("\n");
}






/*
 * Exhaustive tests for vectors of small dimensions
 */
static void test_size0(void (*f)(uint32_t, literal_t *, literal_t *)) {
  printf("Size 0\n");
  f(0, NULL, NULL);
  printf("\n");
}

static void test_size1(void (*f)(uint32_t, literal_t *, literal_t *)) {
  literal_t a[1];
  literal_t b[1];

  printf("Size 1\n");
  a[0] = false_literal;
  b[0] = false_literal;
  f(1, a, b);
  a[0] = false_literal;
  b[0] = true_literal;
  f(1, a, b);
  a[0] = true_literal;
  b[0] = false_literal;
  f(1, a, b);
  a[0] = true_literal;
  b[0] = true_literal;
  f(1, a, b);

  a[0] = fresh_lit();
  b[0] = false_literal;
  f(1, a, b);
  a[0] = fresh_lit();
  b[0] = true_literal;
  f(1, a, b);
  a[0] = false_literal;
  b[0] = fresh_lit();
  f(1, a, b);
  a[0] = true_literal;
  b[0] = fresh_lit();
  f(1, a, b);

  a[0] = fresh_lit();
  b[0] = a[0];
  f(1, a, b);
  a[0] = fresh_lit();
  b[0] = not(a[0]);
  f(1, a, b);

  a[0] = fresh_lit();
  b[0] = fresh_lit();
  f(1, a, b);

  printf("\n");
}



/*
 * Basic tests
 */
static void base_test4(void (*f)(uint32_t, literal_t *, literal_t *)) {
  literal_t a[4];
  literal_t b[4];
  literal_t x;
  uint32_t i;

  printf("Size 4\n");
  x = fresh_lit();
  for (i=0; i<4; i++) {
    a[i] = false_literal;
    b[i] = x;
  }
  f(4, a, b);

  x = fresh_lit();
  for (i=0; i<4; i++) {
    a[i] = x;
    b[i] = false_literal;
  }
  f(4, a, b);

  x = fresh_lit();
  for (i=0; i<4; i++) {
    a[i] = true_literal;
    b[i] = x;
  }
  f(4, a, b);

  x = fresh_lit();
  for (i=0; i<4; i++) {
    a[i] = x;
    b[i] = true_literal;
  }
  f(4, a, b);

  x = fresh_lit();
  for (i=0; i<4; i++) {
    a[i] = x;
    b[i] = x;
  }
  f(4, a, b);

  x = fresh_lit();
  for (i=0; i<4; i++) {
    a[i] = x;
    b[i] = x;
  }
  a[3] = not(x);
  f(4, a, b);

  x = fresh_lit();
  for (i=0; i<4; i++) {
    a[i] = x;
    b[i] = x;
  }
  b[3] = not(x);
  f(4, a, b);

  x = fresh_lit();
  for (i=0; i<4; i++) {
    a[i] = x;
    b[i] = x;
  }
  a[0] = not(x);
  f(4, a, b);

  x = fresh_lit();
  for (i=0; i<4; i++) {
    a[i] = x;
    b[i] = x;
  }
  b[0] = not(x);
  f(4, a, b);


  printf("\n");
}



/*
 * Truth-table tests: all combinations of two 4-input constant vectors
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
 * Random tests with input vectors of size 4: n = number of tests
 */
static void random_tests4(uint32_t n, void (*f)(uint32_t, literal_t *, literal_t *)) {
  literal_t a[4];
  literal_t b[4];
  uint32_t i;

  printf("Size 4:\n");
  init_random(12);
  while (n > 0) {
    for (i=0; i<4; i++) {
      a[i] = pick(12);
      b[i] = pick(12);
    }
    f(4, a, b);
    refresh_random(12);
    n --;
  }
  printf("\n");
}




/*
 * Tests of equality
 */
static void all_bveq_tests(void) {
  printf("\n"
	 "****************\n"
	 "*  BVEQ TESTS  *\n"
	 "****************\n\n");

  init();
  test_size0(test_bveq);
  test_size1(test_bveq);
  truth_table_test4(test_bveq_const);
  base_test4(test_bveq);
  random_tests4(100, test_bveq);
  cleanup();
}


static void all_bvuge_tests(void) {
  printf("\n"
	 "*****************\n"
	 "*  BVUGE TESTS  *\n"
	 "*****************\n\n");

  init();
  test_size0(test_bvuge);
  test_size1(test_bvuge);
  truth_table_test4(test_bvuge_const);
  base_test4(test_bvuge);
  random_tests4(100, test_bvuge);
  cleanup();
}


static void all_bvsge_tests(void) {
  printf("\n"
	 "*****************\n"
	 "*  BVSGE TESTS  *\n"
	 "*****************\n\n");

  init();
  test_size1(test_bvsge);
  truth_table_test4(test_bvsge_const);
  base_test4(test_bvsge);
  random_tests4(100, test_bvsge);
  cleanup();
}



int main(void) {
  all_bveq_tests();
  all_bvuge_tests();
  all_bvsge_tests();

  return 0;
}
