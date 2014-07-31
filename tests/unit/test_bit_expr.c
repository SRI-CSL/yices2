/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of the XOR/OR graph
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <inttypes.h>

#include "terms/bit_expr.h"
#include "utils/memalloc.h"


#ifdef MINGW

static inline long int random(void) {
  return rand();
}

#endif




/*
 * Truth tables:
 * - for each bit x, tt[x] = truth table for x
 *   fresh[x] = true if x has not been created
 * - this assumes at most 5 variables
 * - ttsize = size of the table
 * - max = largest such that fresh[x] = false
 */
static uint32_t *tt;
static bool *fresh;
static uint32_t ttsize;
static int32_t max;

#define INIT_TT_SIZE 100
#define MAX_TT_SIZE  (UINT32_MAX/sizeof(uint32_t))


/*
 * Global node table
 */
static node_table_t dag;


/*
 * 5 variables
 */
static bit_t va, vb, vc, vd, ve;



/*
 * Initialize arrays tt and fresh
 */
static void init_tt(void) {
  uint32_t i;

  ttsize = INIT_TT_SIZE;
  max = -1;
  tt = (uint32_t *) safe_malloc(INIT_TT_SIZE * sizeof(uint32_t));
  fresh = (bool *) safe_malloc(INIT_TT_SIZE * sizeof(bool));
  for (i=0; i<INIT_TT_SIZE; i++) {
    fresh[i] = true;
  }
}


/*
 * Double the size of both arrays
 */
static void extend_tt(void) {
  uint32_t i, n;

  n = ttsize << 1;
  if (n > MAX_TT_SIZE) {
    out_of_memory();
  }

  tt = (uint32_t *) safe_realloc(tt, n * sizeof(uint32_t));
  fresh = (bool *) safe_realloc(fresh, n * sizeof(bool));
  for (i=ttsize; i<n; i++) {
    fresh[i] = true;
  }

  ttsize = n;
}


/*
 * Delete both arrays
 */
static void delete_tt(void) {
  safe_free(tt);
  safe_free(fresh);
}


/*
 * Check whether x is a new bit (not in the table)
 */
static bool fresh_bit(bit_t x) {
  return x >= ttsize || fresh[x];
}


/*
 * Add bit x and its truth table to tt
 * - vector = the truth table for x
 */
static void record_tt(bit_t x, uint32_t vector) {
  assert(fresh_bit(x));

  // make the tables large enough
  while (x >= ttsize) {
    extend_tt();
  }

  fresh[x] = false;
  tt[x] = vector;
  if (x > max) {
    max = x;
  }
}



/*
 * Print the id of bit x (for header of tt)
 */
static void print_id(bit_t x) {
  node_t v;

  if (x == true_bit) {
    printf("   T   ");
  } else if (x == false_bit) {
    printf("   F   ");
  } else {
    v = node_of_bit(x);
    if (is_variable_node(&dag, v)) {
      if (bit_is_neg(x)) {
	printf("  ~%c   ", 'a' + (char) (v-1));
      } else {
	printf("   %c   ", 'a' + (char) (v-1));
      }
    } else if (v < 10) {
      if (bit_is_neg(x)) {
	printf("  ~p%"PRId32"  ", v);
      } else {
	printf("   p%"PRId32"  ", v);
      }
    } else if (v < 100) {
      if (bit_is_neg(x)) {
	printf(" ~p%"PRId32"  ", v);
      } else {
	printf("  p%"PRId32"  ", v);
      }
    } else {
      if (bit_is_neg(x)) {
	printf(" ~p%"PRId32" ", v);
      } else {
	printf("  p%"PRId32" ", v);
      }
    }
  }
}


/*
 * Print the truth table
 */
static void print_tt(void) {
  uint32_t i, j, n;
  uint32_t mask, b;

  n = ttsize;

  // print headers
  for (i=0; i<n; i++) {
    if (! fresh[i]) {
      print_id(i);
    }
  }
  printf("\n\n");

  // print bits
  mask = 0x1;
  for (j=0; j<32; j++) {
    for (i=0; i<n; i++) {
      if (! fresh[i]) {
	b = ((mask & tt[i]) != 0);
	printf("   %"PRIu32"   ", b);
      }
    }
    printf("\n");
    mask <<= 1;
  }

  printf("\n");
}




/*
 * Initialization:
 * - initialize tt for 100 elements
 * - set the truth tables for true and false
 * - create 5 variables, set the truth tables for
 *   each variable and its negation
 */
static void init(void) {
  uint32_t v;
  bit_t x;

  init_tt();
  init_node_table(&dag, 0);

  record_tt(true_bit, 0xFFFFFFFF);
  record_tt(false_bit, 0x0000000);

  x = node_table_alloc_var(&dag, 0);
  v = 0xFFFF0000;
  record_tt(x, v);
  record_tt(bit_not(x), ~v);
  va = x;

  x = node_table_alloc_var(&dag, 1);
  v = 0xFF00FF00;
  record_tt(x, v);
  record_tt(bit_not(x), ~v);
  vb = x;

  x = node_table_alloc_var(&dag, 2);
  v = 0xF0F0F0F0;
  record_tt(x, v);
  record_tt(bit_not(x), ~v);
  vc = x;

  x = node_table_alloc_var(&dag, 3);
  v = 0xCCCCCCCC;
  record_tt(x, v);
  record_tt(bit_not(x), ~v);
  vd = x;

  x = node_table_alloc_var(&dag, 4);
  v = 0xAAAAAAAA;
  record_tt(x, v);
  record_tt(bit_not(x), ~v);
  ve = x;
}


/*
 * Cleanup: delete tables
 */
static void cleanup(void) {
  delete_tt();
  delete_node_table(&dag);
}



/*
 * Compute the truth table for bit x
 * - if x is known, we take it from tt
 * - otherwise, we use the dat
 */
static uint32_t dag_truth_table(bit_t x) {
  node_t v;
  uint32_t left, right, aux;

  if (fresh_bit(x)) {
    v = node_of_bit(x);
    switch (node_kind(&dag, v)) {
    case OR_NODE:
      left = dag_truth_table(left_child_of_node(&dag, v));
      right = dag_truth_table(right_child_of_node(&dag, v));
      aux = left | right;
      break;

    case XOR_NODE:
      left = dag_truth_table(left_child_of_node(&dag, v));
      right = dag_truth_table(right_child_of_node(&dag, v));
      aux = left ^ right;
      break;

    case UNUSED_NODE:
    case CONSTANT_NODE:
    case VARIABLE_NODE:
    default:
      printf("*** BUG: invalid node in DAG ***\n");
      fflush(stdout);
      abort();
    }

    if (bit_is_neg(x)) {
      aux = ~aux;
    }

    return aux;

  } else {
    return tt[x];
  }
}




/*
 * Print id of x, no spacing
 */
static void print_simple_id(bit_t x) {
  node_t v;

  if (x == true_bit) {
    printf("T");
  } else if (x == false_bit) {
    printf("F");
  } else {
    v = node_of_bit(x);
    if (bit_is_neg(x)) {
      printf("~");
    }
    if (is_variable_node(&dag, v)) {
      printf("%c", 'a' + (char) (v-1));
    } else {
      printf("p%"PRId32, v);
    }
  }
}


/*
 * Build z = (or x y) and compare the expected and dag-computed
 * truth values
 * - if they agree, add z and ~z to tt
 */
static void test_or(bit_t x, bit_t y) {
  bit_t z;
  uint32_t v0, v1;

  printf("test: (or ");
  print_simple_id(x);
  printf(" ");
  print_simple_id(y);
  printf("): ");

  assert(! fresh_bit(x) && ! fresh_bit(y));

  //  z = bit_or2(&dag, x, y);
  z = bit_or2simplify(&dag, x, y);
  v0 = dag_truth_table(z);
  v1 = (tt[x] | tt[y]);
  if (v0 == v1) {
    printf("ok\n");
    if (fresh_bit(z)) {
      record_tt(z, v0);
      record_tt(bit_not(z), ~v0);
    }
  } else {
    printf("error\n");
    fflush(stdout);
    abort();
  }
}


/*
 * Build z = (xor x y) and compare the expected and dag-computed
 * truth values
 * - if they agree, add z and ~z to tt
 */
static void test_xor(bit_t x, bit_t y) {
  bit_t z;
  uint32_t v0, v1;

  printf("test: (xor ");
  print_simple_id(x);
  printf(" ");
  print_simple_id(y);
  printf("): ");

  assert(! fresh_bit(x) && ! fresh_bit(y));

  //  z = bit_xor2(&dag, x, y);
  z = bit_xor2simplify(&dag, x, y);
  v0 = dag_truth_table(z);
  v1 = (tt[x] ^ tt[y]);
  if (v0 == v1) {
    printf("ok\n");
    if (fresh_bit(z)) {
      record_tt(z, v0);
      record_tt(bit_not(z), ~v0);
    }
  } else {
    printf("error\n");
    fflush(stdout);
    abort();
  }
}




/*
 * Test all combinations of x and y
 */
static void multi_test(bit_t x, bit_t y) {
  test_or(x, y);
  test_or(bit_not(x), y);
  test_or(x, bit_not(y));
  test_or(bit_not(x), bit_not(y));

  test_or(y, x);
  test_or(y, bit_not(x));
  test_or(bit_not(y), x);
  test_or(bit_not(y), bit_not(x));

  test_xor(x, y);
  test_xor(bit_not(x), y);
  test_xor(x, bit_not(y));
  test_xor(bit_not(x), bit_not(y));

  test_xor(y, x);
  test_xor(bit_not(y), x);
  test_xor(y, bit_not(x));
  test_xor(bit_not(y), bit_not(x));
}


/*
 * Test all pairwise combinations of existing terms
 */
static void test_all_pairs(void) {
  uint32_t n;
  bit_t x, y;

  n = max+1;
  for (x = 0; x<n; x++) {
    if (! fresh[x]) {
      for (y=0; y<n; y++) {
	if (! fresh[y]) {
	  test_or(x, y);
	  test_xor(x, y);
	}
      }
    }
  }
}

/*
 * Select a bit stored in tt
 * - give higher probability to the bits of index < 20
 */
static bit_t random_bit(void) {
  uint32_t n;
  bit_t x;

  n = max + 1;
  if (n > 20) {
    // pick in 0..19 with 25% probability
    if ((random() & 0x8800) == 0) {
      n = 20;
    }
  }

  do {
    x = (bit_t) (random() % n);
  } while (fresh[x]);

  return x;
}


/*
 * A single random test
 * - pick two existing bits x and y
 * - select between OR and XOR randomly
 */
static void random_test(void) {
  bit_t x, y;

  x = random_bit();
  y = random_bit();
  if (random() & 0x8000) {
    test_or(x, y);
  } else {
    test_xor(x, y);
  }
}


/*
 * Random tests
 */
static void random_tests(uint32_t n) {
  while (n > 0) {
    random_test();
    n --;
  }
}


int main(void) {
  init();
  print_tt();
  multi_test(va, vb);
  multi_test(va, vc);
  test_all_pairs();
  random_tests(5000000);
  cleanup();

  return 0;
}
