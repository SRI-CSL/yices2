/*
 * TEST BOOLEAN AND BIT-VECTOR API FUNCTIONS
 */

/*
 * Force assert to work even if compiled with debug disabled
 */
#ifdef NDEBUG
# undef NDEBUG
#endif


#include <assert.h>
#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>
#include <gmp.h>

#include "int_vectors.h"
#include "memalloc.h"
#include "bitvectors.h"

#include "rationals.h"
#include "bv64_constants.h"
#include "bv_constants.h"

#include "yices.h"
#include "yices_globals.h"
#include "type_printer.h"
#include "term_printer.h"

#include "stores.h"
#include "threads.h"
#include "threadsafe.h"


/* knobs or dials for the numbers */
#if 0
#define BVNUM 200
#define ITENUM 5000
#define BINUM 6000
#else
#define BVNUM 200
#define ITENUM 200
#define BINUM 200
#endif


/*
 * GLOBAL STORE:
 * - a store for all the types and another one for the terms
 */
static yices_lock_t __all_lock;
static type_store_t __all_types;
static term_store_t __all_terms;


/*
 * Initialize both
 */
static void init_store(void) {
  create_yices_lock(&__all_lock);
  init_type_store(&__all_types);
  init_term_store(&__all_terms);
}


/*
 * Delete both
 */
static void delete_store(void) {
  destroy_yices_lock(&__all_lock);
  delete_type_store(&__all_types);
  delete_term_store(&__all_terms);
}


/*
 * Add term t to both
 * - do nothing if t is already present
 */
static void add_term(term_t t) {
  yices_lock_t *lock = &__yices_globals.lock;

  get_yices_lock(&__all_lock);

  get_yices_lock(lock);

  if (! term_store_contains_term(&__all_terms, t)) {
    term_store_add_term(&__all_terms, t);
    type_store_add_term(&__all_types, t);
  }

  release_yices_lock(lock);

  release_yices_lock(&__all_lock);
  
  
}





/*
 * BASE TYPES
 */
static type_t the_boolean, bv1, bv2, bv12, bv32, bv64, bv65, bv100;

static void init_base_types(void) {
  the_boolean = yices_bool_type();
  bv1 = yices_bv_type(1);
  bv2 = yices_bv_type(2);
  bv12 = yices_bv_type(12);
  bv32 = yices_bv_type(32);
  bv64 = yices_bv_type(64);
  bv65 = yices_bv_type(65);
  bv100 = yices_bv_type(100);
}


/*
 * BASE TERMS
 */

/*
 * Add constants and uninterpreted terms of base types
 */
static void init_base_terms(void) {
  uint32_t x;
  term_t t;

  // boolean terms
  add_term(yices_true());
  add_term(yices_false());
  t = yices_new_uninterpreted_term(the_boolean);
  yices_set_term_name(t, "p0");
  add_term(t);
  add_term(yices_not(t));
  t = yices_new_uninterpreted_term(the_boolean);
  yices_set_term_name(t, "p1");
  add_term(t);
  add_term(yices_not(t));
  t = yices_new_uninterpreted_term(the_boolean);
  yices_set_term_name(t, "p2");
  add_term(t);
  add_term(yices_not(t));
  t = yices_new_uninterpreted_term(the_boolean);
  yices_set_term_name(t, "p3");
  add_term(t);
  add_term(yices_not(t));
  t = yices_new_uninterpreted_term(the_boolean);
  yices_set_term_name(t, "p4");
  add_term(t);
  add_term(yices_not(t));


  // bitvector constants
  add_term(yices_bvconst_zero(1));
  add_term(yices_bvconst_one(1));

  add_term(yices_bvconst_zero(2));
  add_term(yices_bvconst_one(2));
  add_term(yices_bvconst_uint32(2, 2));
  add_term(yices_bvconst_minus_one(2));

  add_term(yices_bvconst_zero(12));
  add_term(yices_bvconst_zero(32));
  add_term(yices_bvconst_zero(64));
  add_term(yices_bvconst_zero(65));
  add_term(yices_bvconst_zero(100));

  add_term(yices_bvconst_one(12));
  add_term(yices_bvconst_one(32));
  add_term(yices_bvconst_one(64));
  add_term(yices_bvconst_one(65));
  add_term(yices_bvconst_one(100));

  add_term(yices_bvconst_minus_one(12));
  add_term(yices_bvconst_minus_one(32));
  add_term(yices_bvconst_minus_one(64));
  add_term(yices_bvconst_minus_one(65));
  add_term(yices_bvconst_minus_one(100));

  // more random constants
  x = (uint32_t) random();
  add_term(yices_bvconst_uint32(12, x));
  add_term(yices_bvconst_uint32(32, x));
  add_term(yices_bvconst_uint32(64, x));
  add_term(yices_bvconst_uint32(65, x));
  add_term(yices_bvconst_uint32(100, x));

  x = (uint32_t) random();
  add_term(yices_bvconst_uint32(12, x));
  add_term(yices_bvconst_uint32(32, x));
  add_term(yices_bvconst_uint32(64, x));
  add_term(yices_bvconst_uint32(65, x));
  add_term(yices_bvconst_uint32(100, x));

  x = (uint32_t) random();
  add_term(yices_bvconst_uint32(12, x));
  add_term(yices_bvconst_uint32(32, x));
  add_term(yices_bvconst_uint32(64, x));
  add_term(yices_bvconst_uint32(65, x));
  add_term(yices_bvconst_uint32(100, x));

  // uninterpreted bitvectors
  t = yices_new_uninterpreted_term(bv1);
  yices_set_term_name(t, "a0");
  add_term(t);
  t = yices_new_uninterpreted_term(bv1);
  yices_set_term_name(t, "a1");
  add_term(t);
  t = yices_new_uninterpreted_term(bv1);
  yices_set_term_name(t, "a2");
  add_term(t);
  t = yices_new_uninterpreted_term(bv1);
  yices_set_term_name(t, "a3");
  add_term(t);
  t = yices_new_uninterpreted_term(bv1);
  yices_set_term_name(t, "a4");
  add_term(t);

  t = yices_new_uninterpreted_term(bv2);
  yices_set_term_name(t, "b0");
  add_term(t);
  t = yices_new_uninterpreted_term(bv2);
  yices_set_term_name(t, "b1");
  add_term(t);
  t = yices_new_uninterpreted_term(bv2);
  yices_set_term_name(t, "b2");
  add_term(t);
  t = yices_new_uninterpreted_term(bv2);
  yices_set_term_name(t, "b3");
  add_term(t);
  t = yices_new_uninterpreted_term(bv2);
  yices_set_term_name(t, "b4");
  add_term(t);

  t = yices_new_uninterpreted_term(bv12);
  yices_set_term_name(t, "c0");
  add_term(t);
  t = yices_new_uninterpreted_term(bv12);
  yices_set_term_name(t, "c1");
  add_term(t);
  t = yices_new_uninterpreted_term(bv12);
  yices_set_term_name(t, "c2");
  add_term(t);
  t = yices_new_uninterpreted_term(bv12);
  yices_set_term_name(t, "c3");
  add_term(t);
  t = yices_new_uninterpreted_term(bv12);
  yices_set_term_name(t, "c4");
  add_term(t);

  t = yices_new_uninterpreted_term(bv32);
  yices_set_term_name(t, "d0");
  add_term(t);
  t = yices_new_uninterpreted_term(bv32);
  yices_set_term_name(t, "d1");
  add_term(t);
  t = yices_new_uninterpreted_term(bv32);
  yices_set_term_name(t, "d2");
  add_term(t);
  t = yices_new_uninterpreted_term(bv32);
  yices_set_term_name(t, "d3");
  add_term(t);
  t = yices_new_uninterpreted_term(bv32);
  yices_set_term_name(t, "d4");
  add_term(t);

  t = yices_new_uninterpreted_term(bv64);
  yices_set_term_name(t, "e0");
  add_term(t);
  t = yices_new_uninterpreted_term(bv64);
  yices_set_term_name(t, "e1");
  add_term(t);
  t = yices_new_uninterpreted_term(bv64);
  yices_set_term_name(t, "e2");
  add_term(t);
  t = yices_new_uninterpreted_term(bv64);
  yices_set_term_name(t, "e3");
  add_term(t);
  t = yices_new_uninterpreted_term(bv64);
  yices_set_term_name(t, "e4");
  add_term(t);

  t = yices_new_uninterpreted_term(bv65);
  yices_set_term_name(t, "f0");
  add_term(t);
  t = yices_new_uninterpreted_term(bv65);
  yices_set_term_name(t, "f1");
  add_term(t);
  t = yices_new_uninterpreted_term(bv65);
  yices_set_term_name(t, "f2");
  add_term(t);
  t = yices_new_uninterpreted_term(bv65);
  yices_set_term_name(t, "f3");
  add_term(t);
  t = yices_new_uninterpreted_term(bv65);
  yices_set_term_name(t, "f4");
  add_term(t);

  t = yices_new_uninterpreted_term(bv100);
  yices_set_term_name(t, "g0");
  add_term(t);
  t = yices_new_uninterpreted_term(bv100);
  yices_set_term_name(t, "g1");
  add_term(t);
  t = yices_new_uninterpreted_term(bv100);
  yices_set_term_name(t, "g2");
  add_term(t);
  t = yices_new_uninterpreted_term(bv100);
  yices_set_term_name(t, "g3");
  add_term(t);
  t = yices_new_uninterpreted_term(bv100);
  yices_set_term_name(t, "g4");
  add_term(t);

}



/*
 * FUNCTIONS TO TEST
 */

/*
 * Binary functions that require two bitvector of the same size
 * - for each function, we store: name + function pointer in a global
 *   array
 */
typedef struct bv_binop_s {
  char *name;
  term_t (*fun)(term_t, term_t);
} bv_binop_t;

#define NUM_BINOPS 18

static bv_binop_t binop_array[NUM_BINOPS] = {
  { "bvadd", yices_bvadd },
  { "bvsub", yices_bvsub },
  { "bvmul", yices_bvmul },
  { "bvdiv", yices_bvdiv },
  { "bvrem", yices_bvrem },
  { "bvsdiv", yices_bvsdiv },
  { "bvsrem", yices_bvsrem },
  { "bvsmod", yices_bvsmod },
  { "bvand", yices_bvand },
  { "bvor", yices_bvor },
  { "bvxor", yices_bvxor },
  { "bvnand", yices_bvnand },
  { "bvnor", yices_bvnor },
  { "bvxnor", yices_bvxnor },
  { "bvshl", yices_bvshl },
  { "bvlshr", yices_bvlshr },
  { "bvashr", yices_bvashr },
  { "redcomp", yices_redcomp },
};


/*
 * Functions that take one bitvector argument
 */
typedef struct bv_unary_op_s {
  char *name;
  term_t (*fun)(term_t);
} bv_unary_op_t;

#define NUM_UNARY_OPS 5

static bv_unary_op_t unop_array[NUM_UNARY_OPS] = {
  { "bvneg", yices_bvneg },
  { "bvsquare", yices_bvsquare },
  { "bvnot", yices_bvnot },
  { "redand", yices_redand },
  { "redor", yices_redor },
};


/*
 * Atom constructors: two bitvector arguments
 */
#define NUM_PREDS 10

static bv_binop_t pred_array[NUM_PREDS] = {
  { "bveq", yices_bveq_atom },
  { "bvneq", yices_bvneq_atom },
  { "bvge", yices_bvge_atom },
  { "bvgt", yices_bvgt_atom },
  { "bvle", yices_bvle_atom },
  { "bvlt", yices_bvlt_atom },
  { "bvsge", yices_bvsge_atom },
  { "bvsgt", yices_bvsgt_atom },
  { "bvsle", yices_bvsle_atom },
  { "bvslt", yices_bvslt_atom },
};


/*
 * Shift and rotate operations: a bitvector + an integer constant
 */
typedef struct bv_shift_op_s {
  char *name;
  term_t (*fun)(term_t, uint32_t);
} bv_shift_op_t;

#define NUM_SHIFT_OPS 7

static bv_shift_op_t shift_array[NUM_SHIFT_OPS] = {
  { "shift_left0", yices_shift_left0 },
  { "shift_left1", yices_shift_left1 },
  { "shift_right0", yices_shift_right0 },
  { "shift_right1", yices_shift_right1 },
  { "ashift_right", yices_ashift_right },
  { "rotate_left", yices_rotate_left },
  { "rotate_right", yices_rotate_right },
};


/*
 * Zero-extend, sign-extend, repeat concat: bitvector + integer
 */
#define NUM_EXTEND_OPS 3

static bv_shift_op_t extend_array[NUM_EXTEND_OPS] = {
  { "bvrepeat", yices_bvrepeat },
  { "sign_extend", yices_sign_extend },
  { "zero_extend", yices_zero_extend },
};



/*
 * Test a binary operation
 * - i = index in binop_array
 * - t1, t2 = arguments
 */
static term_t test_binop(FILE* output, uint32_t i, term_t t1, term_t t2) {
  term_t t;

  assert(i < NUM_BINOPS);

  fprintf(output, "test: (%s ", binop_array[i].name);
  print_term_mt(output, t1);
  fprintf(output, " ");
  print_term_mt(output, t2);
  fprintf(output, ") --> ");
  t = binop_array[i].fun(t1, t2);
  print_term_mt(output, t);
  fprintf(output, "\n");

  fflush(output);

  return t;
}

// same thing for unary operations
static term_t test_unop(FILE* output, uint32_t i, term_t t1) {
  term_t t;

  assert(i < NUM_UNARY_OPS);

  fprintf(output, "test: (%s ", unop_array[i].name);
  print_term_mt(output, t1);
  fprintf(output, ") --> ");
  t = unop_array[i].fun(t1);
  print_term_mt(output, t);
  fprintf(output, "\n");

  fflush(output);

  return t;
}


// predicate
static term_t test_pred(FILE* output, uint32_t i, term_t t1, term_t t2) {
  term_t t;

  assert(i < NUM_PREDS);

  fprintf(output, "test: (%s ", pred_array[i].name);
  print_term_mt(output, t1);
  fprintf(output, " ");
  print_term_mt(output, t2);
  fprintf(output, ") --> ");
  t = pred_array[i].fun(t1, t2);
  print_term_mt(output, t);
  fprintf(output, "\n");

  fflush(output);

  return t;
}


// shift/rotate operations
static term_t test_shift(FILE* output, uint32_t i, term_t t1, uint32_t n) {
  term_t t;

  assert(i < NUM_SHIFT_OPS);

  fprintf(output, "test: (%s ", shift_array[i].name);
  print_term_mt(output, t1);
  fprintf(output, " %"PRIu32") --> ", n);
  t = shift_array[i].fun(t1, n);
  print_term_mt(output, t);
  fprintf(output, "\n");

  fflush(output);

  return t;
}

// extend/repeat operations
static term_t test_extend(FILE* output, uint32_t i, term_t t1, uint32_t n) {
  term_t t;

  assert(i < NUM_EXTEND_OPS);

  fprintf(output, "test: (%s ", extend_array[i].name);
  print_term_mt(output, t1);
  fprintf(output, " %"PRIu32") --> ", n);
  t = extend_array[i].fun(t1, n);
  print_term_mt(output, t);
  fprintf(output, "\n");

  fflush(output);

  return t;
}



/*
 * Test bvconcat
 */
static term_t test_bvconcat(FILE* output, term_t t1, term_t t2) {
  term_t t;

  fprintf(output, "test: (bvconcat ");
  print_term_mt(output, t1);
  fprintf(output, " ");
  print_term_mt(output, t2);
  fprintf(output, ") ---> ");
  t = yices_bvconcat(t1, t2);
  print_term_mt(output, t);
  fprintf(output, "\n");

  fflush(output);

  return t;
}


/*
 * Test bvextract
 */
static term_t test_bvextract(FILE* output, term_t t1, uint32_t i, uint32_t j) {
  term_t t;

  fprintf(output, "test: (bvextract ");
  print_term_mt(output, t1);
  fprintf(output, " %"PRIu32" %"PRIu32") --> ", i, j);
  t = yices_bvextract(t1, i, j);
  print_term_mt(output, t);
  fprintf(output, "\n");

  fflush(output);

  return t;
}


/*
 * Test of bvarray construct
 */
static term_t __bvarray[100];
static yices_lock_t __bvarray_lock;

static void init_bvarray(void){
 create_yices_lock(&__bvarray_lock);
}

static void destroy_bvarray(void){
 destroy_yices_lock(&__bvarray_lock);
}


// array of constants + t1 + (not t1)
static term_t test_bvarray1(FILE* output, uint32_t n, term_t t1) {
  term_t t;
  uint32_t i;
  
  assert(n <= 100);

  get_yices_lock(&__bvarray_lock);

  for (i=0; i<n; i++) {
    switch (random() % 4) {
    case 0:
      __bvarray[i] = false_term;
      break;

    case 1:
      __bvarray[i] = true_term;
      break;

    case 2:
      __bvarray[i] = t1;
      break;

    default:
      __bvarray[i] = yices_not(t1);
      break;
    }
  }

  fprintf(output, "test: (bvarray");
  for (i=0; i<n; i++) {
    fprintf(output, " ");
    print_term_mt(output, __bvarray[i]);
  }
  fprintf(output, ") --> ");
  t = yices_bvarray(n, __bvarray);
  print_term_mt(output, t);
  fprintf(output, "\n");

  fflush(output);

  release_yices_lock(&__bvarray_lock);

  return t;
}

// array of constants + t1/t2 + (not t1) + (not t2)
static term_t test_bvarray2(FILE* output, uint32_t n, term_t t1, term_t t2) {
  term_t t;
  uint32_t i;

  assert(n <= 100);

  get_yices_lock(&__bvarray_lock);

  for (i=0; i<n; i++) {
    switch (random() % 6) {
    case 0:
      __bvarray[i] = false_term;
      break;

    case 1:
      __bvarray[i] = true_term;
      break;

    case 2:
      __bvarray[i] = t1;
      break;

    case 3:
      __bvarray[i] = yices_not(t1);
      break;

    case 4:
      __bvarray[i] = t2;
      break;

    default:
      __bvarray[i] = yices_not(t2);
      break;
    }
  }

  fprintf(output, "test: (bvarray");
  for (i=0; i<n; i++) {
    fprintf(output, " ");
    print_term_mt(output, __bvarray[i]);
  }
  fprintf(output, ") --> ");
  t = yices_bvarray(n, __bvarray);
  print_term_mt(output, t);
  fprintf(output, "\n");

  fflush(output);

  release_yices_lock(&__bvarray_lock);

  return t;
}


/*
 * If-then-else
 */
static term_t test_ite(FILE* output, term_t c, term_t left, term_t right) {
  term_t t;

  fprintf(output, "test: (ite ");
  print_term_mt(output, c);
  fprintf(output, " ");
  print_term_mt(output, left);
  fprintf(output, " ");
  print_term_mt(output, right);
  fprintf(output, ") --> ");
  t = yices_ite(c, left, right);
  print_term_mt(output, t);
  fprintf(output, "\n");

  fflush(output);

  return t;
}


/*
 * Test bit_extract
 */
static term_t test_bitextract(FILE* output, term_t t, uint32_t i) {
  term_t b;

  fprintf(output, "test: (bit-extract ");
  print_term_mt(output, t);
  fprintf(output, " %"PRIu32") --> ", i);
  b = yices_bitextract(t, i);
  print_term_mt(output, b);
  fprintf(output, "\n");

  fflush(output);

  return b;
}



/*
 * Run all possible tests with terms t1 and t2 (equal size)
 */
static void full_binary_tests(FILE* output, term_t t1, term_t t2) {
  uint32_t i, n;

  for (i=0; i<NUM_BINOPS; i++) {
    test_binop(output, i, t1, t2);
    test_binop(output, i, t2, t1);
  }

  for (i=0; i<NUM_UNARY_OPS; i++) {
    test_unop(output, i, t1);
    test_unop(output, i, t2);
  }

  for (i=0; i<NUM_PREDS; i++) {
    test_pred(output, i, t1, t2);
  }

  n = term_bitsize_mt(__yices_globals.terms, t1);
  for (i=0; i<NUM_SHIFT_OPS; i++) {
    test_shift(output, i, t1, 0);
    test_shift(output, i, t2, 0);
    test_shift(output, i, t1, 1);
    test_shift(output, i, t2, 1);
    test_shift(output, i, t1, n-1);
    test_shift(output, i, t2, n-1);
    test_shift(output, i, t1, n);
    test_shift(output, i, t2, n);
  }

  for (i=0; i<NUM_EXTEND_OPS; i++) {
    if (i > 0) {
      // repeat concat does not allow n=0
      test_extend(output, i, t1, 0);
      test_extend(output, i, t2, 0);
    }
    test_extend(output, i, t1, 1);
    test_extend(output, i, t2, 1);
    test_extend(output, i, t1, 4);
    test_extend(output, i, t2, 4);
  }

  test_bvconcat(output, t1, t2);
  test_bvconcat(output, t2, t1);
  test_bvconcat(output, t1, t1);
  test_bvconcat(output, t2, t2);

  test_bvextract(output, t1, 0, n-1);
  test_bvextract(output, t2, 0, n-1);
  for (i=0; i+2<n; i++) {
    test_bvextract(output, t1, i, i+2);
    test_bvextract(output, t2, i, i+2);
  }

  for (i=0; i<n; i++) {
    test_bvextract(output, t1, i, i);
    test_bvextract(output, t2, i, i);
  }

  for (i=0; i<n; i++) {
    test_bitextract(output, t1, i);
    test_bitextract(output, t2, i);
  }
}




/*
 * RANDOM TESTS
 */


/*
 * Run n full tests on a pair of randomly selected bit-vector terms
 */
static void random_binary_tests(FILE* output, uint32_t n) {
  type_t tau;
  term_t t1, t2;

  while (n > 0) {
    
    get_yices_lock(&__all_lock);

    tau = type_store_sample(&__all_types, is_bvtype_mt);
    assert(tau != NULL_TYPE);
    t1 = type_store_sample_terms(&__all_types, tau);
    t2 = type_store_sample_terms(&__all_types, tau);

    release_yices_lock(&__all_lock);


    assert(t1 != NULL_TERM && t2 != NULL_TERM);
    fprintf(output, "--- Test %"PRIu32"---\n", n);
    full_binary_tests(output, t1, t2);
    fprintf(output, "\n\n");
    n --;
  }
}



/*
 * Random bitarrays n rounds
 */
static void random_bvarrays(FILE* output, uint32_t n) {
  type_t tau;
  term_t t1, t2, t;
  uint32_t k;

  fprintf(output, "\n---- Random bitarrays ----\n");
  while (n > 0) {

    get_yices_lock(&__all_lock);

    tau = type_store_sample(&__all_types, is_bvtype_mt);
    k = bv_type_size(__yices_globals.types, tau);
    t1 = term_store_sample(&__all_terms, the_boolean, has_type_mt);
    t2 = term_store_sample(&__all_terms, the_boolean, has_type_mt);

    release_yices_lock(&__all_lock);


    t = test_bvarray1(output, k, t1);
    add_term(t);
    fprintf(output, "\n");

    t = test_bvarray2(output, k, t1, t2);
    add_term(t);
    fprintf(output, "\n");

    n --;
  }
}



/*
 * Random bv-extracts: n rounds
 */
static void random_bvextracts(FILE* output, uint32_t n) {
  type_t tau;
  term_t t1, t2, t3, t;
  uint32_t k, i;

  fprintf(output, "\n---- Random bvextracts ----\n");
  while (n > 0) {

    get_yices_lock(&__all_lock);
 
    tau = type_store_sample(&__all_types, is_bvtype_mt);
    k = bv_type_size(__yices_globals.types, tau);

    t1 = type_store_sample_terms(&__all_types, tau);

    release_yices_lock(&__all_lock);

    // split t1
    i = ((uint32_t) random()) % k;
    assert(0 <= i && i <= k-1);

    // right part: low order bits [0 ... i]
    t2 = test_bvextract(output, t1, 0, i);
    add_term(t2);

    if (i < k-1) {
      // left part: high-order bits [i+1 ... k-1]
      t3 = test_bvextract(output, t1, i+1, k-1);
      add_term(t3);

      // check concat: should get back t1
      t = test_bvconcat(output, t3, t2);
      assert(t == t1);

    } else {
      // the left part is empty
      assert(t1 == t2);
    }

    fprintf(output, "\n");

    n --;
  }
}


/*
 * Random if-then-else test: n rounds
 */
static void random_ite(FILE* output, uint32_t n) {
  type_t tau;
  term_t t1, t2, c;

  fprintf(output, "\n---- Test if-then-else ----\n");
  while (n > 0) {

    get_yices_lock(&__all_lock);

    tau = type_store_sample(&__all_types, is_bvtype_mt);
    t1 = type_store_sample_terms(&__all_types, tau);
    t2 = type_store_sample_terms(&__all_types, tau);
    c = term_store_sample(&__all_terms, the_boolean, has_type_mt);

    release_yices_lock(&__all_lock);


    test_ite(output, c, t1, t2);
    fprintf(output, "\n");

    n --;
  }
}

yices_thread_result_t YICES_THREAD_ATTR test_thread(void* arg){
  thread_data_t* tdata = (thread_data_t *)arg;
  FILE* output = tdata->output;

  fprintf(stderr, "Starting: %s\n", "show_types_mt");
  show_types_mt(output);

  fprintf(stderr, "Starting: %s\n", "show_terms_mt");
  show_terms_mt(output);

  fprintf(stderr, "Starting: %s\n", "random_bvarrays");
  random_bvarrays(output, BVNUM);

  fprintf(stderr, "Starting: %s\n", "random_bvextracts");
  random_bvextracts(output, BVNUM);

  fprintf(stderr, "Starting: %s\n", "random_ite");
  random_ite(output, ITENUM);

  fprintf(stderr, "Starting: %s\n", "random_binary_tests");
  random_binary_tests(output, BINUM);

  fprintf(stderr, "Starting: %s\n", "show_types_mt");
  show_types_mt(output);

  fprintf(stderr, "Starting: %s\n", "show_terms_mt");
  show_terms_mt(output);


  fprintf(stderr, "Done.\n");

  return yices_thread_exit();
}

int main(int argc, char* argv[]) {

  if(argc != 2){
    mt_test_usage(argc, argv);
    return 0;
  } else {
    int32_t nthreads = atoi(argv[1]);

    yices_init();
    init_bvarray();
    init_store();
    init_base_types();
    init_base_terms();

    if(nthreads < 0){
      fprintf(stderr, "thread number must be positive!\n");
      exit(EXIT_FAILURE);
    } else if(nthreads == 0){
      thread_data_t tdata = {0, stdout};
      test_thread(&tdata);
    } else {
      launch_threads(nthreads, NULL, "test_api3_mt", test_thread);
    }
    

    delete_store();
    destroy_bvarray();
    yices_exit();
  }
  return 0;
}
