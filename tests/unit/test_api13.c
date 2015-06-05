/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST DIV/MOD/ABS/FLOOR/CEIL
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

#include "api/yices_globals.h"
#include "io/term_printer.h"
#include "io/type_printer.h"
#include "utils/bitvectors.h"
#include "utils/int_vectors.h"
#include "utils/memalloc.h"

#include "yices.h"



#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif



/*
 * Print the type table
 */
static void show_types(void) {
  printf("\n---- Type table ----\n");
  //  print_type_table(stdout, __yices_globals.types);
  pp_type_table(stdout, __yices_globals.types);
}


/*
 * Print the term table
 */
static void show_terms(void) {
  printf("\n---- Term table -----\n");
  //  print_term_table(stdout, __yices_globals.terms);
  pp_term_table(stdout, __yices_globals.terms);
}



/*
 * TERM STORE
 */

/*
 * Term store:
 * - term = array of all terms
 * - mark = bitvectore: mark[t] = 1 if t is present in terms
 */
typedef struct term_store_s {
  uint32_t size;
  uint32_t nterms;
  term_t *term;
  uint32_t max_term;  // size of mark bitvector
  byte_t *mark;
} term_store_t;

#define TERM_STORE_DEF_SIZE 1000
#define TERM_STORE_MAX_SIZE (UINT32_MAX/sizeof(term_t))

#define TERM_STORE_DEF_MSIZE 100


/*
 * Initialize store
 */
static void init_term_store(term_store_t *store) {
  uint32_t n;

  n = TERM_STORE_DEF_SIZE;
  assert(n < TERM_STORE_MAX_SIZE);

  store->size = n;
  store->nterms = 0;
  store->term = (term_t *) safe_malloc(n * sizeof(term_t));

  n = TERM_STORE_DEF_MSIZE;
  store->max_term = n;
  store->mark = allocate_bitvector0(n);
}


/*
 * Extend: make the term array 50% larger
 */
static void extend_term_store(term_store_t *store) {
  uint32_t n;

  n = store->size + 1;
  n += n>>1;

  if (n >= TERM_STORE_MAX_SIZE) {
    out_of_memory();
  }

  store->size = n;
  store->term = (term_t *) safe_realloc(store->term, n * sizeof(term_t));
}


/*
 * Get a new index i to store a term
 */
static uint32_t term_store_alloc_index(term_store_t *store) {
  uint32_t i;

  i = store->nterms;
  if (i == store->size) {
    extend_term_store(store);
  }
  assert(i < store->size);
  store->nterms ++;

  return i;
}



/*
 * Mark term t
 */
static void term_store_mark_term(term_store_t *store, term_t t) {
  uint32_t n;

  assert(t >= 0);

  n = store->max_term;
  if (t >= n) {
    // make the mark vector large enough to mark t: try to double its size
    // if that's not enough allocate a vector of size
    n += n;
    if (t >= n) {
      n = (t + 8) >> 3; // ceil((t+1)/8)
    }
    store->mark = extend_bitvector0(store->mark, n, store->max_term);
    store->max_term = n;
    assert(t < n);
  }
  set_bit(store->mark, t);
}



/*
 * Check whether t is present in store
 */
static bool term_store_contains_term(term_store_t *store, term_t t) {
  return t < store->max_term && tst_bit(store->mark, t);
}


/*
 * Add term t to the store if t is not already present
 */
static void term_store_add_term(term_store_t *store, term_t t) {
  uint32_t i;

  if (! term_store_contains_term(store, t)) {
    i = term_store_alloc_index(store);
    store->term[i] = t;
    term_store_mark_term(store, t);
  }
}


/*
 * Delete store
 */
static void delete_term_store(term_store_t *store) {
  safe_free(store->term);
  delete_bitvector(store->mark);
  store->term = NULL;
  store->mark = NULL;
}




/*
 * Term sampling: get a random term
 * Give priority to small terms (i.e., those created early).
 */
typedef bool (*term_pred_t)(type_t tau, term_t t);

static term_t term_array_sample(term_t *a, uint32_t n, type_t tau, term_pred_t p) {
  uint32_t i, m;
  term_t t, s;

  m = 0;
  s = NULL_TERM;
  for (i=0; i<n; i++) {
    t = a[i];
    if (p(tau, t)) {
      m ++;
      if ((((uint32_t)random()) % m) == 0) {
	s = t;
      }
    }
  }

  return s;
}

static term_t term_store_sample(term_store_t *store, type_t tau, term_pred_t p) {
  uint32_t n;
  term_t t, s;

  n = store->nterms;
  if (n > 150) {
    s = term_array_sample(store->term, 150, tau, p); // small terms
    if (s == NULL_TERM || (random() % 10) == 0) {
      t = term_array_sample(store->term + 150, n - 150, tau, p); // large terms
      if (t != NULL_TERM) {
	s = t;
      }
    }
  } else {
    s = term_array_sample(store->term, n, tau, p); // all terms are small
  }

  return s;
}



/*
 * Predicate: check whether t has type tau
 */
#if 0
static bool has_type(type_t tau, term_t t) {
  return term_type(__yices_globals.terms, t) == tau;
}
#endif

// check whether t is arithmetic
static bool is_arith(type_t tau, term_t t) {
  return is_arithmetic_term(__yices_globals.terms, t);
}

// check whether t is an arithmetic constant
static bool is_arith_constant(type_t tau, term_t t) {
  return term_kind(__yices_globals.terms, t) == ARITH_CONSTANT;
}


#if 0
// check whether t is arithmetic and has degree < 10
static bool low_degree(type_t tau, term_t t) {
  return is_arithmetic_term(__yices_globals.terms, t) &&
    term_degree(__yices_globals.terms, t) < 10;
}
#endif


/*
 * GLOBAL STORE + int/real types + a buffer
 */
static term_store_t all_terms;
static type_t boolean, integers, reals;
static ivector_t buffer;


/*
 * Init store and buffer and create base terms
 */
static void init_store(void) {
  char name[4];
  uint32_t i;
  term_t t;

  init_term_store(&all_terms);
  init_ivector(&buffer, 10);

  integers = yices_int_type();
  reals = yices_real_type();
  boolean = yices_bool_type();

  term_store_add_term(&all_terms, yices_true());
  term_store_add_term(&all_terms, yices_false());

  term_store_add_term(&all_terms, yices_zero());
  term_store_add_term(&all_terms, yices_int32(1));
  term_store_add_term(&all_terms, yices_int32(-1));
  term_store_add_term(&all_terms, yices_int32(3));
  term_store_add_term(&all_terms, yices_int32(-3));
  term_store_add_term(&all_terms, yices_rational32(3, 2));
  term_store_add_term(&all_terms, yices_rational32(-3, 2));

  // five integer and five real variables
  for (i=0; i<5; i++) {
    t = yices_new_uninterpreted_term(integers);
    sprintf(name, "i%"PRIu32, i);
    yices_set_term_name(t, name);
    term_store_add_term(&all_terms, t);
  }

  for (i=0; i<5; i++) {
    t = yices_new_uninterpreted_term(reals);
    sprintf(name, "x%"PRIu32, i);
    yices_set_term_name(t, name);
    term_store_add_term(&all_terms, t);
  }
}


/*
 * Constant creation
 */
static int32_t num[10] = {
  0, 1, -1, 2, -2, 100, -100, 5, 6, 7,
};

static uint32_t den[10] = {
  1, 2, 3, 4, 10, 20, 30, 100, 200, 103,
};

static void test_constant(int32_t a) {
  term_t t, u;
  mpz_t z;

  mpz_init(z);

  printf("test: constant %"PRId32, a);
  t = yices_int32(a);
  u = yices_int64(a);
  assert(u == t);
  mpz_set_si(z, a);
  u = yices_mpz(z);
  assert(u == t);
  printf(" --> ");
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");
  fflush(stdout);

  mpz_clear(z);
}

static void test_constant_pair(int32_t a, uint32_t b) {
  term_t t, u;
  mpq_t q;

  mpq_init(q);

  printf("test: constant %"PRId32"/%"PRIu32, a, b);
  t = yices_rational32(a, b);
  u = yices_rational64(a, b);
  assert(u == t);
  mpq_set_si(q, a, b);
  mpq_canonicalize(q);
  u = yices_mpq(q);
  assert(u == t);
  printf(" --> ");
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");
  fflush(stdout);

  mpq_clear(q);
}

static void test_constants(void) {
  uint32_t i, j;

  for (i=0; i<10; i++) {
    test_constant(num[i]);
    for (j=0; j<10; j++) {
      test_constant_pair(num[i], den[j]);
    }
  }
}


/*
 * Binary constructors
 */
typedef struct arith_binop_s {
  char *name;
  term_t (*fun)(term_t, term_t);
} arith_binop_t;

#define NUM_BINOPS 3

static arith_binop_t binop_array[NUM_BINOPS] = {
  { "div", yices_idiv },
  { "mod", yices_imod },
  { "divides", yices_divides_atom },
};


/*
 * Unary constructors
 */
typedef struct arith_unop_s {
  char *name;
  term_t (*fun)(term_t);
} arith_unop_t;

#define NUM_UNOPS 4

static arith_unop_t unop_array[NUM_UNOPS] = {
  { "is-int", yices_is_int_atom },
  { "floor", yices_floor },
  { "ceil", yices_ceil },
  { "abs", yices_abs },
};


/*
 * Test a binary operation between t1 and t2
 * - i = index of the operation in binop_array
 */
static term_t test_binop(uint32_t i, term_t t1, term_t t2) {
  term_t t;

  assert(i < NUM_BINOPS);

  printf("test: (%s ", binop_array[i].name);
  print_term(stdout, __yices_globals.terms, t1);
  printf(" ");
  print_term(stdout, __yices_globals.terms, t2);
  printf(") --> ");
  fflush(stdout);
  t = binop_array[i].fun(t1, t2);
  if (t < 0) {
    printf("error code: %d\n", (int) yices_error_code());
    yices_print_error(stdout);
    printf("\n");
  } else {
    print_term(stdout, __yices_globals.terms, t);
    printf("\n");
  }

  fflush(stdout);

  return t;
}


/*
 * Test a unary operation on t1
 * - i = index of the operation in binop_array
 */
static term_t test_unary_op(uint32_t i, term_t t1) {
  term_t t;

  assert(i < NUM_UNOPS);

  printf("test: (%s ", unop_array[i].name);
  print_term(stdout, __yices_globals.terms, t1);
  printf(") --> ");
  fflush(stdout);
  t = unop_array[i].fun(t1);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}

/*
 * Run all binary tests on t1 and t2
 * - t2 is an arithmetic constant
 */
static void all_divmod_tests(term_t t1, term_t t2) {
  test_binop(0, t1, t2); // (div t1 t2)
  test_binop(1, t1, t2); // (mod t1 t2)
  test_binop(2, t2, t1); // (divides t2 t1)
}


/*
 * All unary tests on t1
 */
static void all_unary_tests(term_t t1) {
  uint32_t i;

  for (i=0; i<NUM_UNOPS; i++) {
    test_unary_op(i, t1);
  }
}


/*
 * Run n random binary tests
 */
static void random_binary_tests(uint32_t n) {
  term_t t1, t2;

  while (n > 0) {
    t1 = term_store_sample(&all_terms, boolean, is_arith);
    t2 = term_store_sample(&all_terms, boolean, is_arith_constant);
    printf("--- Test %"PRIu32" ---\n", n);
    all_divmod_tests(t1, t2);
    printf("\n\n");
    n --;
  }
}


/*
 * Run n random unary tests
 */
static void random_unary_tests(uint32_t n) {
  term_t t;

  while (n > 0) {
    t = term_store_sample(&all_terms, boolean, is_arith);
    printf("--- Test %"PRIu32" ---\n", n);
    all_unary_tests(t);
    printf("\n\n");
    n --;
  }
}


/*
 * Add more random arithmetic and boolean terms
 * to the store
 */
static void add_random_terms(uint32_t n) {
  term_t t1, t2, t;
  uint32_t i;

  while (n > 0) {
    i = random() % (NUM_BINOPS + NUM_UNOPS + 2);
    printf("---> random term: n = %"PRIu32" i = %"PRIu32"\n", n, i);
    fflush(stdout);
    if (i < NUM_BINOPS) {
      t1 = term_store_sample(&all_terms, boolean, is_arith);
      t2 = term_store_sample(&all_terms, boolean, is_arith);
      t = test_binop(i, t1, t2);
    } else if (i < NUM_BINOPS + NUM_UNOPS) {
      t1 = term_store_sample(&all_terms, boolean, is_arith);
      t = test_unary_op(i - NUM_BINOPS, t1);
    } else { 
      t1 = term_store_sample(&all_terms, boolean, is_arith);
      t2 = term_store_sample(&all_terms, boolean, is_arith);
      t = yices_add(t1, t2);
    }
    if (t >= 0) {
      term_store_add_term(&all_terms, t);
      n --;
    }
  }
}



int main(void) {
  yices_init();
  init_store();
  show_types();
  show_terms();

  printf("\n\n*** CONSTANTS ***\n");
  test_constants();

  printf("\n\n*** ADDING TERMS ***\n");
  add_random_terms(80);

  printf("\n\n*** RANDOM TESTS ***\n");
  random_binary_tests(2000);
  random_unary_tests(2000);

  show_types();
  show_terms();

  delete_term_store(&all_terms);
  delete_ivector(&buffer);

  yices_exit();

  printf("All tests succeeded\n");
  
  return 0;
}
