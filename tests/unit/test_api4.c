/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST BOOLEAN API FUNCTIONS
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
 * Add term t to the store (t should not be present)
 */
static void term_store_add_term(term_store_t *store, term_t t) {
  uint32_t i;

  assert(! term_store_contains_term(store, t));

  i = term_store_alloc_index(store);
  store->term[i] = t;
  term_store_mark_term(store, t);
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
static bool has_type(type_t tau, term_t t) {
  return term_type(__yices_globals.terms, t) == tau;
}




/*
 * GLOBAL STORE + boolean type + a buffer
 */
static term_store_t all_terms;
static type_t boolean;
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

  boolean = yices_bool_type();
  term_store_add_term(&all_terms, yices_true());
  term_store_add_term(&all_terms, yices_false());

  // ten boolean variables
  for (i=0; i<10; i++) {
    t = yices_new_uninterpreted_term(boolean);
    sprintf(name, "p%"PRIu32, i);
    yices_set_term_name(t, name);
    term_store_add_term(&all_terms, t);
    term_store_add_term(&all_terms, yices_not(t));
  }
}


/*
 * Binary constructors: bool x bool -> bool
 */
typedef struct bool_binop_s {
  char *name;
  term_t (*fun)(term_t, term_t);
} bool_binop_t;

#define NUM_BINOPS 7

static bool_binop_t binop_array[NUM_BINOPS] = {
  { "eq", yices_eq },
  { "neq", yices_neq },
  { "or2", yices_or2 },
  { "and2", yices_and2 },
  { "xor2", yices_xor2 },
  { "iff", yices_iff },
  { "implies", yices_implies },
};


/*
 * n-ary constructors
 */
typedef struct bool_op_s {
  char *name;
  term_t (*fun)(uint32_t n, term_t arg[]);
} bool_op_t;

#define NUM_OPS 4

static bool_op_t op_array[NUM_OPS] = {
  { "or", yices_or },
  { "and", yices_and },
  { "xor", yices_xor },
  { "distinct", yices_distinct },
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
  t = binop_array[i].fun(t1, t2);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}


/*
 * Test n-ary operation with argumeents a[0 .. n-1]
 * - i = index of the operation in op_array
 */
static term_t test_op(uint32_t i, uint32_t n, term_t *a) {
  term_t aux[n];
  term_t t;
  uint32_t j;

  assert(i < NUM_OPS);

  printf("test: (%s", op_array[i].name);
  for (j=0; j<n; j++) {
    printf(" ");
    print_term(stdout, __yices_globals.terms, a[j]);
    aux[j] = a[j];
  }
  printf(") --> ");
  t = op_array[i].fun(n, aux);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}



/*
 * If-then-else
 */
static term_t test_ite(term_t c, term_t left, term_t right) {
  term_t t;

  printf("test: (ite ");
  print_term(stdout, __yices_globals.terms, c);
  printf(" ");
  print_term(stdout, __yices_globals.terms, left);
  printf(" ");
  print_term(stdout, __yices_globals.terms, right);
  printf(") --> ");
  t = yices_ite(c, left, right);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}



/*
 * Run all binary tests on t1 and t2
 */
static void all_binary_tests(term_t t1, term_t t2) {
  uint32_t i;

  for (i=0; i<NUM_BINOPS; i++) {
    test_binop(i, t1, t2);
    test_binop(i, t2, t1);
  }
}


/*
 * Run all n-ary tests for n and a[0...n-1]
 */
static void all_nary_tests(uint32_t n, term_t *a) {
  uint32_t i;

  for (i=0; i<NUM_OPS-1; i++) {
    test_op(i, n, a);
  }
  // skip distinct if n = 0
  if (n > 0) {
    test_op(i, n, a);
  }
}


/*
 * Run n random binary tests
 */
static void random_binary_tests(uint32_t n) {
  term_t t1, t2;

  while (n > 0) {
    t1 = term_store_sample(&all_terms, boolean, has_type);
    t2 = term_store_sample(&all_terms, boolean, has_type);
    printf("--- Test %"PRIu32" ---\n", n);
    all_binary_tests(t1, t2);
    printf("\n\n");
    n --;
  }
}


/*
 * Run n random n-ary tests
 */
static void random_nary_tests(uint32_t n) {
  uint32_t i, m;
  term_t t;

  while (n > 0) {
    m = ((uint32_t) random()) % 10; // size between 0 and 9
    ivector_reset(&buffer);
    for (i=0; i<m; i++) {
      t = term_store_sample(&all_terms, boolean, has_type);
      ivector_push(&buffer, t);
    }
    printf("--- Test %"PRIu32" ---\n", n);
    all_nary_tests(m, buffer.data);
    printf("\n\n");

    n --;
  }
}


/*
 * Random if-then-else test: n rounds
 */
static void random_ite(uint32_t n) {
  term_t t1, t2, c;

  printf("\n---- Test if-then-else ----\n");
  while (n > 0) {
    c = term_store_sample(&all_terms, boolean, has_type);
    t1 = term_store_sample(&all_terms, boolean, has_type);
    t2 = term_store_sample(&all_terms, boolean, has_type);

    test_ite(c, t1, t2);
    printf("\n");

    n --;
  }
}



int main(void) {
  yices_init();
  init_store();

  show_types();
  show_terms();
  printf("\n\n");

  random_binary_tests(1000);
  random_nary_tests(3000);
  random_ite(3000);

  show_terms();

  delete_term_store(&all_terms);
  delete_ivector(&buffer);

  yices_exit();

  printf("All tests succeeded\n");
  
  return 0;
}
