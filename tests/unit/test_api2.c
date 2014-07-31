/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST GENERAL API FUNCTIONS
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

#include "utils/int_vectors.h"
#include "utils/memalloc.h"
#include "utils/bitvectors.h"

#include "terms/rationals.h"
#include "terms/bv64_constants.h"
#include "terms/bv_constants.h"

#include "yices.h"
#include "api/yices_globals.h"
#include "io/type_printer.h"
#include "io/term_printer.h"



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
 * TYPE STORE
 */

/*
 * Type store:
 * - size = its size
 * - ntypes = number of types
 * - type = array where the types are stored
 * - terms = array of vectors of terms:
 *   terms[i] = all the terms of type type[i]
 */
typedef struct type_store_s {
  uint32_t size;
  uint32_t ntypes;
  type_t *type;
  ivector_t *terms;
} type_store_t;


#define TYPE_STORE_DEF_SIZE 100
#define TYPE_STORE_MAX_SIZE (UINT32_MAX/sizeof(ivector_t))


/*
 * Initialization
 */
static void init_type_store(type_store_t *store) {
  uint32_t n;

  n = TYPE_STORE_DEF_SIZE;
  assert(n < TYPE_STORE_MAX_SIZE);

  store->size = n;
  store->ntypes = 0;
  store->type = (type_t *) safe_malloc(n * sizeof(type_t));
  store->terms = (ivector_t *) safe_malloc(n * sizeof(ivector_t));
}


/*
 * Make the store 50% larger
 */
static void extend_type_store(type_store_t *store) {
  uint32_t n;

  n = store->size + 1;
  n += n >> 1;

  if (n >= TYPE_STORE_MAX_SIZE) {
    out_of_memory();
  }

  store->size = n;
  store->type = (type_t *) safe_realloc(store->type, n * sizeof(type_t));
  store->terms = (ivector_t *) safe_realloc(store->terms, n * sizeof(ivector_t));
}


/*
 * Allocate a new index i and initialize terms[i]
 */
static uint32_t type_store_alloc_index(type_store_t *store) {
  uint32_t i;

  i = store->ntypes;
  if (i == store->size) {
    extend_type_store(store);
  }
  assert(i < store->size);

  init_ivector(store->terms + i, 10);
  store->ntypes ++;

  return i;
}


/*
 * Get the index of type tau:
 * - if tau is not in the store, add it
 */
static uint32_t type_store_get_type(type_store_t *store, type_t tau) {
  uint32_t i, n;

  n = store->ntypes;
  for (i=0; i<n; i++) {
    if (store->type[i] == tau) {
      return i;
    }
  }

  i = type_store_alloc_index(store);
  store->type[i] = tau;

  return i;
}


/*
 * Add term t to the store:
 * - t is added as last element of store->terms[i] where i = index for type of t
 */
static void type_store_add_term(type_store_t *store, term_t t) {
  uint32_t i;
  type_t tau;

  assert(good_term(__yices_globals.terms, t));

  tau = term_type(__yices_globals.terms, t);
  i = type_store_get_type(store, tau);
  ivector_push(store->terms + i, t);
}



/*
 * Get the index of type tau.
 * - return store->ntypes is tau is not present in the store.
 */
static uint32_t type_store_type_index(type_store_t *store, type_t tau) {
  uint32_t i, n;

  n = store->ntypes;
  for (i=0; i<n; i++) {
    if (store->type[i] == tau) break;
  }
  return i;
}




/*
 * Delete the store
 */
static void delete_type_store(type_store_t *store) {
  uint32_t i, n;

  n = store->ntypes;
  for (i=0; i<n; i++) {
    delete_ivector(store->terms + i);
  }
  safe_free(store->type);
  safe_free(store->terms);

  store->type = NULL;
  store->terms = NULL;
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
 * GLOBAL STORE:
 * - a store for all the types and another one for the terms
 */
static type_store_t all_types;
static term_store_t all_terms;


/*
 * Initialize both
 */
static void init_store(void) {
  init_type_store(&all_types);
  init_term_store(&all_terms);
}


/*
 * Delete both
 */
static void delete_store(void) {
  delete_type_store(&all_types);
  delete_term_store(&all_terms);
}


/*
 * Add term t to both
 * - do nothing if t is already present
 */
static void add_term(term_t t) {
  if (! term_store_contains_term(&all_terms, t)) {
    term_store_add_term(&all_terms, t);
    type_store_add_term(&all_types, t);
  }
}



/*
 * BASE TERMS
 */

/*
 * Constructors for function type (tau1 x tau2 -> tau3) and (tau1 -> tau2)
 */
static type_t binary_fun_type(type_t tau1, type_t tau2, type_t tau3) {
  type_t aux[2];

  aux[0] = tau1;
  aux[1] = tau2;
  return yices_function_type(2, aux, tau3);
}

static type_t unary_fun_type(type_t tau1, type_t tau2) {
  return yices_function_type(1, &tau1, tau2);
}


// tuple types
static type_t binary_tuple_type(type_t tau1, type_t tau2) {
  type_t aux[2];

  aux[0] = tau1;
  aux[1] = tau2;
  return yices_tuple_type(2, aux);
}

static type_t unary_tuple_type(type_t tau) {
  return yices_tuple_type(1, &tau);
}

static type_t ternary_tuple_type(type_t tau1, type_t tau2, type_t tau3) {
  type_t aux[3];

  aux[0] = tau1;
  aux[1] = tau2;
  aux[2] = tau3;
  return yices_tuple_type(3, aux);
}


/*
 * Add constants and uninterpreted terms of various types
 */
static void init_base_terms(void) {
  type_t tau, sigma;
  term_t t, u, v;

  // boolean terms
  add_term(yices_true());
  add_term(yices_false());
  tau = yices_bool_type();
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "p0");
  add_term(t);
  add_term(yices_not(t));
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "p1");
  add_term(t);
  add_term(yices_not(t));
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "p2");
  add_term(t);
  add_term(yices_not(t));

  // arithmetic terms
  add_term(yices_zero());
  add_term(yices_int32(1));
  add_term(yices_rational32(1, 3));

  tau = yices_int_type();
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "i");
  add_term(t);
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "j");
  add_term(t);
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "k");
  add_term(t);

  tau = yices_real_type();
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "x");
  add_term(t);
  u = yices_new_uninterpreted_term(tau);
  yices_set_term_name(u, "y");
  add_term(u);
  v = yices_new_uninterpreted_term(tau);
  yices_set_term_name(v, "z");
  add_term(v);

  add_term(yices_add(t, u));
  add_term(yices_sub(t, u));
  add_term(yices_add(v, yices_int32(-1)));
  add_term(yices_add(v, yices_int32(3)));

  // terms of uninterpreted type T
  tau = yices_new_uninterpreted_type();
  yices_set_type_name(tau, "T");
  t = yices_constant(tau, 0);
  yices_set_term_name(t, "A");
  add_term(t);
  t = yices_constant(tau, 1);
  yices_set_term_name(t, "B");
  add_term(t);
  t = yices_constant(tau, 2);
  yices_set_term_name(t, "C");
  add_term(t);
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "a");
  add_term(t);
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "b");
  add_term(t);
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "c");
  add_term(t);


  // functions: [T -> bool], [T, T -> bool]
  sigma = unary_fun_type(tau, yices_bool_type());
  t = yices_new_uninterpreted_term(sigma);
  yices_set_term_name(t, "P");
  add_term(t);
  t = yices_new_uninterpreted_term(sigma);
  yices_set_term_name(t, "Q");
  add_term(t);

  sigma = binary_fun_type(tau, tau, yices_bool_type());
  t = yices_new_uninterpreted_term(sigma);
  yices_set_term_name(t, "R");
  add_term(t);
  t = yices_new_uninterpreted_term(sigma);
  yices_set_term_name(t, "S");
  add_term(t);

  // functions: [int, int -> int], [real, real -> real]
  tau = yices_int_type();
  sigma = binary_fun_type(tau, tau, tau);
  t = yices_new_uninterpreted_term(sigma);
  yices_set_term_name(t, "f");
  add_term(t);
  t = yices_new_uninterpreted_term(sigma);
  yices_set_term_name(t, "g");
  add_term(t);

  tau = yices_real_type();
  sigma = binary_fun_type(tau, tau, tau);
  t = yices_new_uninterpreted_term(sigma);
  yices_set_term_name(t, "f0");
  add_term(t);
  t = yices_new_uninterpreted_term(sigma);
  yices_set_term_name(t, "g0");
  add_term(t);

  // tuples
  tau = unary_tuple_type(yices_bool_type());
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "o1");
  add_term(t);
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "o2");
  add_term(t);

  tau = binary_tuple_type(yices_int_type(), yices_real_type());
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "s1");
  add_term(t);
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "s2");
  add_term(t);

  tau = binary_tuple_type(yices_real_type(), yices_int_type());
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "t1");
  add_term(t);
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "t2");
  add_term(t);

  tau = ternary_tuple_type(tau, tau, tau);
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "u1");
  add_term(t);
  t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, "u2");
  add_term(t);

}



/*
 * Test generic term constructors
 */
static term_t test_app1(term_t fun, term_t arg) {
  term_t t;

  printf("test: (");
  print_term(stdout, __yices_globals.terms, fun);
  printf(" ");
  print_term(stdout, __yices_globals.terms, arg);
  printf(") --> ");
  t = yices_application(fun, 1, &arg);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}


static term_t test_app2(term_t fun, term_t arg1, term_t arg2) {
  term_t aux[2];
  term_t t;

  printf("test: (");
  print_term(stdout, __yices_globals.terms, fun);
  printf(" ");
  print_term(stdout, __yices_globals.terms, arg1);
  printf(" ");
  print_term(stdout, __yices_globals.terms, arg2);
  printf(") --> ");
  aux[0] = arg1;
  aux[1] = arg2;
  t = yices_application(fun, 2, aux);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}


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


static term_t test_eq(term_t left, term_t right) {
  term_t t;

  printf("test: (eq ");
  print_term(stdout, __yices_globals.terms, left);
  printf(" ");
  print_term(stdout, __yices_globals.terms, right);
  printf(") --> ");
  t = yices_eq(left, right);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}


static term_t test_neq(term_t left, term_t right) {
  term_t t;

  printf("test: (neq ");
  print_term(stdout, __yices_globals.terms, left);
  printf(" ");
  print_term(stdout, __yices_globals.terms, right);
  printf(") --> ");
  t = yices_neq(left, right);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}


static term_t test_distinct1(term_t arg) {
  term_t t;

  printf("test: (distinct ");
  print_term(stdout, __yices_globals.terms, arg);
  printf(") --> ");
  t = yices_distinct(1, &arg);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}

static term_t test_distinct2(term_t arg1, term_t arg2) {
  term_t aux[2];
  term_t t;

  printf("test: (distinct ");
  print_term(stdout, __yices_globals.terms, arg1);
  printf(" ");
  print_term(stdout, __yices_globals.terms, arg2);
  printf(") --> ");

  aux[0] = arg1;
  aux[1] = arg2;
  t = yices_distinct(2, aux);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}

static term_t test_distinct4(term_t arg1, term_t arg2, term_t arg3, term_t arg4) {
  term_t aux[4];
  term_t t;

  printf("test: (distinct ");
  print_term(stdout, __yices_globals.terms, arg1);
  printf(" ");
  print_term(stdout, __yices_globals.terms, arg2);
  printf(" ");
  print_term(stdout, __yices_globals.terms, arg3);
  printf(" ");
  print_term(stdout, __yices_globals.terms, arg4);
  printf(") --> ");

  aux[0] = arg1;
  aux[1] = arg2;
  aux[2] = arg3;
  aux[3] = arg4;
  t = yices_distinct(4, aux);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}


static term_t test_tuple1(term_t arg) {
  term_t t;

  printf("test: (mk-tuple ");
  print_term(stdout, __yices_globals.terms, arg);
  printf(") --> ");
  t = yices_tuple(1, &arg);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}

static term_t test_tuple2(term_t arg1, term_t arg2) {
  term_t aux[2];
  term_t t;

  printf("test: (mk-tuple ");
  print_term(stdout, __yices_globals.terms, arg1);
  printf(" ");
  print_term(stdout, __yices_globals.terms, arg2);
  printf(") --> ");

  aux[0] = arg1;
  aux[1] = arg2;
  t = yices_tuple(2, aux);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}

static term_t test_tuple4(term_t arg1, term_t arg2, term_t arg3, term_t arg4) {
  term_t aux[4];
  term_t t;

  printf("test: (mk-tuple ");
  print_term(stdout, __yices_globals.terms, arg1);
  printf(" ");
  print_term(stdout, __yices_globals.terms, arg2);
  printf(" ");
  print_term(stdout, __yices_globals.terms, arg3);
  printf(" ");
  print_term(stdout, __yices_globals.terms, arg4);
  printf(") --> ");

  aux[0] = arg1;
  aux[1] = arg2;
  aux[2] = arg3;
  aux[3] = arg4;
  t = yices_tuple(4, aux);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}


static term_t test_select(term_t arg, uint32_t i) {
  term_t t;

  printf("test: (select %"PRIu32" ", i);
  print_term(stdout, __yices_globals.terms, arg);
  printf(") --> ");
  t = yices_select(i, arg);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}


static term_t test_update1(term_t fun, term_t arg, term_t new_v) {
  term_t t;

  printf("test: (update ");
  print_term(stdout, __yices_globals.terms, fun);
  printf(" (");
  print_term(stdout, __yices_globals.terms, arg);
  printf(") ");
  print_term(stdout, __yices_globals.terms, new_v);
  printf(") --> ");
  t = yices_update(fun, 1, &arg, new_v);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}


static term_t test_update2(term_t fun, term_t arg1, term_t arg2, term_t new_v) {
  term_t aux[2];
  term_t t;

  printf("test: (update ");
  print_term(stdout, __yices_globals.terms, fun);
  printf(" (");
  print_term(stdout, __yices_globals.terms, arg1);
  printf(" ");
  print_term(stdout, __yices_globals.terms, arg2);
  printf(") ");
  print_term(stdout, __yices_globals.terms, new_v);
  printf(") --> ");
  aux[0] = arg1;
  aux[1] = arg2;
  t = yices_update(fun, 2, aux, new_v);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}


static term_t test_tuple_update(term_t arg, term_t new_v, uint32_t i) {
  term_t t;

  printf("test: (tuple-update ");
  print_term(stdout, __yices_globals.terms, arg);
  printf(" %"PRIu32" ", i);
  print_term(stdout, __yices_globals.terms, new_v);
  printf(") --> ");
  t = yices_tuple_update(arg, i, new_v);
  print_term(stdout, __yices_globals.terms, t);
  printf("\n");

  fflush(stdout);

  return t;
}



/*
 * RANDOMIZED TESTING
 */

/*
 * Sampling: select one type in store that satifies predicate p
 * - return NULL_TYPE if there's no such type
 */
typedef bool (*predicate_t)(type_t tau);

static type_t type_store_sample(type_store_t *store, predicate_t p) {
  uint32_t i, n, m;
  type_t tau, sigma;

  n = store->ntypes;
 m = 0;
  sigma = NULL_TYPE;
  for (i=0; i<n; i++) {
    tau = store->type[i];
    if (p(tau)) {
      m ++;
      // replace sigma by tau with probability 1/m
      // keep sigma with probablity (m-1)/m
      if ((((uint32_t)random()) % m) == 0) {
	sigma = tau;
      }
    }
  }

  return sigma;
}




/*
 * Sampling: select one of the terms of type tau
 * - return NULL_TERM if there's nothing of type tau in the store.
 */
static term_t type_store_sample_terms(type_store_t *store, type_t tau) {
  uint32_t i, j, n;
  term_t t;

  t = NULL_TERM;
  i = type_store_type_index(store, tau);
  if (i < store->ntypes) {
    n = store->terms[i].size;
    if (n > 0) {
      j = ((uint32_t) random()) % n;
      t = store->terms[i].data[j];
    }
  }

  return t;
}



/*
 * Term sampling: get a term that satisfies the predicate P(tau, t).
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
  if (n > 100) {
    s = term_array_sample(store->term, 100, tau, p); // small terms
    if (s == NULL_TERM || (random() % 10) == 0) {
      t = term_array_sample(store->term + 100, n - 100, tau, p); // large terms
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
 * Predicates used in sampling functions below
 */
// function type of arity 1
static bool is_fun_type1(type_t tau) {
  return is_function_type(__yices_globals.types, tau) &&
    function_type_arity(__yices_globals.types, tau) == 1;
}

// function type of arity 2
static bool is_fun_type2(type_t tau) {
  return is_function_type(__yices_globals.types, tau) &&
    function_type_arity(__yices_globals.types, tau) == 2;
}

// tuple type
static bool is_tup_type(type_t tau) {
  return is_tuple_type(__yices_globals.types, tau);
}

// any type
static bool is_type(type_t tau) {
  return true;
}


/*
 * Term/type predicates
 */
// t's type is a subtype of tau
static bool has_subtype(type_t tau, term_t t) {
  type_t sigma;

  sigma = term_type(__yices_globals.terms, t);
  return is_subtype(__yices_globals.types, sigma, tau);
}

// t's type is compatible with tau
static bool has_compatible_type(type_t tau, term_t t) {
  type_t sigma;

  sigma = term_type(__yices_globals.terms, t);
  return compatible_types(__yices_globals.types, sigma, tau);
}

// t's type is incompatible with tau
static bool has_incompatible_type(type_t tau, term_t t) {
  return !has_compatible_type(tau, t);
}

// any term
static bool is_term(type_t tau, term_t t) {
  return true;
}


/*
 * One random test
 * - select one of the test above (from test_app1 to test_tuple_update)
 * - select arguments for the test randomly then execute the test
 */
static void random_test(void) {
  uint32_t k, i;
  type_t tau, sigma;
  term_t fun;
  term_t t1, t2, t3, t4;
  term_t v;
  term_t t;

  k = random() % 54;
  switch (k) {
  case 0:
  case 1:
  case 2:
    // app1: select a unary function + select a term as argument
    sigma = type_store_sample(&all_types, is_fun_type1);
    fun = type_store_sample_terms(&all_types, sigma);
    tau = function_type_domain(__yices_globals.types, sigma, 0);
    t1 = term_store_sample(&all_terms, tau, has_subtype);
    // run the test:
    t = test_app1(fun, t1);
    break;

  case 3:
  case 4:
  case 5:
    // app2: binary function + two random arguments
    sigma = type_store_sample(&all_types, is_fun_type2);
    fun = type_store_sample_terms(&all_types, sigma);
    tau = function_type_domain(__yices_globals.types, sigma, 0);
    t1 = term_store_sample(&all_terms, tau, has_subtype);
    tau = function_type_domain(__yices_globals.types, sigma, 1);
    t2 = term_store_sample(&all_terms, tau, has_subtype);
    t = test_app2(fun, t1, t2);
    break;

  case 6:
  case 7:
  case 8:
  case 9:
  case 10:
  case 11:
    // ite
    tau = yices_bool_type();
    t1 = type_store_sample_terms(&all_types, tau); // boolean term
    tau = type_store_sample(&all_types, is_type);  // any type
    t2 = term_store_sample(&all_terms, tau, has_compatible_type);
    t3 = term_store_sample(&all_terms, tau, has_compatible_type);
    t = test_ite(t1, t2, t3);
    break;

  case 12:
  case 13:
  case 14:
  case 15:
  case 16:
  case 17:
    // eq
    tau = type_store_sample(&all_types, is_type); // any type
    t1 = term_store_sample(&all_terms, tau, has_compatible_type);
    t2 = term_store_sample(&all_terms, tau, has_compatible_type);
    t = test_eq(t1, t2);
    break;

  case 18:
  case 19:
  case 20:
  case 21:
  case 22:
  case 23:
    // neq
    tau = type_store_sample(&all_types, is_type); // any type
    t1 = term_store_sample(&all_terms, tau, has_compatible_type);
    t2 = term_store_sample(&all_terms, tau, has_compatible_type);
    t = test_neq(t1, t2);
    break;

  case 24:
  case 25:
    // distinct1: any term
    t1 = term_store_sample(&all_terms, NULL_TYPE, is_term);
    t = test_distinct1(t1);
    break;

  case 26:
  case 27:
    // distinct2
    tau = type_store_sample(&all_types, is_type); // any type
    t1 = term_store_sample(&all_terms, tau, has_compatible_type);
    t2 = term_store_sample(&all_terms, tau, has_compatible_type);
    t = test_distinct2(t1, t2);
    break;

  case 28:
  case 29:
    // distinct4
    tau = type_store_sample(&all_types, is_type); // any type
    t1 = term_store_sample(&all_terms, tau, has_compatible_type);
    t2 = term_store_sample(&all_terms, tau, has_compatible_type);
    t3 = term_store_sample(&all_terms, tau, has_compatible_type);
    t4 = term_store_sample(&all_terms, tau, has_compatible_type);
    t = test_distinct4(t1, t2, t3, t4);
    break;

  case 30:
  case 31:
    // tuple1
    t1 = term_store_sample(&all_terms, NULL_TYPE, is_term);
    t = test_tuple1(t1);
    break;

  case 32:
  case 33:
    // tuple2
    t1 = term_store_sample(&all_terms, NULL_TYPE, is_term);
    t2 = term_store_sample(&all_terms, NULL_TYPE, is_term);
    t = test_tuple2(t1, t2);
    break;

  case 34:
  case 35:
    // tuple4
    t1 = term_store_sample(&all_terms, NULL_TYPE, is_term);
    t2 = term_store_sample(&all_terms, NULL_TYPE, is_term);
    t3 = term_store_sample(&all_terms, NULL_TYPE, is_term);
    t4 = term_store_sample(&all_terms, NULL_TYPE, is_term);
    t = test_tuple4(t1, t2, t3, t4);
    break;

  case 36:
  case 37:
  case 38:
  case 39:
  case 40:
  case 41:
    // select
    tau = type_store_sample(&all_types, is_tup_type);
    t1 = type_store_sample_terms(&all_types, tau);
    i = ((uint32_t) random()) % tuple_type_arity(__yices_globals.types, tau);
    t = test_select(t1, i + 1);
    break;

  case 42:
  case 43:
  case 44:
    // update1
    sigma = type_store_sample(&all_types, is_fun_type1);
    fun = type_store_sample_terms(&all_types, sigma);
    tau = function_type_domain(__yices_globals.types, sigma, 0);
    t1 = term_store_sample(&all_terms, tau, has_subtype);
    tau = function_type_range(__yices_globals.types, sigma);
    v = term_store_sample(&all_terms, tau, has_subtype);
    t = test_update1(fun, t1, v);
    break;

  case 45:
  case 46:
  case 47:
    // update2
    sigma = type_store_sample(&all_types, is_fun_type2);
    fun = type_store_sample_terms(&all_types, sigma);
    tau = function_type_domain(__yices_globals.types, sigma, 0);
    t1 = term_store_sample(&all_terms, tau, has_subtype);
    tau = function_type_domain(__yices_globals.types, sigma, 1);
    t2 = term_store_sample(&all_terms, tau, has_subtype);
    tau = function_type_range(__yices_globals.types, sigma);
    v = term_store_sample(&all_terms, tau, has_subtype);
    t = test_update2(fun, t1, t2, v);
    break;

  default:
    assert(48 <= k && k <= 53);
    // tuple update
    sigma = type_store_sample(&all_types, is_tup_type);
    t1 = type_store_sample_terms(&all_types, sigma); // tuple term
    i = ((uint32_t) random()) % tuple_type_arity(__yices_globals.types, sigma);
    tau = tuple_type_component(__yices_globals.types, sigma, i);
    v = term_store_sample(&all_terms, tau, has_subtype);
    // components are indexed from 1 to n
    // but i is between 0 and n-1
    t = test_tuple_update(t1, v, 1 + i);
    break;
  }

  add_term(t);
}



/*
 * n random tests
 */
static void random_tests(uint32_t n) {
  while (n > 0) {
    random_test();
    n --;
  }
}



/*
 * Test of error codes
 */
static bool check_pos_int_required(term_t t) {
  error_report_t *rep;

  rep = yices_error_report();
  return t == NULL_TERM && yices_error_code() == POS_INT_REQUIRED && rep->badval == 0;
}

static bool check_invalid_term(term_t t, term_t bad_term) {
  error_report_t *rep;

  rep = yices_error_report();
  return t == NULL_TERM && yices_error_code() == INVALID_TERM && rep->term1 == bad_term;
}

static bool check_function_required(term_t t, term_t not_fun) {
  error_report_t *rep;

  rep = yices_error_report();
  return t == NULL_TERM && yices_error_code() == FUNCTION_REQUIRED && rep->term1 == not_fun;
}

static bool check_wrong_number_of_arguments(term_t t, type_t tau, uint32_t bad) {
  error_report_t *rep;

  rep = yices_error_report();
  return t == NULL_TERM && yices_error_code() == WRONG_NUMBER_OF_ARGUMENTS &&
    rep->type1 == tau && rep->badval == bad;
}

static bool check_type_mismatch(term_t t, term_t bad_arg, type_t expected_tau) {
  error_report_t *rep;

  rep = yices_error_report();
  return t == NULL_TERM && yices_error_code() == TYPE_MISMATCH && rep->term1 == bad_arg &&
    rep->type1 == expected_tau;
}

static bool check_incompatible_types(term_t t, term_t bad1, term_t bad2) {
  error_report_t *rep;
  type_t tau1, tau2;

  tau1 = term_type(__yices_globals.terms, bad1);
  tau2 = term_type(__yices_globals.terms, bad2);
  rep = yices_error_report();
  return t == NULL_TERM && yices_error_code() == INCOMPATIBLE_TYPES && rep->term1 == bad1 &&
    rep->term2 == bad2 && rep->type1 == tau1 && rep->type2 == tau2;
}

static bool check_too_many_arguments(term_t t, uint32_t n) {
  error_report_t *rep;

  rep = yices_error_report();
  return t == NULL_TERM && yices_error_code() == TOO_MANY_ARGUMENTS && rep->badval == n;
}

static bool check_tuple_required(term_t t, term_t not_tup) {
  error_report_t *rep;

  rep = yices_error_report();
  return t == NULL_TERM && yices_error_code() == TUPLE_REQUIRED && rep->term1 == not_tup;
}

static bool check_invalid_tuple_index(term_t t, type_t tau, uint32_t i) {
  error_report_t *rep;

  rep = yices_error_report();
  return t == NULL_TERM && yices_error_code() == INVALID_TUPLE_INDEX && rep->badval == i &&
    rep->type1 == tau;
}


static void test_error_codes(void) {
  term_t aux[3];
  type_t sigma, tau1, tau2;
  term_t fun, t1, t2, t3;
  term_t v;
  term_t t;

  // error codes for a function application
  sigma = type_store_sample(&all_types, is_fun_type2);
  fun = type_store_sample_terms(&all_types, sigma);
  tau1 = function_type_domain(__yices_globals.types, sigma, 0);
  t1 = term_store_sample(&all_terms, tau1, has_subtype);
  tau2 = function_type_domain(__yices_globals.types, sigma, 1);
  t2 = term_store_sample(&all_terms, tau2, has_subtype);

  t = yices_application(fun, 0, aux);
  assert(check_pos_int_required(t));

  aux[0] = t1;
  aux[1] = t2;
  t = yices_application(-2, 2, aux);
  assert(check_invalid_term(t, -2));

  aux[0] = 4714789;
  aux[1] = t2;
  t = yices_application(fun, 2, aux);
  assert(check_invalid_term(t, aux[0]));

  aux[0] = t1;
  aux[1] = t2;
  t = yices_application(true_term, 2, aux);
  assert(check_function_required(t, true_term));

  t = yices_application(fun, 1, aux);
  assert(check_wrong_number_of_arguments(t, sigma, 1));

  aux[0] = term_store_sample(&all_terms, tau1, has_incompatible_type);
  aux[1] = t2;
  t = yices_application(fun, 2, aux);
  assert(check_type_mismatch(t, aux[0], tau1));

  aux[0] = t1;
  aux[1] = term_store_sample(&all_terms, tau2, has_incompatible_type);
  t = yices_application(fun, 2, aux);
  assert(check_type_mismatch(t, aux[1], tau2));

  // error codes for if-then-else
  tau1 = type_store_sample(&all_types, is_type);
  tau2 = yices_bool_type();
  t1 = term_store_sample(&all_terms, tau1, has_compatible_type);
  t2 = term_store_sample(&all_terms, tau1, has_compatible_type);
  t3 = type_store_sample_terms(&all_types, tau2);

  t = yices_ite(-4, t1, t2);
  assert(check_invalid_term(t, -4));
  t = yices_ite(t3, -3, t2);
  assert(check_invalid_term(t, -3));
  t = yices_ite(t3, t1, -2);
  assert(check_invalid_term(t, -2));

  v = term_store_sample(&all_terms, tau2, has_incompatible_type);
  t = yices_ite(v, t1, t2);
  assert(check_type_mismatch(t, v, tau2));

  v = term_store_sample(&all_terms, tau1, has_incompatible_type);
  t = yices_ite(t3, t1, v);
  assert(check_incompatible_types(t, t1, v));

  // equality
  t = yices_eq(v, t1);
  assert(check_incompatible_types(t, v, t1));

  t = yices_neq(v, t1);
  assert(check_incompatible_types(t, v, t1));

  v = 19309390;
  t = yices_eq(t1, v);
  assert(check_invalid_term(t , v));

  t = yices_neq(t1, v);
  assert(check_invalid_term(t , v));

  // tuple
  aux[0] = t1;
  aux[1] = false_term;
  aux[2] = t2;
  t = yices_tuple(0, aux);
  assert(check_pos_int_required(t));

  t = yices_tuple(UINT32_MAX, aux);
  assert(check_too_many_arguments(t, UINT32_MAX));

  aux[1] = -3;
  t = yices_tuple(3, aux);
  assert(check_invalid_term(t, aux[1]));

  // projection
  t1 = false_term;
  t = yices_select(1, t1);
  assert(check_tuple_required(t, t1));

  t = yices_select(1, -34);
  assert(check_invalid_term(t, -34));

  tau1 = type_store_sample(&all_types, is_tup_type);
  t1 = type_store_sample_terms(&all_types, tau1);
  t = yices_select(6, t1);
  assert(check_invalid_tuple_index(t, tau1, 6));

  t = yices_select(0, t1);
  assert(check_invalid_tuple_index(t, tau1, 0));

  // tuple update
  tau2 = tuple_type_component(__yices_globals.types, tau1, 0);
  v = type_store_sample_terms(&all_types, tau2);

  t = yices_tuple_update(-3, 1, v);
  assert(check_invalid_term(t, -3));

  t = yices_tuple_update(true_term, 1, v);
  assert(check_tuple_required(t, true_term));

  t = yices_tuple_update(t1, 6, v);
  assert(check_invalid_tuple_index(t, tau1, 6));

  t = yices_tuple_update(t1, 0, v);
  assert(check_invalid_tuple_index(t, tau1, 0));

  v = term_store_sample(&all_terms, tau2, has_incompatible_type);
  t = yices_tuple_update(t1, 1, v);
  assert(check_type_mismatch(t, v, tau2));
}



int main(void) {
  yices_init();
  init_store();

  init_base_terms();
  show_types();
  show_terms();

  printf("\n\n*** Random tests ***\n");
  random_tests(10000);
  printf("\n****\n\n");

  test_error_codes();

  show_types();
  show_terms();

  delete_store();
  yices_exit();

  return 0;
}
