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

#include "memalloc.h"
#include "bitvectors.h"
#include "int_vectors.h"

#include "yices.h"
#include "yices_globals.h"
#include "type_printer.h"
#include "term_printer.h"


#include "threads.h"
#include "threadsafe.h"
#include "stores.h"







/*
 * GLOBAL STORE
 */
static yices_lock_t __all_lock;
static term_store_t __all_terms;
static type_t the_boolean;


/*
 * Init store and buffer and create base terms
 */
static void init_store(void) {
  char name[4];
  uint32_t i;
  term_t t;

  init_term_store(&__all_terms);

  the_boolean = yices_bool_type();
  term_store_add_term(&__all_terms, yices_true());
  term_store_add_term(&__all_terms, yices_false());

  // ten boolean variables
  for (i=0; i<10; i++) {
    t = yices_new_uninterpreted_term(the_boolean);
    sprintf(name, "p%"PRIu32, i);
    yices_set_term_name(t, name);
    term_store_add_term(&__all_terms, t);
    term_store_add_term(&__all_terms, yices_not(t));
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


/*
 * Test n-ary operation with argumeents a[0 .. n-1]
 * - i = index of the operation in op_array
 */
static term_t test_op(FILE* output, uint32_t i, uint32_t n, term_t *a) {
  term_t aux[n];
  term_t t;
  uint32_t j;

  assert(i < NUM_OPS);

  fprintf(output, "test: (%s", op_array[i].name);
  for (j=0; j<n; j++) {
    fprintf(output, " ");
    print_term_mt(output, a[j]);
    aux[j] = a[j];
  }
  fprintf(output, ") --> ");
  t = op_array[i].fun(n, aux);
  print_term_mt(output, t);
  fprintf(output, "\n");

  fflush(output);

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
  print_term_mt(output,left);
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
 * Run all binary tests on t1 and t2
 */
static void all_binary_tests(FILE* output, term_t t1, term_t t2) {
  uint32_t i;

  for (i=0; i<NUM_BINOPS; i++) {
    test_binop(output, i, t1, t2);
    test_binop(output, i, t2, t1);
  }
}


/*
 * Run all n-ary tests for n and a[0...n-1]
 */
static void all_nary_tests(FILE* output, uint32_t n, term_t *a) {
  uint32_t i;

  for (i=0; i<NUM_OPS-1; i++) {
    test_op(output, i, n, a);
  }
  // skip distinct if n = 0
  if (n > 0) {
    test_op(output, i, n, a);
  }
}


/*
 * Run n random binary tests
 */
static void random_binary_tests(FILE* output, uint32_t n) {
  term_t t1, t2;

  while (n > 0) {

    get_yices_lock(&__all_lock);

    t1 = term_store_sample(&__all_terms, the_boolean, has_type_mt);
    t2 = term_store_sample(&__all_terms, the_boolean, has_type_mt);

    release_yices_lock(&__all_lock);
  

    fprintf(output, "--- Test %"PRIu32" ---\n", n);
    all_binary_tests(output, t1, t2);
    fprintf(output, "\n\n");
    n --;
  }
}


/*
 * Run n random n-ary tests
 */
static void random_nary_tests(FILE* output, uint32_t n) {
  uint32_t i, m;
  term_t t;
  ivector_t buffer;
  init_ivector(&buffer, 10);

  while (n > 0) {
    m = ((uint32_t) random()) % 10; // size between 0 and 9
    ivector_reset(&buffer);
    for (i=0; i<m; i++) {
      
      get_yices_lock(&__all_lock);

      t = term_store_sample(&__all_terms, the_boolean, has_type_mt);

      release_yices_lock(&__all_lock);


      ivector_push(&buffer, t);
    }
    fprintf(output, "--- Test %"PRIu32" ---\n", n);
    all_nary_tests(output, m, buffer.data);
    fprintf(output, "\n\n");

    n --;
  }

  delete_ivector(&buffer);
}


/*
 * Random if-then-else test: n rounds
 */
static void random_ite(FILE* output, uint32_t n) {
  term_t t1, t2, c;

  fprintf(output, "\n---- Test if-then-else ----\n");
  while (n > 0) {

    get_yices_lock(&__all_lock);

    c = term_store_sample(&__all_terms, the_boolean, has_type_mt);
    t1 = term_store_sample(&__all_terms, the_boolean, has_type_mt);
    t2 = term_store_sample(&__all_terms, the_boolean, has_type_mt);

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
  show_terms_mt(output);
  fprintf(output, "\n\n");

  random_binary_tests(output, 1000);
  random_nary_tests(output, 3000);
  random_ite(output, 3000);

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
    create_yices_lock(&__all_lock);
    init_store();

    if(nthreads < 0){
      fprintf(stderr, "thread number must be positive!\n");
      exit(EXIT_FAILURE);
    } else if(nthreads == 0){
      thread_data_t tdata = {0, stdout};
      test_thread(&tdata);
    } else {
      launch_threads(nthreads, NULL, 0, "test_api4_mt", test_thread, true);
    }
    
    
    destroy_yices_lock(&__all_lock);
    delete_term_store(&__all_terms);
    
    yices_exit();
   
  } 
  return 0;
}
