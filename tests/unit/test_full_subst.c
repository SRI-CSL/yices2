/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST: SUBSTITUTIONS
 */

#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdlib.h>
#include <assert.h>

#include "api/yices_globals.h"
#include "io/term_printer.h"
#include "terms/full_subst.h"
#include "utils/assert_utils.h"
#include "yices.h"


#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif


/*
 * Global variables
 * - tay = T = uninterpreted type
 * - var[0 ... NVARS-1] = uninterpreted terms of type T
 * - fun[0 ... NFUNS] = uninterpreted functions of type [T, T -> T]
 */
#define NVARS 30
#define NFUNS 5

static type_t tau;
static term_t var[NVARS];
static term_t fun[NVARS];


/*
 * Names for var[0 ... 6]
 * - if there are more vars, we use x7 ...
 */
#define NVNAMES 7

static const char * const vname[NVNAMES] = {
  "x", "y", "z", "t", "u", "v", "w",
};


/*
 * Names for fun[0 .. 4]
 * - if there are more functions, we use f5 ... fn
 */
#define NFNAMES 5

static const char * const fname[NFNAMES] = {
  "f", "g", "h", "p", "q",
};


/*
 * Initialize these tables: tau must be defined
 */
static void init_vars(void) {
  char aux[20];
  const char *name;
  uint32_t i;
  term_t v;
  int32_t code;

  for (i=0; i<NVARS; i++) {
    v = yices_new_uninterpreted_term(tau);
    assert(v >= 0);
    if (i < NVNAMES) {
      name = vname[i];
    } else {
      sprintf(aux, "x%"PRIu32, i);
      name = aux;
    }
    code = yices_set_term_name(v, name);
    assert_true(code == 0);
    var[i] = v;
  }
}

static void init_funs(void) {
  char aux[20];
  const char *name;
  type_t ftype;
  uint32_t i;
  term_t f;
  int32_t code;

  ftype = yices_function_type2(tau, tau, tau); // [tau, tau -> tau]
  assert(ftype >= 0);

  for (i=0; i<NFUNS; i++) {
    f = yices_new_uninterpreted_term(ftype);
    assert(f >= 0);
    if (i < NFNAMES) {
      name = fname[i];
    } else {
      sprintf(aux, "f%"PRIu32, i);
      name = aux;
    }
    code = yices_set_term_name(f, name);
    assert_true(code == 0);
    fun[i] = f;
  }
}

static void init_tables(void) {
  int32_t code;

  tau = yices_new_uninterpreted_type();
  code = yices_set_type_name(tau, "T");
  assert_true(code == 0);

  init_vars();
  init_funs();
}


/*
 * Random terms
 */
static term_t random_var(void) {
  return var[random() % NVARS];
}

static term_t random_fun(void) {
  return fun[random() % NFUNS];
}

// general form: build a term of type tau.
// d = max depth
static term_t random_term(uint32_t d) {
  term_t t, f;
  term_t aux[2];

  // random decrement on d
  while (d > 0) {
    if ((random() & 0x0300) != 0) break;
    d --;
  }

  if (d == 0) {
    t = random_var();
  } else {
    f = random_fun();
    aux[0] = random_term(d - 1);
    aux[1] = random_term(d - 1);
    t = yices_application(f, 2, aux);
  }

  assert(t >= 0);

  return t;
}




/*
 * Print [x --> t]
 */
static void show_map(FILE *f, term_t x, term_t t) {
  assert(x >= 0);

  fprintf(f, "[");
  print_term_name(f, __yices_globals.terms, x);
  fprintf(f, " --> ");
  if (t < 0) {
    fprintf(f, "nil");
  } else {
    print_term_full(f, __yices_globals.terms, t);
  }
  fprintf(f, "]");
}


/*
 * Print the map in subst
 */
// iterator: f is a FILE
static void show_map_record(void *f, const int_hmap_pair_t *p) {
  show_map(f, p->key, p->val);
  fputc('\n', f);
}

static void show_subst(FILE *f, full_subst_t *subst) {
  int_hmap_iterate(&subst->map, f, show_map_record);
  fprintf(f, "---\n\n");
  fflush(f);
}



/*
 * Add maps: test for cycles before each addition
 */
static void test_safe_add(full_subst_t *subst, term_t x, term_t val) {
  printf("testing: ");
  show_map(stdout, x, val);
  if (full_subst_check_map(subst, x, val)) {
    printf("   good\n");
    full_subst_add_map(subst, x, val);
  } else {
    printf("   skipped\n");
  }
}

static void test_safe_add_random(full_subst_t *subst) {
  term_t x, val;

  x = random_var();
  val = random_term(3);
  test_safe_add(subst, x, val);
}

static void test_safe_add_maps(full_subst_t *subst, uint32_t n) {
  while (n > 0) {
    n --;
    test_safe_add_random(subst);
  }
}


/*
 * Add maps: don't check for cycles
 * - but skip it if x is mapped
 */
static void test_add(full_subst_t *subst, term_t x, term_t val) {
  printf("adding: ");
  show_map(stdout, x, val);
  if (full_subst_is_mapped(subst, x)) {
    printf("   skipped\n");
  } else {
    printf("   done\n");
    full_subst_add_map(subst, x, val);
  }
}

static void test_add_random(full_subst_t *subst) {
  term_t x, val;

  x = random_var();
  val = random_term(3);
  test_add(subst, x, val);
}

static void test_add_maps(full_subst_t *subst, uint32_t n) {
  while (n > 0) {
    n --;
    test_add_random(subst);
  }
}


/*
 * Test: circular substitution: x_i --> x_i+1 and x_{NVARS-1} --> x_0
 */
static void test_circular(full_subst_t *subst) {
  term_t x, val;
  uint32_t i;

  for (i=0; i+1<NVARS; i++) {
    x = var[i];
    val = var[i+1];
    printf("testing: ");
    show_map(stdout, x, val);
    printf("\n");
    if (! full_subst_check_map(subst, x, val)) {
      printf("*** BUG: check_map returned false ***\n");
      fflush(stdout);
      exit(1);
    }
    full_subst_add_map(subst, x, val);
  }

  printf("\nVariable shift:\n");
  show_subst(stdout, subst);

  printf("\nTesting removing cycles\n");
  full_subst_remove_cycles(subst);
  show_subst(stdout, subst);

  // close the cycle
  x = var[NVARS-1];
  val = var[0];
  printf("testing: ");
  show_map(stdout, x, val);
  printf("\n");
  if (full_subst_check_map(subst, x, val)) {
    printf("*** BUG: check_map returned true (cycle present) ***\n");
    fflush(stdout);
    exit(1);
  }
  full_subst_add_map(subst, x, val);

  printf("\nCircular substitution\n");
  show_subst(stdout, subst);

  printf("\nAfter removing cycles\n");
  full_subst_remove_cycles(subst);
  show_subst(stdout, subst);
}


/*
 * Error code
 */
static void print_subst_error(FILE *f, int32_t code) {
  assert(code < 0);
  switch (code) {
  case FULL_SUBST_INTERNAL_ERROR:
    fprintf(f, "Internal error\n");
    break;

  case FULL_SUBST_DEGREE_OVERFLOW:
    fprintf(f, "Degree overflow\n");
    break;

  case FULL_SUBST_CYCLE:
    fprintf(f, "Cycle detected\n");
    break;

  default:
    fprintf(f, "Unexpected error code %"PRId32"\n", code);
    fflush(f);
    exit(1);
  }
}

/*
 * Apply subst to all variables
 */
static void test_apply_subst(full_subst_t *subst) {
  uint32_t i;
  term_t x, s;

  for (i=0; i<NVARS; i++) {
    x = var[i];
    printf("Test: apply_subst to ");
    print_term_name(stdout, __yices_globals.terms, x);
    printf("\n");
    s = full_subst_apply(subst, x);
    if (s < 0) {
      print_subst_error(stdout, s);
    } else {
      printf("result = ");
      print_term_full(stdout, __yices_globals.terms, s);
      printf("\n");
    }
    printf("\n");
  }
}



int main(void) {
  full_subst_t test;
  uint32_t i;

  yices_init();
  init_tables();

  printf("**********************************\n"
	 "* Testing circular substitution  *\n"
	 "**********************************\n");
  init_full_subst(&test, __yices_globals.manager);
  test_circular(&test);
  test_apply_subst(&test);
  delete_full_subst(&test);

  for (i=1; i<=3000; i++) {
    printf("**********************\n"
	   "*  Random test %-4"PRIu32"  *\n"
	   "**********************\n", i);
    init_full_subst(&test, __yices_globals.manager);
    printf("\nEmpty substitution:\n");
    show_subst(stdout, &test);
    test_apply_subst(&test);

    test_safe_add_maps(&test, 10);
    printf("\nContent\n");
    show_subst(stdout, &test);
    test_apply_subst(&test);

    test_add_maps(&test, 10);
    printf("\nContent\n");
    show_subst(stdout, &test);

    printf("\nRemoving cycles\n");
    full_subst_remove_cycles(&test);
    show_subst(stdout, &test);

    printf("\nDouble checking: should not change\n");
    full_subst_remove_cycles(&test);
    show_subst(stdout, &test);
    test_apply_subst(&test);

    delete_full_subst(&test);
  }

  yices_exit();

  return 0;
}
