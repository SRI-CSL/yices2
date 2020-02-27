/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2020 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * Force assert to work even if compiled with debug disabled
 */
#ifdef NDEBUG
# undef NDEBUG
#endif

#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>

#include "yices.h"

#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif


/*
 * Global types
 */
static type_t boolType = NULL_TYPE;
static type_t realType = NULL_TYPE;
static type_t intType = NULL_TYPE;

static void init_global_types(void) {
  boolType = yices_bool_type();
  realType = yices_real_type();
  intType = yices_int_type();
}


/*
 * Declare an uninterpreted of type tau:
 */
static term_t declare(const char *name, type_t tau) {
  term_t t;

  t = yices_new_uninterpreted_term(tau);
  assert(t >= 0);
  (void) yices_set_term_name(t, name);

  return t;
}

static term_t declare_bool(const char *name) {
  assert(boolType != NULL_TYPE);
  return declare(name, boolType);
}

static term_t declare_real(const char *name) {
  assert(realType != NULL_TYPE);
  return declare(name, realType);
}

static term_t declare_int(const char *name) {
  assert(intType != NULL_TYPE);
  return declare(name, intType);
}


/*
 * Declare some uninterpreted terms and store them in global arrays
 * - Boolean terms have names like "b0", "b1", etc
 *   reals have names like "x0", "x1", etc.
 *   integers have names like "i0", "i1", etc.
 */
#define N 10

static term_t boolVar[N];
static term_t realVar[N];
static term_t intVar[N];

static void declare_booleans(void) {
  char name[10];
  uint32_t i;

  for (i=0; i<N; i++) {
    snprintf(name, 10, "b%"PRIu32, i);
    boolVar[i] = declare_bool(name);
  }
}

static void declare_reals(void) {
  char name[10];
  uint32_t i;

  for (i=0; i<N; i++) {
    snprintf(name, 10, "x%"PRIu32, i);
    realVar[i] = declare_real(name);
  }
}

static void declare_integers(void) {
  char name[10];
  uint32_t i;

  for (i=0; i<N; i++) {
    snprintf(name, 10, "i%"PRIu32, i);
    intVar[i] = declare_int(name);
  }
}


/*
 * Constant terms
 */
static term_t random_bool_constant(void) {
  long x;
  x = random();
  if ((x & 0x800) == 0x800) {
    return yices_true();
  } else {
    return yices_false();
  } 
}

// random integer in [-n, n]
static term_t random_integer_constant(int32_t n) {
  int32_t x;

  x = (((int32_t) random()) % (2 * n + 1)) - n;
  return yices_int32(x);
}


/*
 * Build a model by assigning random values to the 3N variables
 */
static model_t *make_model(void) {
  term_t allVars[3 * N];
  term_t values[3 * N];
  uint32_t i;

  for (i=0; i<N; i++) {
    allVars[i] = boolVar[i];
    values[i] = random_bool_constant();
  }

  for (i=0; i<N; i++) {
    allVars[i+N] = realVar[i];
    values[i+N] = random_integer_constant(9);
  }

  for (i=0; i<N; i++) {
    allVars[i+2*N] = intVar[i];
    values[i+2*N] = random_integer_constant(9);
  }

  return yices_model_from_map(3*N, allVars, values);
}


/*
 * Collect & print support for term t in model m
 */
static void show_support(model_t *m, term_t t) {
  term_vector_t v;
  uint32_t i, n;
  int32_t c;

  yices_init_term_vector(&v);
  c = yices_model_term_support(m, t, &v);
  if (c < 0) {
    fprintf(stderr, "yices_model_term_support failed\n");
    yices_print_error(stderr);
    fprintf(stderr, "\nBUG\n");
    exit(1);
  }

  printf("Support for term ");
  yices_pp_term(stdout, t, 80, 10, 16);

  n = v.size;
  for (i=0; i<n; i++) {
    printf(" %s", yices_get_term_name(v.data[i]));
  }
  printf("\n");
  yices_pp_term_values(stdout, m, n, v.data, 80, 10, 0);

  yices_delete_term_vector(&v);
}


/*
 * Set of test terms
 */
#define NUM_TEST_TERMS 7

static const char *terms_to_parse[NUM_TEST_TERMS]  = {
  "x0",
  "false",
  "1/3",
  "(or b0 (and b1 b0 b2) (and b0 b3 (<= x1 0)))",
  "(or b5 (and b1 b0 b2) (and b4 b3 (<= x1 0)))",
  "(ite (> i2 0) (+ i2 i0 1) (+ i3 i4 15))",
  "(* x0 x1 x2 x4 x5)"
};

static term_t terms_to_test[NUM_TEST_TERMS];

static void init_terms_to_test(void) {
  uint32_t i;
  term_t t;

  for (i=0; i<NUM_TEST_TERMS; i++) {
    t = yices_parse_term(terms_to_parse[i]);
    if (t < 0) {
      fprintf(stderr, "yices_parser_term(%s)\n", terms_to_parse[i]);
      yices_print_error(stderr);
      fprintf(stderr, "\nBUG\n");
      exit(1);
    }
    terms_to_test[i] = t;
  }
}

  
int main(void) {
  model_t *m;
  uint32_t i, j;

  yices_init();

  init_global_types();
  declare_booleans();
  declare_reals();
  declare_integers();
  init_terms_to_test();
  
  for (i=0; i<10; i++) {
    m = make_model();
    printf("\n=== random model ===\n");
    yices_pp_model(stdout, m, 50, 50, 0);
    printf("\n");
    for (j=0; j<NUM_TEST_TERMS; j++) {
      show_support(m, terms_to_test[j]);
    }
    yices_free_model(m);
  }

  yices_exit();

  printf("All tests succeeded\n");
  return 0;
}
