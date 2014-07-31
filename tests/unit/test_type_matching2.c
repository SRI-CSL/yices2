/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>

#include "terms/types.h"
#include "io/type_printer.h"
#include "utils/refcount_strings.h"
#include "utils/int_vectors.h"

/*
 * GLOBAL VARIABLES
 */
#define NCONSTRUCTORS  2
#define NBASES         2
#define NVARS          3


static type_table_t types;

static type_t var[NVARS];
static type_t base[NBASES];
static int32_t constructor[NCONSTRUCTORS];

static ivector_t patterns;
static ivector_t tests;


/*
 * Initialize the tables
 */
// variables are X, Y, Z
static void init_variables(void) {
  var[0] = type_variable(&types, 0);
  set_type_name(&types, var[0], clone_string("X"));
  var[1] = type_variable(&types, 1);
  set_type_name(&types, var[1], clone_string("Y"));
  var[2] = type_variable(&types, 2);
  set_type_name(&types, var[2], clone_string("Z"));
}

// base types are int and real
static void init_base_types(void) {
  base[0] = int_type(&types);
  base[1] = real_type(&types);
}

// constructors: Set[X] and List[X]
static void init_constructors(void) {
  add_type_constructor(&types, clone_string("Set"), 1);
  constructor[0] = get_type_macro_by_name(&types, "Set");
  add_type_constructor(&types, clone_string("List"), 1);
  constructor[0] = get_type_macro_by_name(&types, "List");
}


/*
 * Patterns:
 * + the variabless
 * + apply the constructors to all variables
 * + tuple types with X Y Z
 * + function types with X Y Z
 */
static void init_patterns(void) {
  type_t aux[3];
  uint32_t i, j, k;

  init_ivector(&patterns, 40);

  // variables
  for (i=0; i<NVARS; i++) {
    ivector_push(&patterns, var[i]);
  }

  // constructors
  for (i=0; i<NCONSTRUCTORS; i++) {
    for (j=0; j<NVARS; j++) {
      ivector_push(&patterns, instance_type(&types, constructor[i], 1, &var[j]));
    }
  }

  // tuples (arity three)
  for (i=0; i<NVARS; i++) {
    for (j=0; j<NVARS; j++) {
      for (k=0; k<NVARS; k++) {
	aux[0] = var[i];
	aux[1] = var[j];
	aux[2] = var[k];
	ivector_push(&patterns, tuple_type(&types, 3, aux));
      }
    }
  }

  // tuples with variables + base type
  for (i=0; i<NBASES; i++) {
    for (j=0; j<NVARS; j++) {
      for (k=0; k<NVARS; k++) {
	aux[0] = base[i];
	aux[1] = var[j];
	aux[2] = var[k];
	ivector_push(&patterns, tuple_type(&types, 3, aux));

	aux[0] = var[j];
	aux[1] = base[i];
	aux[2] = var[k];
	ivector_push(&patterns, tuple_type(&types, 3, aux));

	aux[0] = var[j];
	aux[1] = var[k];
	aux[2] = base[i];
	ivector_push(&patterns, tuple_type(&types, 3, aux));
      }
    }
  }

  // function types
  for (i=0; i<NVARS; i++) {
    for (j=0; j<NVARS; j++) {
      for (k=0; k<NVARS; k++) {
	aux[0] = var[i];
	aux[1] = var[j];
	ivector_push(&patterns, function_type(&types, var[k], 2, aux));
      }
    }
  }

  // function types with fixed range
  for (i=0; i<NVARS; i++) {
    for (j=0; j<NVARS; j++) {
      for (k=0; k<NBASES; k++) {
	aux[0] = var[i];
	aux[1] = var[j];
	ivector_push(&patterns, function_type(&types, base[k], 2, aux));
      }
    }
  }
}


/*
 * Ground types used in tests
 */
static void init_tests(void) {
  type_t aux[3];
  uint32_t i, j, k;

  init_ivector(&tests, 40);

  // base types
  for (i=0; i<NBASES; i++) {
    ivector_push(&tests, base[i]);
  }

  // constructors
  for (i=0; i<NCONSTRUCTORS; i++) {
    for (j=0; j<NBASES; j++) {
      ivector_push(&tests, instance_type(&types, constructor[i], 1, &base[j]));
    }
  }

  // tuples
  for (i=0; i<NBASES; i++) {
    for (j=0; j<NBASES; j++) {
      for (k=0; k<NBASES; k++) {
	aux[0] = base[i];
	aux[1] = base[j];
	aux[2] = base[k];
	ivector_push(&tests, tuple_type(&types, 3, aux));
      }
    }
  }

  // function types
  for (i=0; i<NBASES; i++) {
    for (j=0; j<NBASES; j++) {
      for (k=0; k<NBASES; k++) {
	aux[0] = base[i];
	aux[1] = base[j];
	ivector_push(&tests, function_type(&types, base[k], 2, aux));
      }
    }
  }
}


/*
 * Show a matching
 */
static void show_matching(type_matcher_t *matcher) {
  uint32_t i, n;
  type_t x;

  n = matcher->nvars;
  for (i=0; i<n; i++) {
    x = matcher->var[i];
    assert(is_type_variable(&types, x));
    printf("    ");
    print_type(stdout, &types, x);
    printf(" := ");
    print_type(stdout, &types, matcher->map[i]);
    printf("\n");
  }
}


static void check_submatching(type_matcher_t *matcher, type_t pattern, type_t target) {
  type_t test;

  test = apply_type_matching(matcher, pattern);
  if (! is_subtype(&types, target, test)) {
    fprintf(stderr, "BUG: incorrect matching (expected subtype)\n");
    exit(1);
  }
}


/*
 * Test: solve constraints (tau[i] subtype of pattern[i])
 * - n = number of elements
 */
static void test_multi_matching(type_matcher_t *matcher, type_t *pattern, type_t *tau, uint32_t n) {
  uint32_t i;

  printf("Multiple subtype constraints\n");
  for (i=0; i<n; i++) {
    printf("  ");
    print_type(stdout, &types, tau[i]);
    printf(" subtype of ");
    print_type(stdout, &types, pattern[i]);
    printf("\n");
  }

  reset_type_matcher(matcher);
  for (i=0; i<n; i++) {
    if (! type_matcher_add_constraint(matcher, pattern[i], tau[i], false)) {
      printf("No match\n\n");
      return;
    }
  }

  type_matcher_build_subst(matcher);
  printf("Matching found:\n");
  show_matching(matcher);
  printf("\n");

  // check it
  for (i=0; i<n; i++) {
    check_submatching(matcher, pattern[i], tau[i]);
  }
}


/*
 * Filter: check whether tau and sigma have a chance of matching
 * - return true of tau is a variable
 *   or if the toplevel constructs in tau and sigma are equal
 */
static bool match_possible(type_t tau, type_t sigma) {
  type_kind_t ktau, ksigma;

  ktau = type_kind(&types, tau);
  ksigma = type_kind(&types, sigma);
  switch (ktau) {
  case VARIABLE_TYPE:
    return true;

  case INT_TYPE:
  case REAL_TYPE:
    return ksigma == INT_TYPE || ksigma == REAL_TYPE;

  default:
    return ktau == ksigma;
  }
}


/*
 * Full test
 */
static void all_tests(type_matcher_t *matcher) {
  uint32_t i, j, k, l;
  uint32_t npatterns, ntests;
  type_t pat[2];
  type_t tau[2];

  npatterns = patterns.size;
  ntests = tests.size;

  for (i=0; i<npatterns; i++) {
    pat[0] = patterns.data[i];
    for (k=0; k<ntests; k++) {
      tau[0] = tests.data[k];
      if (match_possible(pat[0], tau[0])) {
	for (j=0; j<npatterns; j++) {
	  pat[1] = patterns.data[j];
	  for (l=0; l<ntests; l++) {
	    tau[1] = tests.data[l];
	    if (match_possible(pat[1], tau[1])) {
	      test_multi_matching(matcher, pat, tau, 2);
	    }
	  }
	}
      }
    }
  }
}


int main(void) {
  type_matcher_t matcher;

  init_type_table(&types, 0);
  init_variables();
  init_base_types();
  init_constructors();
  init_patterns();
  init_tests();

  init_type_matcher(&matcher, &types);

  all_tests(&matcher);

  delete_type_matcher(&matcher);
  delete_ivector(&patterns);
  delete_ivector(&tests);
  delete_type_table(&types);

  return 0;
}
