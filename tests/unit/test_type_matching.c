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

#include "io/type_printer.h"
#include "terms/types.h"
#include "utils/refcount_strings.h"

#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif

/*
 * GLOBAL VARIABLES
 */
#define NVARS 6
#define NBASES 20
#define NCONST 3
#define NTYPES 500

static type_table_t types;
static type_t var[NVARS];
static type_t base[NBASES];
static int32_t constructor[NCONST];
static type_t sample[NTYPES];

/*
 * Short cuts for type construction
 */
static type_t binary_ftype(type_t dom1, type_t dom2, type_t range) {
  type_t a[2];

  a[0] = dom1;
  a[1] = dom2;
  return function_type(&types, range, 2, a);
}

static type_t ternary_ftype(type_t dom1, type_t dom2, type_t dom3, type_t range) {
  type_t a[3];

  a[0] = dom1;
  a[1] = dom2;
  a[2] = dom3;
  return function_type(&types, range, 3, a);
}

static type_t pair_type(type_t t1, type_t t2) {
  type_t a[2];

  a[0] = t1;
  a[1] = t2;
  return tuple_type(&types, 2, a);
}

static type_t triple_type(type_t t1, type_t t2, type_t t3) {
  type_t a[3];

  a[0] = t1;
  a[1] = t2;
  a[2] = t3;
  return tuple_type(&types, 3, a);
}

static type_t instance_type1(int32_t cid, type_t t1) {
  return instance_type(&types, cid, 1, &t1);
}

static type_t instance_type2(int32_t cid, type_t t1, type_t t2) {
  type_t a[2];

  a[0] = t1;
  a[1] = t2;
  return instance_type(&types, cid, 2, a);
}


/*
 * Initialize the type variables
 */
static void init_variables(void) {
  char name[2];
  uint32_t i;

  name[0] = 'A';
  name[1] = '\0';

  for (i=0; i<NVARS; i++) {
    var[i] = type_variable(&types, i);
    set_type_name(&types, var[i], clone_string(name));
    name[0] ++;
  }
}


/*
 * Check that cid has the given name and arity
 */
static void check_constructor(int32_t cid, uint32_t arity, const char *name) {
  type_macro_t *m;

  if (cid < 0) {
    fprintf(stderr, "BUG: incorrect constructor id\n");
    exit(1);
  }

  m = type_macro(&types, cid);
  if (strcmp(name, m->name) != 0 || m->arity != arity || m->body != NULL_TYPE) {
    fprintf(stderr, "BUG: incorrect macro descriptor for %s\n", name);
    exit(1);
  }
}


/*
 * Initialize the type constructors
 */
static void init_constructors(void) {
  add_type_constructor(&types, clone_string("Set"), 1);
  constructor[0] = get_type_macro_by_name(&types, "Set");
  check_constructor(constructor[0], 1, "Set");

  add_type_constructor(&types, clone_string("List"), 1);
  constructor[1] = get_type_macro_by_name(&types, "List");
  check_constructor(constructor[1], 1, "List");

  add_type_constructor(&types, clone_string("Map"), 2);
  constructor[2] = get_type_macro_by_name(&types, "Map");
  check_constructor(constructor[2], 2, "Map");
}


/*
 * Initialize the table of atomic types
 * - this must be called after init_variables
 */
static void init_base_types(void) {
  base[0] = bool_type(&types);
  base[1] = int_type(&types);
  base[2] = real_type(&types);
  base[3] = var[0];
  base[4] = var[1];
  base[5] = var[2];
  base[6] = var[3];
  base[7] = var[4];
  base[8] = var[5];
  base[9] = bv_type(&types, 8);
  base[10] = bv_type(&types, 32);
  base[11] = new_uninterpreted_type(&types);
  set_type_name(&types, base[11], clone_string("T1"));
  base[12] = new_uninterpreted_type(&types);
  set_type_name(&types, base[12], clone_string("T2"));
  base[13] = new_scalar_type(&types, 1);
  set_type_name(&types, base[13], clone_string("S1"));
  base[14] = new_scalar_type(&types, 100);
  set_type_name(&types, base[14], clone_string("S2"));

  base[15] = pair_type(var[5], var[5]);
  base[16] = pair_type(var[0], var[1]);
  base[17] = triple_type(var[0], var[1], var[0]);
  base[18] = instance_type2(constructor[2], var[3], var[3]);
  base[19] = binary_ftype(var[2], var[2], var[4]);
}


/*
 * Create a random new type by applying a type constructor
 * to existing types picked in a[0 ... n-1]
 */
// select k elements of a, store them in b[0 .. k-1]
static void select_random_types(type_t *b, uint32_t k, type_t *a, uint32_t n) {
  uint32_t i, j;

  for (i=0; i<k; i++) {
    j = random() % n;
    b[i] = a[j];
  }
}

// store k random types of the same constructor in b
static void random_types(type_t *b, uint32_t k, type_t *a, uint32_t n) {
  uint32_t i;
  type_t tau[4];

  switch (random() % 7) {
  case 0:
    for (i=0; i<k; i++) {
      select_random_types(tau, 3, a, n);
      b[i] = binary_ftype(tau[0], tau[1], tau[2]);
    }
    break;

  case 1:
    for (i=0; i<k; i++) {
      select_random_types(tau, 4, a, n);
      b[i] = ternary_ftype(tau[0], tau[1], tau[2], tau[3]);
    }
    break;

  case 2:
    for (i=0; i<k; i++) {
      select_random_types(tau, 2, a, n);
      b[i] = pair_type(tau[0], tau[1]);
    }
    break;

  case 3:
    for (i=0; i<k; i++) {
      select_random_types(tau, 3, a, n);
      b[i] = triple_type(tau[0], tau[1], tau[2]);
    }
    break;

  case 4:
    for (i=0; i<k; i++) {
      select_random_types(tau, 1, a, n);
      b[i] = instance_type1(constructor[0], tau[0]);
    }
    break;

  case 5:
    for (i=0; i<k; i++) {
      select_random_types(tau, 1, a, n);
      b[i] = instance_type1(constructor[1], tau[0]);
    }
    break;

  case 6:
    for (i=0; i<k; i++) {
      select_random_types(tau, 2, a, n);
      b[i] = instance_type2(constructor[2], tau[0], tau[1]);
    }
    break;
  }
}

// one random type
static type_t random_type(type_t *a, uint32_t n) {
  type_t result;

  random_types(&result, 1, a, n);
  return result;
}

// one random type variable
static type_t random_var(void) {
  uint32_t i;

  i = random() % NVARS;
  return var[i];
}

/*
 * Fill in the sample table
 */
static void init_samples(void) {
  uint32_t i, n;

  for (i=0; i<NBASES; i++) {
    sample[i] = base[i];
  }

  n = NBASES;
  while (i < NTYPES) {
    random_types(sample + i, 8, sample, n);
    i += 8;
    if (i > 3 * n) {
      n += n;
    }
  }

  printf("\n==== SAMPLES ====\n");
  for (i=0; i<NTYPES; i++) {
    printf("  ");
    print_type(stdout, &types, sample[i]);
    printf("\n");
  }
  printf("\n\n");
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


/*
 * Check that the matching works
 */
static void check_exact_matching(type_matcher_t *matcher, type_t pattern, type_t target) {
  type_t test;

  test = apply_type_matching(matcher, pattern);
  if (test != target) {
    fprintf(stderr, "BUG: incorrect matching (expected exact matching)\n");
    exit(1);
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
 * Test: check whether pattern and tau match
 * - if so apply the resulting substitution
 *   to all types in array sample
 */
static void test_exact_matching(type_matcher_t *matcher, type_t pattern, type_t target) {
  printf("Test exact matching\n");
  printf("  pattern: ");
  print_type(stdout, &types, pattern);
  printf("\n");
  printf("  target:  ");
  print_type(stdout, &types, target);
  printf("\n");

  reset_type_matcher(matcher);
  if (type_matcher_add_constraint(matcher, pattern, target, true)) {
    type_matcher_build_subst(matcher);
    printf("  Matching found:\n");
    show_matching(matcher);
    printf("\n");
    check_exact_matching(matcher, pattern, target);
  } else {
    printf("  No match\n\n");
  }
}


/*
 * Test2: apply a substitution to pattern to force matching to succeed
 */
static void test_forced_matching(type_matcher_t *matcher, type_t pattern) {
  type_t v[NVARS];
  type_t map[NVARS];
  type_t test;
  uint32_t i;

  for (i=0; i<NVARS; i++) {
    v[i] = var[i];
    map[i] = random_type(sample, NTYPES);
  }

  test = type_substitution(&types, pattern, NVARS, v, map);
  printf("Forced matching\n");
  printf("  pattern: ");
  print_type(stdout, &types, pattern);
  printf("\n");
  printf("  target:  ");
  print_type(stdout, &types, test);
  printf("\n");

  reset_type_matcher(matcher);
  if (type_matcher_add_constraint(matcher, pattern, test, true)) {
    type_matcher_build_subst(matcher);
    printf("  OK\n");
    show_matching(matcher);
    printf("\n");
  } else {
    fprintf(stderr, "BUG: matching failed\n");
    exit(1);
  }
}


/*
 * Test3: solve constraints (tau[i] subtype of pattern[i])
 * - n = number of elements
 */
static bool test_multi_matching(type_matcher_t *matcher, type_t *pattern, type_t *tau, uint32_t n) {
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
      return false;
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

  return true;
}


/*
 * Random tests of subtype matching
 * - n = number of tests
 * - p = array size (must be 5 or less)
 */
static void test_random_multi_vars(type_matcher_t *matcher, uint32_t n, uint32_t p) {
  type_t pattern[5];
  type_t tau[5];
  uint32_t i;

  assert(p <= 5);

  while (n > 0) {
    n--;
    for (i=0; i<p; i++) {
      pattern[i] = random_var();
      tau[i] = random_type(sample, 50);
    }
    test_multi_matching(matcher, pattern, tau, p);
  }
}

static void test_random_multi_patterns(type_matcher_t *matcher, uint32_t n, uint32_t p) {
  type_t pattern[5];
  type_t tau[5];
  uint32_t i;

  assert(p <= 5);

  while (n > 0) {
    n--;
    for (i=0; i<p; i++) {
      pattern[i] = random_type(sample, 50);
      tau[i] = random_type(sample, 50);
    }
    test_multi_matching(matcher, pattern, tau, p);
  }
}

static void test_random_multi_forced(type_matcher_t *matcher, uint32_t n, uint32_t p) {
  type_t v[NVARS];
  type_t map[NVARS];
  type_t pattern[5];
  type_t tau[5];
  uint32_t i;

  for (i=0; i<NVARS; i++) {
    v[i] = var[i];
    map[i] = random_type(sample, 30);
  }

  while (n > 0) {
    n --;

    for (i=0; i<NVARS; i++) {
      map[i] = random_type(sample, 30);
    }

    for (i=0; i<p; i++) {
      pattern[i] = random_type(sample, 30);
      tau[i] = type_substitution(&types, pattern[i], NVARS, v, map);
    }

    if (! test_multi_matching(matcher, pattern, tau, p)) {
      fprintf(stderr, "BUG: matching failed\n");
      exit(1);
    }
  }
}


int main(void) {
  type_matcher_t matcher;
  uint32_t i, j;
  type_t pattern;

  init_type_table(&types, 0);
  init_variables();
  init_constructors();
  init_base_types();
  init_samples();

  init_type_matcher(&matcher, &types);

  //  printf("\n===== TYPES =====\n");
  //  print_type_table(stdout, &types);
  //  printf("\n\n");

  for (i=0; i<NTYPES; i++) {
    pattern = sample[i];
    if (! ground_type(&types, pattern)) {
      test_forced_matching(&matcher, pattern);
      test_forced_matching(&matcher, pattern);
      for (j=0; j<NTYPES; j++) {
	test_exact_matching(&matcher, sample[i], sample[j]);
      }
      printf("---\n");
    }
  }

  test_random_multi_vars(&matcher, 20, 2);
  test_random_multi_vars(&matcher, 20, 3);
  test_random_multi_vars(&matcher, 20, 4);
  test_random_multi_vars(&matcher, 20, 5);

  test_random_multi_patterns(&matcher, 20, 2);
  test_random_multi_patterns(&matcher, 20, 3);
  test_random_multi_patterns(&matcher, 20, 4);
  test_random_multi_patterns(&matcher, 20, 5);

  test_random_multi_forced(&matcher, 20, 2);
  test_random_multi_forced(&matcher, 20, 3);
  test_random_multi_forced(&matcher, 20, 4);
  test_random_multi_forced(&matcher, 20, 5);

  delete_type_matcher(&matcher);
  delete_type_table(&types);

  return 0;
}
