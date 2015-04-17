/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of type macros
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
 * Display a macro
 */
static void show_macro(FILE *f, type_table_t *table, type_macro_t *d) {
  uint32_t i, n;

  if (d->body != NULL_TYPE) {
    fprintf(f, "macro %s[", d->name);
    n = d->arity;
    for (i=0; i<n; i++) {
      if (i > 0) fputs(", ", f);
      print_type(f, table, d->vars[i]);
    }
    fputs("] = ", f);
    print_type(f, table, d->body);
    fputc('\n', f);
  } else {
    fprintf(f, "constructor %s: arity %"PRIu32"\n", d->name, d->arity);
  }
}

/*
 * Print a cached instance
 */
static void print_macro_instance(FILE *f, type_table_t *types, tuple_hmap_rec_t *d) {
  char *name;
  type_mtbl_t *mtbl;
  uint32_t i, n;

  mtbl = types->macro_tbl;
  assert(d->arity > 0 && mtbl != NULL);

  name = type_macro_name(mtbl, d->key[0]);
  if (name != NULL) {
    fprintf(f, "%s[", name);
  } else {
    fprintf(f, "M_%"PRId32"[", d->key[0]);
  }

  n = d->arity;
  for (i=1; i<n; i++) {
    if (i > 1) fputs(", ", f);
    print_type(f, types, d->key[i]);
  }
  fputs("] = ", f);
  print_type(f, types, d->value);
  fputc('\n', f);
}

/*
 * Display all instances of macro id
 */
static void show_macro_instances(FILE *f, type_table_t *types, int32_t id) {
  type_mtbl_t *mtbl;
  char *name;
  tuple_hmap_t *cache;
  tuple_hmap_rec_t *d;
  uint32_t i, n;

  mtbl = types->macro_tbl;
  assert(mtbl != NULL);

  name = type_macro_name(mtbl, id);
  if (name != NULL) {
    fprintf(f, "Instances of macro %s (id = %"PRId32")\n", name, id);
  } else {
    fprintf(f, "Instances of macro M_%"PRId32"\n", id);
  }

  cache = &mtbl->cache;
  n = cache->size;
  for (i=0; i<n; i++) {
    d = cache->data[i];
    if (d != NULL && d != TUPLE_HMAP_DELETED && d->key[0] == id) {
      fputs("  ", f);
      print_macro_instance(f, types, d);
    }
  }
  fputs("----\n", f);
}



/*
 * GLOBAL VARIABLES
 */
#define NVARS 10
#define NTYPES 12

static type_table_t types;
static type_t var[NVARS];
static type_t base[NTYPES];

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
 * Create some types: this must be called after init_variables
 */
static void init_types(void) {
  base[0] = bool_type(&types);
  base[1] = int_type(&types);
  base[2] = real_type(&types);
  base[3] = var[0];
  base[4] = var[1];
  base[5] = var[2];
  base[6] = pair_type(base[1], base[1]);
  base[7] = triple_type(var[3], base[0], var[3]);
  base[8] = binary_ftype(base[2], base[2], base[0]);
  base[9] = binary_ftype(var[4], var[5], base[0]);
  base[10] = ternary_ftype(base[1], base[1], base[1], base[2]);
  base[11] = ternary_ftype(base[2], base[2], base[2], base[0]);
}


/*
 * Create a random instance of a macro
 * - id = macro id
 * - n = arity
 */
static void test_instance(int32_t id, uint32_t n) {
  type_t actual[n];
  uint32_t i, j;
  type_t result, check;

  for (i=0; i<n; i++) {
    j = random() % NTYPES;
    actual[i] = base[j];
  }

  printf("Test: instance of macro %"PRId32"\n", id);
  for (i=0; i<n; i++) {
    printf("  arg[%"PRIu32"] = ", i);
    print_type(stdout, &types, actual[i]);
    printf("\n");
  }
  result = instantiate_type_macro(&types, id, n, actual);
  printf("result = ");
  print_type(stdout, &types, result);
  printf("\n");

  check = instantiate_type_macro(&types, id, n, actual);
  if (check != result) {
    printf("BUG: hash-consing failure\n");
    fflush(stdout);
    exit(1);
  }
  printf("\n");
}

/*
 * Create a new macro: then create some random instances
 */
static void test_macro(const char *name, uint32_t n, type_t *vars, type_t body) {
  uint32_t i;
  int32_t id;

  printf("Test: create macro %s[", name);
  for (i=0; i<n; i++) {
    if (i > 0) fputs(", ", stdout);
    print_type(stdout, &types, vars[i]);
  }
  printf("] = ");
  print_type(stdout, &types, body);
  printf("\n");

  add_type_macro(&types, clone_string(name), n, vars, body);
  id = get_type_macro_by_name(&types, name);
  printf("Result: ");
  show_macro(stdout, &types, type_macro(&types, id));
  printf("\n");

  for (i=0; i<10; i++) {
    test_instance(id, n);
  }
  printf("----\n");
  show_macro_instances(stdout, &types, id);
  printf("\n");
}


/*
 * Create a new type constructor + some instances
 */
static void test_constructor(const char *name, uint32_t n) {
  int32_t id;
  uint32_t i;

  printf("Test: create constructor %s, arity %"PRIu32"\n", name, n);
  add_type_constructor(&types, clone_string(name), n);
  id = get_type_macro_by_name(&types, name);
  printf("Result: ");
  show_macro(stdout, &types, type_macro(&types, id));
  printf("\n");

  for (i=0; i<10; i++) {
    test_instance(id, n);
  }
}



int main(void) {
  type_t tau;

  init_type_table(&types, 0);
  init_variables();
  init_types();

  // pair(A) = (tuple A A)
  tau = pair_type(var[0], var[0]);
  test_macro("pair", 1, var, tau);

  // triple(B) = (tuple B B B)
  tau = triple_type(var[1], var[1], var[1]);
  test_macro("triple", 1, var+1, tau);

  // test(C, D) = bool
  test_macro("test", 2, var+2, base[0]);

  // fun(E, F) = (-> (tuple E E) F)
  tau = pair_type(var[4], var[4]);
  tau = function_type(&types, var[5], 1, &tau);
  test_macro("fun", 2, var+4, tau);

  // two constructors
  test_constructor("mk_type2", 2);
  test_constructor("mk_type3", 3);

  printf("\n====== TYPES ========\n");
  print_type_table(stdout, &types);
  printf("\n===== MACROS ========\n");
  print_type_macros(stdout, &types);
  printf("===\n\n");

  // creation after remove
  // vector[G] = (-> int G)
  tau = int_type(&types);
  tau = function_type(&types, var[6], 1, &tau);
  test_macro("vector", 1, var+6, tau);

  // matrix[H] = (-> int int H)
  tau = int_type(&types);
  tau = binary_ftype(tau, tau, var[7]);
  test_macro("matrix", 1, var+7, tau);

  printf("\n====== TYPES ========\n");
  print_type_table(stdout, &types);
  printf("\n===== MACROS ========\n");
  print_type_macros(stdout, &types);
  printf("===\n\n");

  delete_type_table(&types);

  return 0;
}
