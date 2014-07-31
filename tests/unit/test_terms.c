/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test term table:
 * - hash consing
 * - term names
 * - garbage collection
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <inttypes.h>

#include "utils/refcount_strings.h"
#include "terms/pprod_table.h"
#include "terms/bv_constants.h"
#include "terms/bv64_constants.h"
#include "terms/types.h"
#include "terms/terms.h"

#include "io/term_printer.h"
#include "io/type_printer.h"


/*
 * Global tables + stores for arith, bv, bv64 buffers
 */
static pprod_table_t pprods;
static type_table_t types;
static term_table_t terms;
static object_store_t bvmlist_store;
static object_store_t bvmlist64_store;


/*
 * Initialize the tables
 */
static void init_globals(void) {
  init_pprod_table(&pprods, 10);
  init_type_table(&types, 10);
  init_term_table(&terms, 10, &types, &pprods);
  init_bvmlist_store(&bvmlist_store);
  init_bvmlist64_store(&bvmlist64_store);
  init_rationals();
  init_bvconstants();
}


/*
 * Delete them
 */
static void delete_globals(void) {
  delete_term_table(&terms);
  delete_type_table(&types);
  delete_pprod_table(&pprods);
  delete_bvmlist_store(&bvmlist_store);
  delete_bvmlist64_store(&bvmlist64_store);
  cleanup_rationals();
  cleanup_bvconstants();
}



/*
 * TYPES
 */

/*
 * A fixed set of types
 */
#define MAX_TYPES 100

static type_t type[MAX_TYPES];
static uint32_t num_types;


/*
 * Add tau to the set of types
 * - name = optional name (NULL means no name)
 */
static void add_type(type_t tau, char *name) {
  uint32_t i;

  i = num_types;
  if (i < MAX_TYPES) {
    type[i] = tau;
    num_types = i+1;
  }

  if (name != NULL) {
    set_type_name(&types, tau, clone_string(name));
  }
}


/*
 * Short cuts
 */
static type_t fun_type1(type_t dom, type_t range) {
  return function_type(&types, range, 1, &dom);
}

static type_t fun_type2(type_t dom1, type_t dom2, type_t range) {
  type_t aux[2];

  aux[0] = dom1;
  aux[1] = dom2;
  return function_type(&types, range, 2, aux);
}

static type_t tup_type1(type_t t1) {
  return tuple_type(&types, 1, &t1);
}

static type_t tup_type2(type_t t1, type_t t2) {
  type_t aux[2];

  aux[0] = t1;
  aux[1] = t2;
  return tuple_type(&types, 2, aux);
}

static type_t tup_type3(type_t t1, type_t t2, type_t t3) {
  type_t aux[3];

  aux[0] = t1;
  aux[1] = t2;
  aux[2] = t3;
  return tuple_type(&types, 3, aux);
}


/*
 * Build the initial types
 */
static void init_global_types(void) {
  num_types = 0;

  add_type(bool_type(&types), NULL);  // 0
  add_type(int_type(&types), NULL);   // 1
  add_type(real_type(&types), NULL);  // 2

  add_type(bv_type(&types, 1), "bv1");  // 3
  add_type(bv_type(&types, 6), "bv6");  // 4
  add_type(bv_type(&types, 63), "bv63");  // 5
  add_type(bv_type(&types, 64), "bv64");  // 6
  add_type(bv_type(&types, 65), "bv65");  // 7

  add_type(new_uninterpreted_type(&types), "T1");  // 8
  add_type(new_uninterpreted_type(&types), "T2");  // 9
  add_type(new_scalar_type(&types, 5), "E1");      // 10
  add_type(new_scalar_type(&types, 100), "E2");    // 11
  add_type(new_scalar_type(&types, 1), "U1");      // 12
  add_type(new_scalar_type(&types, 1), "U2");      // 13

  add_type(fun_type1(type[0], type[3]), NULL);   // 14: [bool -> bv1]
  add_type(fun_type2(type[1], type[1], type[1]), NULL); // 15: [int, int -> int]
  add_type(fun_type1(type[8], type[9]), NULL);   // 16: [T1 -> T2]
  add_type(fun_type1(type[2], type[12]), NULL);  // 17: [real -> U1]

  add_type(tup_type1(type[4]), NULL);             // 18: [bv6]
  add_type(tup_type2(type[1], type[2]), NULL);    // 19: [int, real]
  add_type(tup_type2(type[12], type[13]), NULL);  // 20: [U1, U2]
  add_type(tup_type3(type[8], type[0], type[0]), NULL);    // 21: [T1, bool, bool)
  add_type(tup_type3(type[11], type[11], type[11]), NULL); // 22: [E2, E2, E2]
}





/*
 * CONSTRUCTOR TESTS
 */

/*
 * Check whether term x matches (tag, tau, index)
 */
static bool check_term_integer(term_t x, term_kind_t tag, type_t tau, int32_t index) {
  int32_t i;

  i = index_of(x);
  return kind_for_idx(&terms, i) == tag && type_for_idx(&terms, i) == tau &&
    integer_value_for_idx(&terms, i) == index && is_pos_term(x);
}


/*
 * Check whether x matches binary composite defined by (tag, tau, a, ..,)
 */
static bool check_composite1(term_t x, term_kind_t tag, type_t tau, term_t a) {
  composite_term_t *p;
  int32_t i;

  i = index_of(x);
  p = composite_for_idx(&terms, i);
  return kind_for_idx(&terms, i) == tag && type_for_idx(&terms, i) == tau &&
    p->arity == 1 && p->arg[0] == a;
}

static bool check_composite2(term_t x, term_kind_t tag, type_t tau, term_t a, term_t b) {
  composite_term_t *p;
  int32_t i;

  i = index_of(x);
  p = composite_for_idx(&terms, i);
  return kind_for_idx(&terms, i) == tag && type_for_idx(&terms, i) == tau &&
    p->arity == 2 && p->arg[0] == a && p->arg[1] == b;
}

static bool check_composite3(term_t x, term_kind_t tag, type_t tau, term_t a, term_t b, term_t c) {
  composite_term_t *p;
  int32_t i;

  i = index_of(x);
  p = composite_for_idx(&terms, i);
  return kind_for_idx(&terms, i) == tag && type_for_idx(&terms, i) == tau &&
    p->arity == 3 && p->arg[0] == a && p->arg[1] == b && p->arg[2] == c;
}

static bool check_composite4(term_t x, term_kind_t tag, type_t tau, term_t a, term_t b, term_t c, term_t d) {
  composite_term_t *p;
  int32_t i;

  i = index_of(x);
  p = composite_for_idx(&terms, i);
  return kind_for_idx(&terms, i) == tag && type_for_idx(&terms, i) == tau &&
    p->arity == 4 && p->arg[0] == a && p->arg[1] == b && p->arg[2] == c && p->arg[3] == d;
}


/*
 * Same thing for (select k a)
 */
static bool check_select(term_t x, term_kind_t tag, type_t tau, term_t a, uint32_t k) {
  select_term_t *p;
  int32_t i;

  i = index_of(x);
  p = select_for_idx(&terms, i);
  return kind_for_idx(&terms, i) == tag && type_for_idx(&terms, i) == tau && p->idx == k && p->arg == a;
}


/*
 * Report bug and abort
 */
static void constructor_failed(void) {
  printf("BUG: constructor failed\n");
  fflush(stdout);
  abort();
}

static void hash_consing_failed(void) {
  printf("BUG: hash consing failed\n");
  fflush(stdout);
  abort();
}


/*
 * Test term constructors
 * - each test function builds a term
 * - check that the term descriptor and type are correct
 * - call the constructor twice to check whether hash-consing works
 * - add the name if
 */
static term_t test_constant_term(type_t tau, int32_t index, char *name) {
  term_t x, y;

  printf("Testing: constant %"PRId32" of type ", index);
  print_type_name(stdout, &types, tau);
  printf(": ");

  x = constant_term(&terms, tau, index);
  if (! check_term_integer(x, CONSTANT_TERM, tau, index)) {
    constructor_failed();
  }

  y = constant_term(&terms, tau, index);
  if (x != y) {
    hash_consing_failed();
  }

  // give the name
  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_uninterpreted_term(type_t tau, char *name) {
  term_t x;
  int32_t i;

  printf("Testing: uninterpreted term of type ");
  print_type_name(stdout, &types, tau);
  printf(": ");

  x = new_uninterpreted_term(&terms, tau);
  i = index_of(x);
  if (kind_for_idx(&terms, i) != UNINTERPRETED_TERM ||
      type_for_idx(&terms, i) != tau ||
      is_neg_term(x)) {
    constructor_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}


static term_t test_variable(type_t tau, char *name) {
  term_t x;

  printf("Testing: variable of type ");
  print_type_name(stdout, &types, tau);
  printf(": ");

  x = new_variable(&terms, tau);
  if (! check_term_integer(x, VARIABLE, tau, index_of(x))) {
    constructor_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_not(term_t a, char *name) {
  term_t x, y;

  printf("Testing: (not ");
  print_term_name(stdout, &terms, a);
  printf("): ");

  x = not_term(&terms, a);
  if (x != opposite_term(a)) {
    constructor_failed();
  }

  y = not_term(&terms, x);
  if (y != a) {
    printf("BUG: (neg (neg a)) != a\n");
    fflush(stdout);
    abort();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}


/*
 * constructor ite_term(.., a. b, c) may build ITE_TERM or ITE_SPECIAL, depending
 * on the tags for b and c:
 */
static bool special_for_ite(term_t x) {
  term_kind_t tag;
  tag = term_kind(&terms, x);
  return tag == ITE_SPECIAL || is_const_kind(tag);
}


static term_t test_ite(type_t tau, term_t a, term_t b, term_t c, char *name) {
  term_t x, y;
  term_kind_t expected_tag;

  printf("Testing: (ite ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf(" ");
  print_term_name(stdout, &terms, c);
  printf("): ");

  x = ite_term(&terms, tau, a, b, c);
  expected_tag = ITE_TERM;
  if (special_for_ite(b) && special_for_ite(c)) {
    expected_tag = ITE_SPECIAL;
  }

  if (! check_composite3(x, expected_tag, tau, a, b, c)) {
    constructor_failed();
  }

  y = ite_term(&terms, tau, a, b, c);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_app1(type_t tau, term_t fun, term_t a, char *name) {
  term_t aux[1];
  term_t x, y;

  aux[0] = a;

  printf("Testing: (app ");
  print_term_name(stdout, &terms, fun);
  printf(" ");
  print_term_name(stdout, &terms, a);
  printf("): ");

  x = app_term(&terms, fun, 1, aux);
  if (! check_composite2(x, APP_TERM, tau, fun, a)) {
    constructor_failed();
  }

  y = app_term(&terms, fun, 1, aux);
  if (x != y) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_app2(type_t tau, term_t fun, term_t a, term_t b, char *name) {
  term_t aux[2];
  term_t x, y;

  aux[0] = a;
  aux[1] = b;

  printf("Testing: (app ");
  print_term_name(stdout, &terms, fun);
  printf(" ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf("): ");

  x = app_term(&terms, fun, 2, aux);
  if (! check_composite3(x, APP_TERM, tau, fun, a, b)) {
    constructor_failed();
  }

  y = app_term(&terms, fun, 2, aux);
  if (x != y) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_update1(type_t tau, term_t fun, term_t a, term_t v, char *name) {
  term_t aux[1];
  term_t x, y;

  aux[0] = a;

  printf("Testing: (update ");
  print_term_name(stdout, &terms, fun);
  printf(" (");
  print_term_name(stdout, &terms, a);
  printf(") ");
  print_term_name(stdout, &terms, v);
  printf("): ");

  x = update_term(&terms, fun, 1, aux, v);
  if (! check_composite3(x, UPDATE_TERM, tau, fun, a, v)) {
    constructor_failed();
  }

  y = update_term(&terms, fun, 1, aux, v);
  if (x != y) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_update2(type_t tau, term_t fun, term_t a, term_t b, term_t v, char *name) {
  term_t aux[2];
  term_t x, y;

  aux[0] = a;
  aux[1] = b;

  printf("Testing: (update ");
  print_term_name(stdout, &terms, fun);
  printf(" (");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf(") ");
  print_term_name(stdout, &terms, v);
  printf("): ");

  x = update_term(&terms, fun, 2, aux, v);
  if (! check_composite4(x, UPDATE_TERM, tau, fun, a, b, v)) {
    constructor_failed();
  }

  y = update_term(&terms, fun, 2, aux, v);
  if (x != y) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_tuple1(type_t tau, term_t a, char *name) {
  term_t aux[1];
  term_t x, y;

  aux[0] = a;

  printf("Testing: (tuple ");
  print_term_name(stdout, &terms, a);
  printf("): ");

  x = tuple_term(&terms, 1, aux);
  if (! check_composite1(x, TUPLE_TERM, tau, a)) {
    constructor_failed();
  }

  y = tuple_term(&terms, 1, aux);
  if (x != y) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_tuple2(type_t tau, term_t a, term_t b, char *name) {
  term_t aux[2];
  term_t x, y;

  aux[0] = a;
  aux[1] = b;

  printf("Testing: (tuple ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf("): ");

  x = tuple_term(&terms, 2, aux);
  if (! check_composite2(x, TUPLE_TERM, tau, a, b)) {
    constructor_failed();
  }

  y = tuple_term(&terms, 2, aux);
  if (x != y) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_select(type_t tau, term_t a, uint32_t k, char *name) {
  term_t x, y;


  printf("Testing: (select %"PRIu32" ",k);
  print_term_name(stdout, &terms, a);
  printf("): ");

  x = select_term(&terms, k, a);
  if (! check_select(x, SELECT_TERM, tau, a, k)) {
    constructor_failed();
  }

  y = select_term(&terms, k, a);
  if (x != y) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_eq(term_t a, term_t b, char *name) {
  term_t x, y;

  printf("Testing: (eq ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf("): ");

  x = eq_term(&terms, a, b);
  if (! check_composite2(x, EQ_TERM, bool_type(&types), a, b)) {
    constructor_failed();
  }

  y = eq_term(&terms, a, b);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_distinct4(term_t a, term_t b, term_t c, term_t d, char *name) {
  term_t aux[4];
  term_t x, y;

  aux[0] = a;
  aux[1] = b;
  aux[2] = c;
  aux[3] = d;

  printf("Testing: (distinct ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf(" ");
  print_term_name(stdout, &terms, c);
  printf(" ");
  print_term_name(stdout, &terms, d);
  printf("): ");

  x = distinct_term(&terms, 4, aux);
  if (! check_composite4(x, DISTINCT_TERM, bool_type(&types), a, b, c, d)) {
    constructor_failed();
  }

  y = distinct_term(&terms, 4, aux);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_forall2(term_t a, term_t b, term_t c, char *name) {
  term_t aux[2];
  term_t x, y;

  aux[0] = a;
  aux[1] = b;

  printf("Testing: (forall (");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf(") ");
  print_term_name(stdout, &terms, c);
  printf("): ");

  x = forall_term(&terms, 2, aux, c);
  if (! check_composite3(x, FORALL_TERM, bool_type(&types), a, b, c)) {
    constructor_failed();
  }

  y = forall_term(&terms, 2, aux, c);
  if (x != y) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_lambda2(type_t tau, term_t a, term_t b, term_t c, char *name) {
  term_t aux[2];
  term_t x, y;

  aux[0] = a;
  aux[1] = b;

  printf("Testing: (lambda (");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf(") ");
  print_term_name(stdout, &terms, c);
  printf("): ");

  x = lambda_term(&terms, 2, aux, c);
  if (! check_composite3(x, LAMBDA_TERM, tau, a, b, c)) {
    constructor_failed();
  }

  y = lambda_term(&terms, 2, aux, c);
  if (x != y) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_or2(term_t a, term_t b, char *name) {
  term_t aux[2];
  term_t x, y;

  aux[0] = a;
  aux[1] = b;

  printf("Testing: (or ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf("): ");

  x = or_term(&terms, 2, aux);
  if (! check_composite2(x, OR_TERM, bool_type(&types), a, b)) {
    constructor_failed();
  }

  y = or_term(&terms, 2, aux);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_xor3(term_t a, term_t b, term_t c, char *name) {
  term_t aux[3];
  term_t x, y;

  aux[0] = a;
  aux[1] = b;
  aux[2] = c;

  printf("Testing: (xor ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf(" ");
  print_term_name(stdout, &terms, c);
  printf("): ");

  x = xor_term(&terms, 3, aux);
  if (! check_composite3(x, XOR_TERM, bool_type(&types), a, b, c)) {
    constructor_failed();
  }

  y = xor_term(&terms, 3, aux);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_bit(term_t a, uint32_t k, char *name) {
  term_t x, y;

  printf("Testing: (bit %"PRIu32" ",k);
  print_term_name(stdout, &terms, a);
  printf("): ");

  x = bit_term(&terms, k, a);
  if (! check_select(x, BIT_TERM, bool_type(&types), a, k)) {
    constructor_failed();
  }

  y = bit_term(&terms, k, a);
  if (x != y) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_arith_eq(term_t a, char *name) {
  term_t x, y;

  printf("Testing: (arith-eq ");
  print_term_name(stdout, &terms, a);
  printf(" 0): ");

  x = arith_eq_atom(&terms, a);
  if (! check_term_integer(x, ARITH_EQ_ATOM, bool_type(&types), a)) {
    constructor_failed();
  }

  y = arith_eq_atom(&terms, a);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_arith_geq(term_t a, char *name) {
  term_t x, y;

  printf("Testing: (arith-geq ");
  print_term_name(stdout, &terms, a);
  printf(" 0): ");

  x = arith_geq_atom(&terms, a);
  if (! check_term_integer(x, ARITH_GE_ATOM, bool_type(&types), a)) {
    constructor_failed();
  }

  y = arith_geq_atom(&terms, a);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_arith_bineq(term_t a, term_t b, char *name) {
  term_t x, y;

  printf("Testing: (arith-bineq ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf("): ");

  x = arith_bineq_atom(&terms, a, b);
  if (! check_composite2(x, ARITH_BINEQ_ATOM, bool_type(&types), a, b)) {
    constructor_failed();
  }

  y = arith_bineq_atom(&terms, a, b);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_bvarray4(term_t a, term_t b, term_t c, term_t d, char *name) {
  term_t aux[4];
  term_t x, y;

  aux[0] = a;
  aux[1] = b;
  aux[2] = c;
  aux[3] = d;

  printf("Testing: (bvarray ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf(" ");
  print_term_name(stdout, &terms, c);
  printf(" ");
  print_term_name(stdout, &terms, d);
  printf("): ");

  x = bvarray_term(&terms, 4, aux);
  if (! check_composite4(x, BV_ARRAY, bv_type(&types, 4), a, b, c, d)) {
    constructor_failed();
  }

  y = bvarray_term(&terms, 4, aux);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_bvdiv(type_t tau, term_t a, term_t b, char *name) {
  term_t x, y;

  printf("Testing: (bvdiv ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf("): ");

  x = bvdiv_term(&terms, a, b);
  if (! check_composite2(x, BV_DIV, tau, a, b)) {
    constructor_failed();
  }

  y = bvdiv_term(&terms, a, b);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_bvrem(type_t tau, term_t a, term_t b, char *name) {
  term_t x, y;

  printf("Testing: (bvrem ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf("): ");

  x = bvrem_term(&terms, a, b);
  if (! check_composite2(x, BV_REM, tau, a, b)) {
    constructor_failed();
  }

  y = bvrem_term(&terms, a, b);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_bvsdiv(type_t tau, term_t a, term_t b, char *name) {
  term_t x, y;

  printf("Testing: (bvsdiv ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf("): ");

  x = bvsdiv_term(&terms, a, b);
  if (! check_composite2(x, BV_SDIV, tau, a, b)) {
    constructor_failed();
  }

  y = bvsdiv_term(&terms, a, b);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_bvsrem(type_t tau, term_t a, term_t b, char *name) {
  term_t x, y;

  printf("Testing: (bvsrem ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf("): ");

  x = bvsrem_term(&terms, a, b);
  if (! check_composite2(x, BV_SREM, tau, a, b)) {
    constructor_failed();
  }

  y = bvsrem_term(&terms, a, b);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_bvsmod(type_t tau, term_t a, term_t b, char *name) {
  term_t x, y;

  printf("Testing: (bvsmod ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf("): ");

  x = bvsmod_term(&terms, a, b);
  if (! check_composite2(x, BV_SMOD, tau, a, b)) {
    constructor_failed();
  }

  y = bvsmod_term(&terms, a, b);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_bvshl(type_t tau, term_t a, term_t b, char *name) {
  term_t x, y;

  printf("Testing: (bvshl ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf("): ");

  x = bvshl_term(&terms, a, b);
  if (! check_composite2(x, BV_SHL, tau, a, b)) {
    constructor_failed();
  }

  y = bvshl_term(&terms, a, b);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_bvlshr(type_t tau, term_t a, term_t b, char *name) {
  term_t x, y;

  printf("Testing: (bvlshr ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf("): ");

  x = bvlshr_term(&terms, a, b);
  if (! check_composite2(x, BV_LSHR, tau, a, b)) {
    constructor_failed();
  }

  y = bvlshr_term(&terms, a, b);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_bvashr(type_t tau, term_t a, term_t b, char *name) {
  term_t x, y;

  printf("Testing: (bvashr ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf("): ");

  x = bvashr_term(&terms, a, b);
  if (! check_composite2(x, BV_ASHR, tau, a, b)) {
    constructor_failed();
  }

  y = bvashr_term(&terms, a, b);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_bveq(term_t a, term_t b, char *name) {
  term_t x, y;

  printf("Testing: (bveq ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf("): ");

  x = bveq_atom(&terms, a, b);
  if (! check_composite2(x, BV_EQ_ATOM, bool_type(&types), a, b)) {
    constructor_failed();
  }

  y = bveq_atom(&terms, a, b);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_bvge(term_t a, term_t b, char *name) {
  term_t x, y;

  printf("Testing: (bvge ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf("): ");

  x = bvge_atom(&terms, a, b);
  if (! check_composite2(x, BV_GE_ATOM, bool_type(&types), a, b)) {
    constructor_failed();
  }

  y = bvge_atom(&terms, a, b);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_bvsge(term_t a, term_t b, char *name) {
  term_t x, y;

  printf("Testing: (bvsge ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf("): ");

  x = bvsge_atom(&terms, a, b);
  if (! check_composite2(x, BV_SGE_ATOM, bool_type(&types), a, b)) {
    constructor_failed();
  }

  y = bvsge_atom(&terms, a, b);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}



/*
 * Rational constants
 */
static bool check_rational(term_t x, rational_t *a) {
  type_t tau;
  int32_t i;

  tau = real_type(&types);
  if (q_is_integer(a)) {
    tau = int_type(&types);
  }

  i = index_of(x);
  return kind_for_idx(&terms, i) == ARITH_CONSTANT && type_for_idx(&terms, i) == tau &&
    q_eq(a, rational_for_idx(&terms, i)) && is_pos_term(x);
}

static void test_rationals(void) {
  rational_t a;
  term_t x, y;

  q_init(&a);
  q_set_int32(&a, 1, 3);

  printf("Testing: rational ");
  q_print(stdout, &a);
  printf(": ");

  x = arith_constant(&terms, &a);
  if (! check_rational(x, &a)) {
    constructor_failed();
  }

  y  = arith_constant(&terms, &a);
  if (y != x) {
    hash_consing_failed();
  }

  print_term(stdout, &terms, x);
  printf("\n");

  q_set_int32(&a, -3, 1);

  printf("Testing: rational ");
  q_print(stdout, &a);
  printf(": ");

  x = arith_constant(&terms, &a);
  if (! check_rational(x, &a)) {
    constructor_failed();
  }

  y  = arith_constant(&terms, &a);
  if (y != x) {
    hash_consing_failed();
  }

  print_term(stdout, &terms, x);
  printf("\n");

  q_clear(&a);
}


/*
 * Polynomials
 */
static bool check_polynomial(term_t x, type_t tau) {
  int32_t i;

  i = index_of(x);
  return kind_for_idx(&terms, i) == ARITH_POLY && type_for_idx(&terms, i) == tau
    && is_pos_term(x);
}

static void test_polynomials(void) {
  rba_buffer_t buffer1;
  rba_buffer_t buffer2;
  rational_t a;
  term_t x, y, s, t;
  pprod_t *r0;

  init_rba_buffer(&buffer1, &pprods);
  init_rba_buffer(&buffer2, &pprods);
  q_init(&a);

  // integer polynomial: x + 3 x y + 1
  x = test_uninterpreted_term(int_type(&types), "xx");
  y = test_uninterpreted_term(int_type(&types), "yy");
  rba_buffer_add_var(&buffer1, x);
  r0 = pprod_mul(&pprods, var_pp(x), var_pp(y)); // x * y
  q_set_int32(&a, 3, 1);
  rba_buffer_add_mono(&buffer1, &a, r0);
  q_set_int32(&a, 1, 1);
  rba_buffer_add_const(&buffer1, &a);

  rba_buffer_add_buffer(&buffer2, &buffer1); // make a copy
  assert(rba_buffer_equal(&buffer1, &buffer2));

  printf("Testing: ");
  print_arith_buffer(stdout, &buffer1);
  printf(": ");

  s = arith_poly(&terms, &buffer1);
  if (! check_polynomial(s, int_type(&types))) {
    constructor_failed();
  }

  t = arith_poly(&terms, &buffer2);
  if (t != s) {
    hash_consing_failed();
  }

  print_term(stdout, &terms, s);
  printf("\n");

  // real polynomial x + y - 1/2
  reset_rba_buffer(&buffer1);
  reset_rba_buffer(&buffer2);
  rba_buffer_add_var(&buffer1, x);
  rba_buffer_add_var(&buffer1, y);
  q_set_int32(&a, -1, 2);
  rba_buffer_add_const(&buffer1, &a);
  printf("Testing: ");
  print_arith_buffer(stdout, &buffer1);
  printf(": ");

  rba_buffer_add_buffer(&buffer2, &buffer1); // make a copy
  assert(rba_buffer_equal(&buffer1, &buffer2));

  s = arith_poly(&terms, &buffer1);
  if (! check_polynomial(s, real_type(&types))) {
    constructor_failed();
  }

  t = arith_poly(&terms, &buffer2);
  if (t != s) {
    hash_consing_failed();
  }

  print_term(stdout, &terms, s);
  printf("\n");

  q_clear(&a);
  delete_rba_buffer(&buffer1);
  delete_rba_buffer(&buffer2);
  printf("\n");
}


/*
 * Bitvector constants
 */
static bool check_bvconst(term_t x, uint32_t *bv, uint32_t n) {
  bvconst_term_t *d;
  type_t tau;
  int32_t i;
  uint32_t k;

  tau = bv_type(&types, n);
  i = index_of(x);
  k = (n + 31) >> 5;
  d = bvconst_for_idx(&terms, i);
  return kind_for_idx(&terms, i) == BV_CONSTANT && type_for_idx(&terms, i) == tau &&
    d->bitsize == n && bvconst_eq(d->data, bv, k);
}

static void test_bvconst(void) {
  uint32_t bv[4];
  term_t x, y;

  bv[0] = 0x55555555;
  bv[1] = 1;
  bv[2] = 1;
  bv[3] = 0;
  bvconst_normalize(bv, 66);
  printf("Testing bitvector constant: ");
  bvconst_print(stdout, bv, 66);
  printf(": ");

  x = bvconst_term(&terms, 66, bv);
  if (! check_bvconst(x, bv, 66)) {
    constructor_failed();
  }

  y = bvconst_term(&terms, 66, bv);
  if (y != x) {
    hash_consing_failed();
  }

  print_term(stdout, &terms, x);
  printf("\n");
}


/*
 * Bitvector polynomials
 */
static bool check_bvpoly(term_t x, uint32_t n) {
  int32_t i;
  type_t tau;

  i = index_of(x);
  tau = bv_type(&types, n);
  return kind_for_idx(&terms, i) == BV_POLY && type_for_idx(&terms, i) == tau
    && is_pos_term(x);
}

static void test_bvpoly(void) {
  bvarith_buffer_t buffer1;
  bvarith_buffer_t buffer2;
  uint32_t bv[4];
  type_t tau;
  term_t x, y, s, t;
  pprod_t *r0;

  init_bvarith_buffer(&buffer1, &pprods, &bvmlist_store);
  init_bvarith_buffer(&buffer2, &pprods, &bvmlist_store);

  bvconst_set_one(bv, 3);
  bvconst_normalize(bv, 65);
  tau = bv_type(&types, 65);

  // polynomial: x + x y + 1
  x = test_uninterpreted_term(tau, "U");
  y = test_uninterpreted_term(tau, "V");
  bvarith_buffer_prepare(&buffer1, 65);
  bvarith_buffer_prepare(&buffer2, 65);

  bvarith_buffer_add_var(&buffer1, x);
  r0 = pprod_mul(&pprods, var_pp(x), var_pp(y)); // x * y
  bvarith_buffer_add_pp(&buffer1, r0);
  bvarith_buffer_add_const(&buffer1, bv);
  bvarith_buffer_normalize(&buffer1);

  bvarith_buffer_add_buffer(&buffer2, &buffer1); // make a copy
  bvarith_buffer_normalize(&buffer2);
  assert(bvarith_buffer_equal(&buffer1, &buffer2));

  printf("Testing: ");
  print_bvarith_buffer(stdout, &buffer1);
  printf(": ");

  s = bv_poly(&terms, &buffer1);
  if (! check_bvpoly(s, 65)) {
    constructor_failed();
  }

  t = bv_poly(&terms, &buffer2);
  if (t != s) {
    hash_consing_failed();
  }

  print_term(stdout, &terms, s);
  printf("\n");

  delete_bvarith_buffer(&buffer1);
  delete_bvarith_buffer(&buffer2);
  printf("\n");
}



/*
 * Bitvector constants
 */
static bool check_bvconst64(term_t x, uint64_t c, uint32_t n) {
  bvconst64_term_t *d;
  type_t tau;
  int32_t i;

  tau = bv_type(&types, n);
  i = index_of(x);
  d = bvconst64_for_idx(&terms, i);
  return kind_for_idx(&terms, i) == BV64_CONSTANT && type_for_idx(&terms, i) == tau &&
    d->bitsize == n && d->value == c;
}

static void test_bvconst64(void) {
  uint64_t c;
  term_t x, y;

  c = norm64(12, 5);
  printf("Testing bitvector constant: ");

  x = bv64_constant(&terms, 5, c);
  if (! check_bvconst64(x, c, 5)) {
    constructor_failed();
  }

  y = bv64_constant(&terms, 5, c);
  if (y != x) {
    hash_consing_failed();
  }

  print_term(stdout, &terms, x);
  printf("\n");

  // mark it for next GC test
  printf("Marking term %"PRId32"\n", index_of(x));
  term_table_set_gc_mark(&terms, index_of(x));
}


/*
 * Bitvector polynomials
 */
static bool check_bvpoly64(term_t x, uint32_t n) {
  int32_t i;
  type_t tau;

  i = index_of(x);
  tau = bv_type(&types, n);
  return kind_for_idx(&terms, i) == BV64_POLY && type_for_idx(&terms, i) == tau
    && is_pos_term(x);
}

static void test_bvpoly64(void) {
  bvarith64_buffer_t buffer1;
  bvarith64_buffer_t buffer2;
  uint64_t c;
  type_t tau;
  term_t x, y, s, t;
  pprod_t *r0;

  init_bvarith64_buffer(&buffer1, &pprods, &bvmlist64_store);
  init_bvarith64_buffer(&buffer2, &pprods, &bvmlist64_store);

  c = 3;
  tau = bv_type(&types, 5);

  // polynomial: x + x y + 1
  x = test_uninterpreted_term(tau, "ZZ");
  y = test_uninterpreted_term(tau, "YY");
  bvarith64_buffer_prepare(&buffer1, 5);
  bvarith64_buffer_prepare(&buffer2, 5);

  bvarith64_buffer_add_var(&buffer1, x);
  r0 = pprod_mul(&pprods, var_pp(x), var_pp(y)); // x * y
  bvarith64_buffer_add_pp(&buffer1, r0);
  bvarith64_buffer_add_const(&buffer1, c);
  bvarith64_buffer_normalize(&buffer1);

  bvarith64_buffer_add_buffer(&buffer2, &buffer1); // make a copy
  bvarith64_buffer_normalize(&buffer2);
  assert(bvarith64_buffer_equal(&buffer1, &buffer2));

  printf("Testing: ");
  print_bvarith64_buffer(stdout, &buffer1);
  printf(": ");

  s = bv64_poly(&terms, &buffer1);
  if (! check_bvpoly64(s, 5)) {
    constructor_failed();
  }

  t = bv64_poly(&terms, &buffer2);
  if (t != s) {
    hash_consing_failed();
  }

  print_term(stdout, &terms, s);
  printf("\n");

  // mark it for next GC test
  printf("Marking term %"PRId32"\n", index_of(s));
  term_table_set_gc_mark(&terms, index_of(s));

  delete_bvarith64_buffer(&buffer1);
  delete_bvarith64_buffer(&buffer2);
  printf("\n");
}



/*
 * CONSTANTS
 */
#define MAX_CONSTANTS 20

static term_t constant[MAX_CONSTANTS];
static uint32_t num_constants;


static void test_constants(void) {
  constant[0] = test_constant_term(type[8], 0, "c0");  // T1
  constant[1] = test_constant_term(type[8], 1, "c1");  // T1
  constant[2] = test_constant_term(type[9], 2, "d2");  // T2
  constant[3] = test_constant_term(type[10], 0, "A");  // E1
  constant[4] = test_constant_term(type[10], 1, "B");  // E1
  constant[5] = test_constant_term(type[10], 2, "C");  // E1
  constant[6] = test_constant_term(type[10], 3, "D");  // E1
  constant[7] = test_constant_term(type[10], 4, "E");  // E1
  constant[8] = test_constant_term(type[11], 0, "e0");  // E2
  constant[9] = test_constant_term(type[11], 4, "e4");  // E2
  constant[10] = test_constant_term(type[12], 0, "u1");  // U1
  constant[11] = test_constant_term(type[13], 0, "u2");  // U2

  num_constants = 12;
  printf("\n");
}


/*
 * UNINTERPRETED TERMS
 */
#define MAX_UNINTERPRETED 20

static term_t unint[MAX_UNINTERPRETED];
static uint32_t num_unints;

static void test_unints(void) {
  unint[0] = test_uninterpreted_term(type[0], "p");   // bool
  unint[1] = test_uninterpreted_term(type[0], "q");   // bool
  unint[2] = test_uninterpreted_term(type[1], "i");   // int
  unint[3] = test_uninterpreted_term(type[1], "j");   // int
  unint[4] = test_uninterpreted_term(type[2], "x");   // real
  unint[5] = test_uninterpreted_term(type[2], "y");   // real
  unint[6] = test_uninterpreted_term(type[3], "aa");  // bv1
  unint[7] = test_uninterpreted_term(type[4], "bb");  // bv6
  unint[8] = test_uninterpreted_term(type[5], "cc");  // bv63
  unint[9] = test_uninterpreted_term(type[6], "dd");  // bv64
  unint[10] = test_uninterpreted_term(type[7], "ee"); // bv65

  unint[11] = test_uninterpreted_term(type[14], "F0"); // bool -> bv1
  unint[12] = test_uninterpreted_term(type[14], "F1"); // bool -> bv1
  unint[13] = test_uninterpreted_term(type[15], "max"); // int, int -> int
  unint[14] = test_uninterpreted_term(type[16], "G0"); // T1 -> T2
  unint[15] = test_uninterpreted_term(type[17], "H0"); // real -> U1
  unint[16] = test_uninterpreted_term(type[17], "H1"); // real -> U1

  num_unints = 17;
  printf("\n");
}


/*
 * VARIABLES
 */
static void test_variables(void) {
  (void) test_variable(type[18], NULL);
  (void) test_variable(type[18], NULL);
  printf("\n");
}


/*
 * COMPOSITES AND SELECT
 */
static void test_composites(void) {
  term_t x, y;

  (void) test_not(true_term, NULL);
  (void) test_not(false_term, NULL);
  x = test_not(unint[0], "not_p");
  y = test_not(x, "not_not_p");

  (void) test_ite(type[8], x, constant[0], constant[1], NULL);
  (void) test_ite(type[8], y, constant[0], constant[1], NULL);
  (void) test_ite(type[8], x, constant[1], constant[0], NULL);
  (void) test_ite(type[8], y, constant[1], constant[0], NULL);
  (void) test_ite(type[2], x, unint[2], unint[4], NULL);
  (void) test_ite(type[2], x, unint[3], unint[4], NULL);

  (void) test_app1(type[3], unint[11], x, NULL);
  (void) test_app1(type[3], unint[12], y, NULL);
  (void) test_app2(type[1], unint[13], unint[2], unint[2], NULL);
  (void) test_app2(type[1], unint[13], unint[2], unint[3], NULL);

  (void) test_update1(type[14], unint[12], true_term, unint[6], NULL); // bool -> bv1
  (void) test_update2(type[15], unint[13], unint[2], unint[3], unint[2], NULL); // int int -> int

  x = test_tuple1(type[18], unint[7], NULL);   // [bv6]
  y = test_tuple2(type[19], unint[2], unint[5], NULL); // [int real]

  (void) test_select(type[4], x, 0, NULL);
  (void) test_select(type[1], y, 0, NULL);
  (void) test_select(type[2], y, 1, NULL);

  (void) test_eq(y, y, NULL);
  (void) test_eq(constant[3], constant[4], NULL);

  (void) test_distinct4(constant[4], constant[5], constant[6], constant[7], NULL);

  x = test_variable(type[7], NULL);
  y = test_variable(type[7], NULL);
  (void) test_forall2(x, y, unint[1], "xxx");

  x = test_variable(type[1], NULL);
  y = test_variable(type[1], NULL);
  (void) test_lambda2(type[15], x, y, unint[3], "lll");

  x = test_or2(unint[0], unint[1], NULL);
  y = test_xor3(x, unint[1], false_term, NULL);
  (void) test_or2(y, x, "test");
  (void) test_bit(unint[10], 64, NULL);
  (void) test_bit(unint[10], 12, NULL);

  (void) test_arith_eq(unint[4], NULL);
  (void) test_arith_geq(unint[3], NULL);
  (void) test_arith_bineq(unint[2], unint[5], NULL);
  (void) test_bvarray4(true_term, true_term, true_term, false_term, NULL);
  (void) test_bvdiv(type[4], unint[7], unint[7], NULL);
  (void) test_bvrem(type[4], unint[7], unint[7], NULL);
  (void) test_bvsdiv(type[4], unint[7], unint[7], NULL);
  (void) test_bvsrem(type[4], unint[7], unint[7], NULL);
  (void) test_bvsmod(type[4], unint[7], unint[7], NULL);
  (void) test_bvshl(type[4], unint[7], unint[7], NULL);
  (void) test_bvlshr(type[4], unint[7], unint[7], NULL);
  (void) test_bvashr(type[4], unint[7], unint[7], NULL);

  (void) test_bveq(unint[8], unint[8], NULL);
  (void) test_bvge(unint[8], unint[8], NULL);
  (void) test_bvsge(unint[8], unint[8], NULL);

  printf("\n");
}


/*
 * Test the unit term maps
 */
static void test_units(void) {
  type_t tau;
  term_t x;

  // both type[12] and type[13] are singleton types
  // const[10] and const[11] are constants of these types
  tau = type[12];
  printf("Testing unit of type ");
  print_type_name(stdout, &types, tau);
  printf("\n");

  x = unit_type_rep(&terms, tau);
  if (x == NULL_TERM) {
    printf("--> no representative\n");
  } else {
    printf("--> representative is term ");
    print_term_name(stdout, &terms, x);
    printf("\n");
    printf("BUG!\n");
    fflush(stdout);
    abort();
  }

  add_unit_type_rep(&terms, tau, constant[10]);
  printf("--> recording term ");
  print_term_name(stdout, &terms, constant[10]);
  printf(" as representative\n");

  x = unit_type_rep(&terms, tau);
  if (x == NULL_TERM) {
    printf("--> no representative\n");
    printf("BUG!\n");
    fflush(stdout);
    abort();
  } else {
    printf("--> representative is term ");
    print_term_name(stdout, &terms, x);
    printf("\n");
    if (x != constant[10]) {
      printf("BUG: rep is wrong\n");
      fflush(stdout);
      abort();
    }
  }


  tau = type[13];
  printf("Testing unit of type ");
  print_type_name(stdout, &types, tau);
  printf("\n");

  x = unit_type_rep(&terms, tau);
  if (x == NULL_TERM) {
    printf("--> no representative\n");
  } else {
    printf("--> representative is term ");
    print_term_name(stdout, &terms, x);
    printf("\n");
    printf("BUG!\n");
    fflush(stdout);
    abort();
  }

  add_unit_type_rep(&terms, tau, constant[11]);
  printf("--> recording term ");
  print_term_name(stdout, &terms, constant[11]);
  printf(" as representative\n");

  x = unit_type_rep(&terms, tau);
  if (x == NULL_TERM) {
    printf("--> no representative\n");
    printf("BUG!\n");
    fflush(stdout);
    abort();
  } else {
    printf("--> representative is term ");
    print_term_name(stdout, &terms, x);
    printf("\n");
    if (x != constant[11]) {
      printf("BUG: rep is wrong\n");
      fflush(stdout);
      abort();
    }
  }

  printf("\n");
}


/*
 * Test names
 */
// name, y = expected result
static void test_name(char *name, type_t y) {
  term_t x;

  x = get_term_by_name(&terms, name);
  if (x == NULL_TERM) {
    printf("No term of name '%s'\n", name);
  } else {
    printf("Term of name '%s' is ", name);
    print_term_name(stdout, &terms, x);
    printf("\n--> ");
    print_term(stdout, &terms, x);
    printf("\n");
  }

  if (y != x) {
    printf("BUG: the expected result is ");
    if (y != NULL_TERM) {
      print_term_name(stdout, &terms, y);
      printf("\n");
    } else {
      printf("null term\n");
    }
    fflush(stdout);
    abort();
  }

}

static void test_names(void) {
  // get all the named terms  after test_constants,
  // test_unints, test_composites
  test_name("c0", constant[0]);
  test_name("c1", constant[1]);
  test_name("d2", constant[2]);
  test_name("A", constant[3]);
  test_name("B", constant[4]);
  test_name("C", constant[5]);
  test_name("D", constant[6]);
  test_name("E", constant[7]);
  test_name("e0", constant[8]);
  test_name("e4", constant[9]);
  test_name("u1", constant[10]);
  test_name("u2", constant[11]);

  test_name("p", unint[0]);
  test_name("q", unint[1]);
  test_name("i", unint[2]);
  test_name("j", unint[3]);
  test_name("x", unint[4]);
  test_name("y", unint[5]);
  test_name("aa", unint[6]);
  test_name("bb", unint[7]);
  test_name("cc", unint[8]);
  test_name("dd", unint[9]);
  test_name("ee", unint[10]);
  test_name("F0", unint[11]);
  test_name("F1", unint[12]);
  test_name("max", unint[13]);
  test_name("G0", unint[14]);
  test_name("H0", unint[15]);
  test_name("H1", unint[16]);

  test_name("not_p", opposite_term(unint[0]));
  test_name("not_not_p", unint[0]);

  test_name("....", NULL_TERM);
  test_name("", NULL_TERM);

  // constant[2]
  printf("\n");
  printf("removing name 'd2'\n");
  remove_term_name(&terms, "d2");
  test_name("d2", NULL_TERM);
  printf("constant[2]: ");
  print_term_name(stdout, &terms, constant[2]);
  printf("\n");
  printf("clearing name of constant[2]\n");
  clear_term_name(&terms, constant[2]);
  printf("constant[2]: ");
  print_term_name(stdout, &terms, constant[2]);
  printf("\n");
  // add a name
  printf("new name for constant[2] = 'dddd'\n");
  set_term_name(&terms, constant[2], clone_string("dddd"));
  test_name("d2", NULL_TERM);
  test_name("dddd", constant[2]);
  printf("\n\n");
}



int main() {
  init_globals();
  init_global_types();

  test_constants();
  test_unints();
  test_variables();
  test_composites();
  test_units();
  test_names();

  printf("--- global types ---\n");
  print_type_table(stdout, &types);
  printf("---\n");

  printf("--- terms ---\n");
  print_term_table(stdout, &terms);
  printf("---\n");

  // test gc
  term_table_gc(&terms, true);

  printf("--- After GC ---\n");
  print_type_table(stdout, &types);
  printf("---\n");

  printf("--- terms ---\n");
  print_term_table(stdout, &terms);
  printf("---\n");

  init_global_types();
  test_composites();
  test_rationals();
  test_polynomials();
  test_bvconst();
  test_bvpoly();
  test_bvconst64();
  test_bvpoly64();

  printf("--- global types ---\n");
  print_type_table(stdout, &types);
  printf("---\n");

  printf("--- terms ---\n");
  print_term_table(stdout, &terms);
  printf("---\n");

  term_table_gc(&terms, true);

  printf("--- After GC ---\n");
  print_type_table(stdout, &types);
  printf("---\n");

  printf("--- terms ---\n");
  print_term_table(stdout, &terms);
  printf("---\n");


  delete_globals();

  return 0;
}
