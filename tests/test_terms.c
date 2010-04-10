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

#include "refcount_strings.h"
#include "pprod_table.h"
#include "types.h"
#include "terms.h"

#include "term_printer.h"
#include "type_printer.h"


/*
 * Global tables
 */
static pprod_table_t pprods;
static type_table_t types;
static term_table_t terms;


/*
 * Initialize the tables
 */
static void init_globals(void) {
  init_pprod_table(&pprods, 10);
  init_type_table(&types, 10);
  init_term_table(&terms, 10, &types, &pprods);
}


/*
 * Delete them
 */
static void delete_globals(void) {
  delete_term_table(&terms);
  delete_type_table(&types);
  delete_pprod_table(&pprods);
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
static bool check_term_integer(term_t x, type_kind_t tag, type_t tau, int32_t index) {
  int32_t i;

  i = index_of(x);
  return kind_for_idx(&terms, i) == tag && type_for_idx(&terms, i) == tau && 
    integer_value_for_idx(&terms, i) == index && is_pos_term(x);
}


/*
 * Check whether x matches binary composite defined by (tag, tau, a, ..,)
 */
static bool check_composite1(term_t x, type_kind_t tag, type_t tau, term_t a) {
  composite_term_t *p;
  int32_t i;

  i = index_of(x);
  p = composite_for_idx(&terms, i);
  return kind_for_idx(&terms, i) == tag && type_for_idx(&terms, i) == tau &&
    p->arity == 1 && p->arg[0] == a;
}

static bool check_composite2(term_t x, type_kind_t tag, type_t tau, term_t a, term_t b) {
  composite_term_t *p;
  int32_t i;

  i = index_of(x);
  p = composite_for_idx(&terms, i);
  return kind_for_idx(&terms, i) == tag && type_for_idx(&terms, i) == tau &&
    p->arity == 2 && p->arg[0] == a && p->arg[1] == b;
}

static bool check_composite3(term_t x, type_kind_t tag, type_t tau, term_t a, term_t b, term_t c) {
  composite_term_t *p;
  int32_t i;

  i = index_of(x);
  p = composite_for_idx(&terms, i);
  return kind_for_idx(&terms, i) == tag && type_for_idx(&terms, i) == tau &&
    p->arity == 3 && p->arg[0] == a && p->arg[1] == b && p->arg[2] == c;
}

static bool check_composite4(term_t x, type_kind_t tag, type_t tau, term_t a, term_t b, term_t c, term_t d) {
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
static bool check_select(term_t x, type_kind_t tag, type_t tau, term_t a, uint32_t k) {
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

  printf("OK: created ");
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

  printf("OK: ");
  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}


static term_t test_variable(type_t tau, int32_t index, char *name) {
  term_t x, y;

  printf("Testing: variable %"PRId32" of type ", index);
  print_type_name(stdout, &types, tau);
  printf(": ");

  x = variable(&terms, tau, index);
  if (! check_term_integer(x, VARIABLE, tau, index)) {
    constructor_failed();
  }

  y = variable(&terms, tau, index);
  if (x != y) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  printf("OK:  ");
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

  printf("OK: ");
  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}

static term_t test_ite(type_t tau, term_t a, term_t b, term_t c, char *name) {
  term_t x, y;

  printf("Testing: (ite ");
  print_term_name(stdout, &terms, a);
  printf(" ");
  print_term_name(stdout, &terms, b);
  printf(" ");
  print_term_name(stdout, &terms, c);
  printf("): ");

  x = ite_term(&terms, tau, a, b, c);
  if (! check_composite3(x, ITE_TERM, tau, a, b, c)) {
    constructor_failed();
  }
  
  y = ite_term(&terms, tau, a, b, c);
  if (y != x) {
    hash_consing_failed();
  }

  if (name != NULL) {
    set_term_name(&terms, x, clone_string(name));
  }

  printf("OK: ");
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

  printf("OK: ");
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

  printf("OK: ");
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

  printf("OK: ");
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

  printf("OK: ");
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

  printf("OK: ");
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

  printf("OK:  ");
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

  printf("OK:  ");
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

  printf("OK:  ");
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

  printf("OK:  ");
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

  printf("OK:  ");
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

  printf("OK: ");
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

  printf("OK: ");
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

  printf("OK: ");
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

  printf("OK: ");
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

  printf("OK:  ");
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

  printf("OK:  ");
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

  printf("OK:  ");
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

  printf("OK:  ");
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

  printf("OK:  ");
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

  printf("OK:  ");
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

  printf("OK:  ");
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

  printf("OK:  ");
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

  printf("OK:  ");
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

  printf("OK:  ");
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

  printf("OK:  ");
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

  printf("OK:  ");
  print_term(stdout, &terms, x);
  printf("\n");

  return x;
}






/*
 * CONSTANTS
 */
#define MAX_CONSTANTS 20

static term_t constant[MAX_CONSTANTS];
static uint32_t num_constants;


static void test_constants(void) {
  constant[0] = test_constant_term(type[8], 0, "c0");
  constant[1] = test_constant_term(type[8], 1, "c1");
  constant[2] = test_constant_term(type[9], 2, "d2");
  constant[3] = test_constant_term(type[10], 0, "A");
  constant[4] = test_constant_term(type[10], 1, "B");
  constant[5] = test_constant_term(type[10], 2, "C");
  constant[6] = test_constant_term(type[10], 3, "D");
  constant[7] = test_constant_term(type[10], 4, "E");
  constant[8] = test_constant_term(type[11], 0, "e0");
  constant[9] = test_constant_term(type[11], 4, "e4");
  constant[10] = test_constant_term(type[12], 0, "u1");
  constant[11] = test_constant_term(type[13], 0, "u2");
  num_constants = 12;
}


/*
 * UNINTERPRETED TERMS
 */
#define MAX_UNINTERPRETED 20

static term_t unint[MAX_UNINTERPRETED];
static uint32_t num_unints;

static void test_unints(void) {
  unint[0] = test_uninterpreted_term(type[0], "p");
  unint[1] = test_uninterpreted_term(type[0], "q");
  unint[2] = test_uninterpreted_term(type[1], "i");
  unint[3] = test_uninterpreted_term(type[1], "j");
  unint[4] = test_uninterpreted_term(type[2], "x");
  unint[5] = test_uninterpreted_term(type[2], "y");
  unint[6] = test_uninterpreted_term(type[3], "aa");
  unint[7] = test_uninterpreted_term(type[4], "bb");
  unint[8] = test_uninterpreted_term(type[5], "cc");
  unint[9] = test_uninterpreted_term(type[6], "dd");
  unint[10] = test_uninterpreted_term(type[7], "ee");
  unint[11] = test_uninterpreted_term(type[14], "F0");
  unint[12] = test_uninterpreted_term(type[14], "F1");
  unint[13] = test_uninterpreted_term(type[15], "max");
  unint[14] = test_uninterpreted_term(type[16], "G0");
  unint[15] = test_uninterpreted_term(type[17], "H0");
  unint[16] = test_uninterpreted_term(type[17], "H1");
  
  num_unints = 17;
}


/*
 * VARIABLES
 */
static void test_variables(void) {
  (void) test_variable(type[18], 0, NULL);
  (void) test_variable(type[18], 1, NULL);
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
  (void) test_app2(type[1], unint[15], unint[2], unint[2], NULL);
  (void) test_app2(type[1], unint[15], unint[2], unint[3], NULL);
  
}




int main() {
  init_globals();
  init_global_types();
  printf("--- global types ---\n");
  print_type_table(stdout, &types);
  printf("---\n");

  test_constants();
  test_unints();
  test_variables();
  test_composites();

  printf("--- terms ---\n");
  print_term_table(stdout, &terms);
  printf("---\n");

  delete_globals();

  return 0;
}
