/*
 * TEST BOOLEAN TABLE
 */

#include <assert.h>
#include <stdio.h>
#include <inttypes.h>

#include "smt_core_printer.h"
#include "bool_vartable.h"


/*
 * Display definition of variable x
 */
static void print_gate_desc(bgate_t *g) {
  if (g->var[2] == null_bvar) {
    printf("(gate p!%"PRId32" p!%"PRId32" [%02x])", g->var[0], g->var[1], (uint32_t) g->ttbl);
  } else {
    printf("(gate p!%"PRId32" p!%"PRId32" p!%"PRId32" [%02x])",
	   g->var[0], g->var[1], g->var[2], (uint32_t) g->ttbl);
  }
}

static void print_or_desc(int32_t *d) {
  int32_t n, i;

  n = d[0];
  printf("(or");
  for (i=1; i<n; i++) {
    printf(" p!%"PRId32, d[i]);
  }
  printf(")");
}

static void show_var_def(bool_vartable_t *table, bvar_t x) {
  assert(valid_boolvar(table, x));

  printf("p!%"PRId32" := ", x);
  switch (boolvar_tag(table, x)) {
  case BCONST:
    fputs("true", stdout);
    break;

  case BVAR:
    printf("var");
    break;

  case BGATE:
    print_gate_desc(boolvar_gate_desc(table, x));
    break;

  case BOR:
    print_or_desc(boolvar_or_desc(table, x));
    break;
  }
}


static void show_bool_vartable(bool_vartable_t *table) {
  uint32_t i, n;

  printf("---- All variables ----\n");
  n = table->nvars;
  for (i=0; i<n; i++) {
    show_var_def(table, i);
    fputc('\n', stdout);
  }
  printf("-----\n");
}


/*
 * Test construction (or l1 l2)
 */
static void test_or2(bool_vartable_t *table, literal_t l1, literal_t l2) {
  literal_t l, check, swap;

  printf("test: (or ");
  print_literal(stdout, l1);
  printf(" ");
  print_literal(stdout, l2);
  printf(") --> ");
  fflush(stdout);

  l = make_or2(table, l1, l2);
  print_literal(stdout, l);
  printf("\n");
  fflush(stdout);

  check = make_or2(table, l1, l2);
  if (l != check) {
    printf("BUG: Hash consing error\n");
    exit(1);
  }

  swap = make_or2(table, l2, l1);
  if (l != swap) {
    printf("BUG: Symmetry failure\n");
    exit(1);
  }
}

/*
 * Test construction (xor l1 l2)
 */
static void test_xor2(bool_vartable_t *table, literal_t l1, literal_t l2) {
  literal_t l, check, swap;

  printf("test: (xor ");
  print_literal(stdout, l1);
  printf(" ");
  print_literal(stdout, l2);
  printf(") --> ");
  fflush(stdout);

  l = make_xor2(table, l1, l2);
  print_literal(stdout, l);
  printf("\n");
  fflush(stdout);

  check = make_xor2(table, l1, l2);
  if (l != check) {
    printf("BUG: Hash consing error\n");
    exit(1);
  }

  swap = make_xor2(table, l2, l1);
  if (l != swap) {
    printf("BUG: Symmetry failure\n");
    exit(1);
  }

  check = make_xor2(table, l1, not(l2));
  if (l != not(check)) {
    printf("BUG: in xor negated\n");
    exit(1);
  }

  check = make_xor2(table, not(l1), l2);
  if (l != not(check)) {
    printf("BUG: in xor negated\n");
    exit(1);
  }

  check = make_xor2(table, not(l1), not(l2));
  if (l != check) {
    printf("BUG: in xor negated\n");
    exit(1);
  }
}

static bool_vartable_t table;

int main(void) {
  bvar_t x, y, z;

  init_bool_vartable(&table);

  printf("\nAFTER INIT\n");
  show_bool_vartable(&table);
  x = make_fresh_boolvar(&table);
  y = make_fresh_boolvar(&table);
  z = make_fresh_boolvar(&table);

  test_or2(&table, pos_lit(x), pos_lit(x));
  test_or2(&table, neg_lit(x), pos_lit(x));
  test_or2(&table, neg_lit(x), neg_lit(x));

  test_or2(&table, pos_lit(y), pos_lit(x));
  test_or2(&table, neg_lit(y), pos_lit(x));
  test_or2(&table, neg_lit(y), neg_lit(x));
  test_or2(&table, pos_lit(y), neg_lit(x));

  test_or2(&table, false_literal, false_literal);
  test_or2(&table, false_literal, true_literal);
  test_or2(&table, true_literal, false_literal);
  test_or2(&table, true_literal, true_literal);

  test_or2(&table, false_literal, pos_lit(z));
  test_or2(&table, false_literal, neg_lit(z));
  test_or2(&table, true_literal, pos_lit(z));
  test_or2(&table, true_literal, neg_lit(z));

  test_xor2(&table, pos_lit(x), pos_lit(x));
  test_xor2(&table, neg_lit(x), pos_lit(x));
  test_xor2(&table, neg_lit(x), neg_lit(x));

  test_xor2(&table, pos_lit(y), pos_lit(x));
  test_xor2(&table, neg_lit(y), pos_lit(x));
  test_xor2(&table, neg_lit(y), neg_lit(x));
  test_xor2(&table, pos_lit(y), neg_lit(x));

  test_xor2(&table, false_literal, false_literal);
  test_xor2(&table, false_literal, true_literal);
  test_xor2(&table, true_literal, false_literal);
  test_xor2(&table, true_literal, true_literal);

  test_xor2(&table, false_literal, pos_lit(z));
  test_xor2(&table, false_literal, neg_lit(z));
  test_xor2(&table, true_literal, pos_lit(z));
  test_xor2(&table, true_literal, neg_lit(z));

  printf("\nAFTER TESTS\n");
  show_bool_vartable(&table);

  reset_bool_vartable(&table);
  printf("\nAFTER RESET\n");
  show_bool_vartable(&table);

  delete_bool_vartable(&table);
  return 0;
}
