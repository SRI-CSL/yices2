/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test for hash-consing/push/pop of boolean combinators
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>

#include "solvers/cdcl/gates_hash_table.h"
#include "solvers/cdcl/smt_core_printer.h"
#include "solvers/cdcl/gates_printer.h"


/*
 * Global table
 */
static gate_table_t table;

static void print_all(FILE *f) {
  print_gate_table_stack(f, &table);
  print_gate_table_htbl(f, &table);
  fputc('\n', f);
  fflush(f);
}


/*
 * Array of literals for gate construction
 */
#define MAX_INPUT_SIZE 30

static literal_t input[MAX_INPUT_SIZE];

/*
 * Print n first elements of input array
 */
static void show_input(uint32_t n) {
  uint32_t i;

  fputc('(', stdout);
  if (n > 0) {
    print_literal(stdout, input[0]);
    for (i=1; i<n; i++) {
      fputc(' ', stdout);
      print_literal(stdout, input[i]);
    }
  }
  fputc(')', stdout);
}


/*
 * Test of constructors
 */
static void check_orgate(boolgate_t *g, literal_t l0, literal_t l1, literal_t l2) {
  uint32_t tag;

  tag = g->tag;
  if (tag_combinator(tag) != OR_GATE) {
    printf("*** Incorrect operator: OR_GATE expected ***\n");
  }
  if (tag_indegree(tag) != 3) {
    printf("*** Incorrect in-degree: 3 expected ***\n");
  }
  if (tag_outdegree(tag) != 1) {
    printf("*** Incorrect out-degree: 1 expected ***\n");
  }
  if (g->lit[0] != l0 || g->lit[1] != l1 || g->lit[2] != l2) {
    printf("*** Incorrect input literals ***\n");
  }
}

static void test_orgate(literal_t l0, literal_t l1, literal_t l2) {
  boolgate_t *g0, *g;

  input[0] = l0;
  input[1] = l1;
  input[2] = l2;
  printf("\n--- Testing OR gate ---\n");
  printf("test: OR");
  show_input(3);
  fputc('\n', stdout);

  // test find 1
  g0 = gate_table_find(&table, orgate_tag(3), input);
  if (g0 == NULL) {
    printf("find: returned NULL\n");
  } else {
    printf("find: returned %p: ", g0);
    print_boolgate(stdout, g0);
    printf("\n");
    check_orgate(g0, l0, l1, l2);
  }

  // test get
  g = gate_table_get(&table, orgate_tag(3), input);
  assert(g != NULL);
  printf("get:  returned %p: ", g);
  print_boolgate(stdout, g);
  printf("\n");
  check_orgate(g, l0, l1, l2);
  if (g0 == NULL) {
    if (g->lit[3] != null_literal) {
      printf("*** hash consing inconsistency between find and get ***\n");
    } else {
      printf("new gate: setting output literal to: ");
      print_literal(stdout, pos_lit(12));
      g->lit[3] = pos_lit(12);
      printf("\n");
    }
  } else if (g != g0) {
    printf("*** hash consing bug ***\n");
  }

  // test find 2
  g0 = gate_table_find(&table, orgate_tag(3), input);
  if (g0 == NULL) {
    printf("find: returned NULL\n");
  } else {
    printf("find: returned %p: ", g0);
    print_boolgate(stdout, g0);
    printf("\n");
    check_orgate(g0, l0, l1, l2);
  }
  if (g0 != g) {
    printf("*** hash consing inconsistency between find and get ***\n");
  }
}


static void test1(void) {
  literal_t l0, l1, l2;

  printf("*************************\n");
  printf("*       TEST 1          *\n");
  printf("*************************\n");

  init_gate_table(&table);
  printf("\n--- Initial table ---\n");
  print_all(stdout);

  l0 = pos_lit(4);
  l1 = pos_lit(5);
  l2 = pos_lit(6);
  test_orgate(l0, l1, l2);
  test_orgate(l0, l1, l2);

  printf("\n--- After addition ---\n");
  print_all(stdout);

  gate_table_push(&table);
  gate_table_push(&table);
  printf("\n--- Push: level 2 ---\n");
  print_all(stdout);

  l0 = pos_lit(4);
  l1 = pos_lit(5);
  l2 = pos_lit(6);
  test_orgate(l0, l1, l2);

  l0 = pos_lit(5);
  l1 = pos_lit(6);
  l2 = pos_lit(7);
  test_orgate(l0, l1, l2);
  test_orgate(l0, l1, l2);

  printf("\n--- After addition ---\n");
  print_all(stdout);

  gate_table_push(&table);
  printf("\n--- Push: level 3 ---\n");
  print_all(stdout);

  gate_table_pop(&table);
  printf("\n--- Pop: level 2 ---\n");
  print_all(stdout);

  gate_table_pop(&table);
  printf("\n--- Pop: level 1 ---\n");
  print_all(stdout);

  gate_table_pop(&table);
  printf("\n--- Pop: level 0 ---\n");
  print_all(stdout);

  delete_gate_table(&table);
}


static void test2(void) {
  literal_t l0, l1, l2;

  printf("*************************\n");
  printf("*       TEST 2          *\n");
  printf("*************************\n");

  init_gate_table(&table);
  printf("\n--- Initial table ---\n");
  print_all(stdout);

  gate_table_push(&table);
  gate_table_push(&table);
  printf("\n--- Push: level 2 ---\n");
  print_all(stdout);

  l0 = pos_lit(4);
  l1 = pos_lit(5);
  l2 = pos_lit(6);
  test_orgate(l0, l1, l2);
  test_orgate(l0, l1, l2);

  printf("\n--- After addition ---\n");
  print_all(stdout);

  gate_table_push(&table);
  gate_table_push(&table);

  printf("\n--- Push: level 4 ---\n");
  print_all(stdout);

  l0 = pos_lit(9);
  l1 = pos_lit(8);
  l2 = pos_lit(7);
  test_orgate(l0, l1, l2);
  test_orgate(l0, l1, l2);

  l0 = pos_lit(5);
  l1 = pos_lit(6);
  l2 = pos_lit(7);
  test_orgate(l0, l1, l2);
  test_orgate(l0, l1, l2);

  printf("\n--- After addition ---\n");
  print_all(stdout);

  gate_table_push(&table);
  printf("\n--- Push: level 5 ---\n");
  print_all(stdout);

  gate_table_pop(&table);
  printf("\n--- Pop: level 4 ---\n");
  print_all(stdout);

  gate_table_pop(&table);
  printf("\n--- Pop: level 3 ---\n");
  print_all(stdout);

  l0 = pos_lit(19);
  l1 = pos_lit(18);
  l2 = pos_lit(17);
  test_orgate(l0, l1, l2);
  test_orgate(l0, l1, l2);

  l0 = pos_lit(5);
  l1 = pos_lit(6);
  l2 = pos_lit(7);
  test_orgate(l0, l1, l2);
  test_orgate(l0, l1, l2);

  printf("\n--- After addition ---\n");
  print_all(stdout);

  gate_table_pop(&table);
  printf("\n--- Pop: level 2 ---\n");
  print_all(stdout);

  gate_table_pop(&table);
  printf("\n--- Pop: level 1 ---\n");
  print_all(stdout);

  gate_table_pop(&table);
  printf("\n--- Pop: level 0 ---\n");
  print_all(stdout);

  delete_gate_table(&table);
}


static void test3(void) {
  literal_t l0, l1, l2;

  printf("*************************\n");
  printf("*       TEST 3          *\n");
  printf("*************************\n");

  init_gate_table(&table);
  printf("\n--- Initial table ---\n");
  print_all(stdout);

  gate_table_push(&table);
  gate_table_push(&table);
  printf("\n--- Push: level 2 ---\n");
  print_all(stdout);

  reset_gate_table(&table);
  printf("\n--- Reset ---\n");
  print_all(stdout);

  l0 = pos_lit(4);
  l1 = pos_lit(5);
  l2 = pos_lit(6);
  test_orgate(l0, l1, l2);
  test_orgate(l0, l1, l2);

  printf("\n--- After addition ---\n");
  print_all(stdout);

  gate_table_push(&table);
  gate_table_push(&table);

  printf("\n--- Push: level 2 ---\n");
  print_all(stdout);

  l0 = pos_lit(4);
  l1 = pos_lit(5);
  l2 = pos_lit(6);
  test_orgate(l0, l1, l2);

  l0 = pos_lit(5);
  l1 = pos_lit(6);
  l2 = pos_lit(7);
  test_orgate(l0, l1, l2);
  test_orgate(l0, l1, l2);

  l0 = pos_lit(15);
  l1 = pos_lit(16);
  l2 = pos_lit(17);
  test_orgate(l0, l1, l2);

  l0 = pos_lit(25);
  l1 = pos_lit(26);
  l2 = pos_lit(27);
  test_orgate(l0, l1, l2);

  l0 = pos_lit(35);
  l1 = pos_lit(36);
  l2 = pos_lit(37);
  test_orgate(l0, l1, l2);

  l0 = pos_lit(45);
  l1 = pos_lit(46);
  l2 = pos_lit(47);
  test_orgate(l0, l1, l2);

  l0 = pos_lit(55);
  l1 = pos_lit(56);
  l2 = pos_lit(57);
  test_orgate(l0, l1, l2);

  l0 = pos_lit(65);
  l1 = pos_lit(66);
  l2 = pos_lit(67);
  test_orgate(l0, l1, l2);

  l0 = pos_lit(75);
  l1 = pos_lit(76);
  l2 = pos_lit(77);
  test_orgate(l0, l1, l2);

  l0 = pos_lit(85);
  l1 = pos_lit(86);
  l2 = pos_lit(87);
  test_orgate(l0, l1, l2);

  printf("\n--- After addition ---\n");
  print_all(stdout);

  gate_table_push(&table);
  printf("\n--- Push: level 3 ---\n");
  print_all(stdout);

  reset_gate_table(&table);
  printf("\n--- Reset ---\n");
  print_all(stdout);

  delete_gate_table(&table);
}



int main() {
  test1();
  test2();
  test3();
  return 0;
}
