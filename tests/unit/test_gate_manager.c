/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test the construction of boolean gates
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <assert.h>

#include "solvers/cdcl/gates_manager.h"
#include "solvers/cdcl/gates_printer.h"
#include "solvers/cdcl/smt_core.h"
#include "solvers/cdcl/smt_core_printer.h"



/******************
 *   SAT SOLVER   *
 *****************/

/*
 * Descriptor for the null-theory
 */
static void do_nothing(void *t) {
}

static void null_backtrack(void *t, uint32_t back_level) {
}

static fcheck_code_t null_final_check(void *t) {
  return FCHECK_SAT;
}

static th_ctrl_interface_t null_theory_ctrl = {
  do_nothing,       // start_internalization
  do_nothing,       // start_search
  NULL,             // propagate
  null_final_check, // final_check
  do_nothing,       // increase_dlevel
  null_backtrack,   // backtrack
  do_nothing,       // push
  do_nothing,       // pop
  do_nothing,       // reset
  do_nothing,       // clear
};

static th_smt_interface_t null_theory_smt = {
  NULL,            // assert_atom
  NULL,            // expand explanation
  NULL,            // select polarity
  NULL,            // delete_atom
  NULL,            // end_deletion
};


/*
 * Initialize core for pure SAT solving
 */
static void init_sat_solver(smt_core_t *core) {
  init_smt_core(core, 0, NULL, &null_theory_ctrl, &null_theory_smt, SMT_MODE_INTERACTIVE);
}


/*
 * Find a model for the current set of clauses (or return unsat)
 * Since this is for testing only, and there are just a few
 * clauses, no restart or reduce are used.
 */
static void quick_solve(smt_core_t *core) {
  literal_t l;

  /*
   * Hackish: if the empty clause was added,
   * we must return now. Adding the empty clause just
   * sets core->inconsistent to true, but start_search clears
   * this flag.
   */
  if (core->inconsistent) {
    core->status = STATUS_UNSAT;
    return;
  }

  start_search(core);
  smt_process(core);
  while (smt_status(core) == STATUS_SEARCHING) {
    l = select_unassigned_literal(core);
    if (l == null_literal) {
      end_search_sat(core);
      break;
    }
    decide_literal(core, l);
    smt_process(core);
  }
}


/*
 * Print current model
 */
static void print_var_value(smt_core_t *core, bvar_t x) {
  bval_t v;

  v = bvar_value(core, x);
  print_bvar(stdout, x);
  printf(" = ");
  print_bval(stdout, v);
  if (v == VAL_TRUE) printf(" ");
}

static void print_assignment(smt_core_t *core) {
  bvar_t x;
  uint32_t n, k;

  assert(smt_status(core) == STATUS_SAT);
  n = num_vars(core);
  k = 0;
  for (x = const_bvar + 1; x<n; x++) {
    printf("  ");
    print_var_value(core, x);
    k ++;
    if (k >= 10) {
      printf("\n");
      k = 0;
    }
  }
  if (k> 0) printf("\n");
}


/*
 * Print decision literals
 */
static void print_decision_literals(smt_core_t *core) {
  ivector_t v;
  uint32_t i, k, n;

  assert(smt_status(core) == STATUS_SAT);
  init_ivector(&v, 10);
  collect_decision_literals(core, &v);

  n = v.size;
  k = 0;
  printf("  %"PRIu32" decision literals:", n);
  for (i=0; i<n; i++) {
    printf(" ");
    print_literal(stdout, v.data[i]);
    k ++;
    if (k >= 30) {
      printf("\n");
      k = 0;
    }
  }
  if (k > 0) printf("\n");

  delete_ivector(&v);
}


/*
 * Print all models
 */
static void all_sat(smt_core_t *core) {
  ivector_t v;
  uint32_t i, n, s;

  init_ivector(&v, 10);

  s = 0;
  for (;;) {
    //    printf("\nClauses\n");
    //    print_clauses(stdout, core);

    quick_solve(core);
    if (smt_status(core) != STATUS_SAT) break;

    s ++;
    print_assignment(core);
    print_decision_literals(core);

    // Add blocking clause
    collect_decision_literals(core, &v);
    n = v.size;
    for (i=0; i<n; i++) {
      v.data[i] = not(v.data[i]);
    }
    smt_clear(core);
    add_clause(core, n, v.data);
  }

  if (s == 0) {
    printf("unsat\n");
  } else {
    printf("\n");
  }

  delete_ivector(&v);
}







/*****************
 * DISPLAY INPUT *
 ****************/

/*
 * Print expression (op a[0] ... a[n-1])
 */
static void display_boolexpr(char *op, uint32_t n, literal_t *a) {
  uint32_t i;

  printf("(%s", op);
  for (i=0; i<n; i++) {
    printf(" ");
    print_literal(stdout, a[i]);
  }
  printf(")");
}

/*
 * Print l := (op a[0] ... a[n-1])
 */
static void display_def(literal_t l, char *op, uint32_t n, literal_t *a) {
  print_literal(stdout, l);
  printf(" := ");
  display_boolexpr(op, n, a);
}


/*
 * Short cuts
 */
static void display_boolexpr2(char *op, literal_t l1, literal_t l2) {
  literal_t a[2];

  a[0] = l1;
  a[1] = l2;
  display_boolexpr(op, 2, a);
}

static void display_def2(literal_t l, char *op, literal_t l1, literal_t l2) {
  literal_t a[2];

  a[0] = l1;
  a[1] = l2;
  display_def(l, op, 2, a);
}

static void display_boolexpr3(char *op, literal_t l1, literal_t l2, literal_t l3) {
  literal_t a[3];

  a[0] = l1;
  a[1] = l2;
  a[2] = l3;
  display_boolexpr(op, 3, a);
}

static void display_def3(literal_t l, char *op, literal_t l1, literal_t l2, literal_t l3) {
  literal_t a[3];

  a[0] = l1;
  a[1] = l2;
  a[2] = l3;
  display_def(l, op, 3, a);
}



/*******************
 *  CROSS-CHECKING *
 ******************/

/*
 * The eval_op functions simplify (op l1 l2) to a single literal,
 * where l1 and l2 are both non_null.
 * They return null_literal if they can't evaluate (op l1 l2)
 * They are guaranteed to return a constant if l1 and l2 are constant
 * (i.e., true_literal or false_literal)
 */
static literal_t eval_and(literal_t l1, literal_t l2) {
  if (l1 == true_literal) return l2;
  if (l2 == true_literal) return l1;
  if (l1 == false_literal) return false_literal;
  if (l2 == false_literal) return false_literal;
  if (l1 == l2) return l1;
  if (l1 == not(l2)) return false_literal;
  return null_literal;
}

static literal_t eval_or(literal_t l1, literal_t l2) {
  if (l1 == false_literal) return l2;
  if (l2 == false_literal) return l1;
  if (l1 == true_literal) return true_literal;
  if (l2 == true_literal) return true_literal;
  if (l1 == l2) return l1;
  if (l1 == not(l2)) return true_literal;
  return null_literal;
}

static literal_t eval_xor(literal_t l1, literal_t l2) {
  if (l1 == false_literal) return l2;
  if (l2 == false_literal) return l1;
  if (l1 == true_literal) return not(l2);
  if (l2 == true_literal) return not(l1);
  if (l1 == l2) return false_literal;
  if (l1 == not(l2)) return true_literal;
  return null_literal;
}

static literal_t eval_iff(literal_t l1, literal_t l2) {
  return eval_xor(not(l1), l2);
}

static literal_t eval_implies(literal_t l1, literal_t l2) {
  return eval_or(not(l1), l2);
}

static literal_t eval_ite(literal_t c, literal_t l1, literal_t l2) {
  literal_t aux1, aux2;

  if (l1 == l2) return l1;

  aux1 = eval_implies(c, l1);
  aux2 = eval_implies(not(c), l2);

  // like (and aux1 aux2)
  if (aux1 == true_literal) return aux2;
  if (aux2 == true_literal) return aux1;
  if (aux1 == false_literal) return false_literal;
  if (aux2 == false_literal) return false_literal;
  if (aux1 == null_literal) return null_literal;
  if (aux2 == null_literal) return null_literal;
  if (aux1 == aux2) return aux1;
  if (aux1 == not(aux2)) return false_literal;
  return null_literal;
}



/************************************
 *  CHECK GATES WITH CONSTANT INPUT *
 ***********************************/

// both l1 and l2 must be constant
static void check_and_aux(gate_manager_t *m, literal_t l1, literal_t l2) {
  literal_t l;

  l = mk_and_gate2(m, l1, l2);
  display_def2(l, "AND", l1, l2);
  if (l == eval_and(l1, l2)) {
    printf(": OK\n");
  } else {
    printf(": ERROR\n");
  }
}

static void check_and(gate_manager_t *m) {
  check_and_aux(m, false_literal, false_literal);
  check_and_aux(m, false_literal, true_literal);
  check_and_aux(m, true_literal, false_literal);
  check_and_aux(m, true_literal, true_literal);
}


static void check_or_aux(gate_manager_t *m, literal_t l1, literal_t l2) {
  literal_t l;

  l = mk_or_gate2(m, l1, l2);
  display_def2(l, "OR", l1, l2);
  if (l == eval_or(l1, l2)) {
    printf(": OK\n");
  } else {
    printf(": ERROR\n");
  }
}

static void check_or(gate_manager_t *m) {
  check_or_aux(m, false_literal, false_literal);
  check_or_aux(m, false_literal, true_literal);
  check_or_aux(m, true_literal, false_literal);
  check_or_aux(m, true_literal, true_literal);
}



static void check_implies_aux(gate_manager_t *m, literal_t l1, literal_t l2) {
  literal_t l;

  l = mk_implies_gate(m, l1, l2);
  display_def2(l, "IMPLIES", l1, l2);
  if (l == eval_implies(l1, l2)) {
    printf(": OK\n");
  } else {
    printf(": ERROR\n");
  }
}

static void check_implies(gate_manager_t *m) {
  check_implies_aux(m, false_literal, false_literal);
  check_implies_aux(m, false_literal, true_literal);
  check_implies_aux(m, true_literal, false_literal);
  check_implies_aux(m, true_literal, true_literal);
}


static void check_xor_aux(gate_manager_t *m, literal_t l1, literal_t l2) {
  literal_t l;

  l = mk_xor_gate2(m, l1, l2);
  display_def2(l, "XOR", l1, l2);
  if (l == eval_xor(l1, l2)) {
    printf(": OK\n");
  } else {
    printf(": ERROR\n");
  }
}

static void check_xor(gate_manager_t *m) {
  check_xor_aux(m, false_literal, false_literal);
  check_xor_aux(m, false_literal, true_literal);
  check_xor_aux(m, true_literal, false_literal);
  check_xor_aux(m, true_literal, true_literal);
}


static void check_iff_aux(gate_manager_t *m, literal_t l1, literal_t l2) {
  literal_t l;

  l = mk_iff_gate(m, l1, l2);
  display_def2(l, "IFF", l1, l2);
  if (l == eval_iff(l1, l2)) {
    printf(": OK\n");
  } else {
    printf(": ERROR\n");
  }
}

static void check_iff(gate_manager_t *m) {
  check_iff_aux(m, false_literal, false_literal);
  check_iff_aux(m, false_literal, true_literal);
  check_iff_aux(m, true_literal, false_literal);
  check_iff_aux(m, true_literal, true_literal);
}




static void check_ite_aux(gate_manager_t *m, literal_t c, literal_t l1, literal_t l2) {
  literal_t l;

  l = mk_ite_gate(m, c, l1, l2);
  display_def3(l, "ITE", c, l1, l2);
  if (l == eval_ite(c, l1, l2)) {
    printf(": OK\n");
  } else {
    printf(": ERROR\n");
  }
}

static void check_ite(gate_manager_t *m) {
  check_ite_aux(m, false_literal, false_literal, false_literal);
  check_ite_aux(m, false_literal, false_literal, true_literal);
  check_ite_aux(m, false_literal, true_literal, false_literal);
  check_ite_aux(m, false_literal, true_literal, true_literal);
  check_ite_aux(m, true_literal, false_literal, false_literal);
  check_ite_aux(m, true_literal, false_literal, true_literal);
  check_ite_aux(m, true_literal, true_literal, false_literal);
  check_ite_aux(m, true_literal, true_literal, true_literal);
}


static void test1(gate_manager_t *m) {
  printf("\n"
	 "****************\n"
	 "*     TEST1    *\n"
	 "****************\n\n");
  check_and(m);
  printf("\n");
  check_or(m);
  printf("\n");
  check_implies(m);
  printf("\n");
  check_xor(m);
  printf("\n");
  check_iff(m);
  printf("\n");
  check_ite(m);
  printf("\n\n");
}


/*
 * CHECK HASH-CONSING
 */
static void test2(gate_manager_t *m) {
  smt_core_t *core;
  literal_t a[3];
  literal_t l, l0;

  printf("\n"
	 "*****************\n"
	 "*     TEST2     *\n"
	 "*****************\n\n");

  core = m->core;
  a[2] = pos_lit(create_boolean_variable(core));
  a[1] = pos_lit(create_boolean_variable(core));
  a[0] = pos_lit(create_boolean_variable(core));
  printf("\n**** AND TEST ****\n");
  l = mk_and_gate(m, 3, a);
  display_def(l, "AND", 3, a);
  printf("\n");
  l0 = mk_and_gate(m, 3, a);
  display_def(l0, "AND", 3, a);
  printf("\n");
  printf("Clauses\n");
  print_clauses(stdout, core);

  printf("\n**** OR TEST ****\n");
  a[0] = not(a[0]);
  a[1] = not(a[1]);
  a[2] = not(a[2]);
  l = mk_or_gate(m, 3, a);
  display_def(l, "OR", 3, a);
  printf("\n");
  l0 = mk_or_gate(m, 3, a);
  display_def(l0, "OR", 3, a);
  printf("\n");
  printf("Clauses\n");
  print_clauses(stdout, core);

  printf("\n**** XOR TEST ****\n");
  a[0] = not(a[0]);
  a[1] = not(a[1]);
  a[2] = not(a[2]);
  l = mk_xor_gate(m, 3, a);
  display_def(l, "XOR", 3, a);
  printf("\n");
  l0 = mk_xor_gate(m, 3, a);
  display_def(l0, "XOR", 3, a);
  printf("\n");
  printf("Clauses\n");
  print_clauses(stdout, core);

  a[0] = not(a[0]);
  l = mk_xor_gate(m, 3, a);
  display_def(l, "XOR", 3, a);
  printf("\n");
  l0 = mk_xor_gate(m, 3, a);
  display_def(l0, "XOR", 3, a);
  printf("\n");
  printf("Clauses\n");
  print_clauses(stdout, core);

  a[1] = not(a[1]);
  l = mk_xor_gate(m, 3, a);
  display_def(l, "XOR", 3, a);
  printf("\n");
  l0 = mk_xor_gate(m, 3, a);
  display_def(l0, "XOR", 3, a);
  printf("\n");
  printf("Clauses\n");
  print_clauses(stdout, core);

  a[2] = not(a[2]);
  l = mk_xor_gate(m, 3, a);
  display_def(l, "XOR", 3, a);
  printf("\n");
  l0 = mk_xor_gate(m, 3, a);
  display_def(l0, "XOR", 3, a);
  printf("\n");
  printf("Clauses\n");
  print_clauses(stdout, core);
  printf("\n");

  printf("*** GATES ***\n");
  print_gate_table(stdout, &m->htbl);
  printf("\n\n");
}




/*
 * More tests on XOR
 */
static void test3(gate_manager_t *m) {
  smt_core_t *core;
  literal_t a[10];
  literal_t l1, l2, l3, l;
  uint32_t i;

  printf("\n"
	 "*****************\n"
	 "*     TEST3     *\n"
	 "*****************\n\n");

  core = m->core;
  l1 = pos_lit(create_boolean_variable(core));
  l2 = pos_lit(create_boolean_variable(core));
  l3 = pos_lit(create_boolean_variable(core));

  for (i=0; i<10; i++) {
    a[i] = l1;
  }
  for (i=0; i<=10; i++) {
    l = mk_xor_gate(m, i, a);
    display_def(l, "XOR", i, a);
    printf("\n");
  }
  printf("\n");

  a[0] = true_literal;
  a[1] = l2;
  a[2] = not(l2);
  a[3] = false_literal;
  for (i=0; i<=10; i++) {
    l = mk_xor_gate(m, i, a);
    display_def(l, "XOR", i, a);
    printf("\n");
  }
  printf("\n");

  a[4] = not(l1);
  a[5] = l1;
  a[6] = not(l3);
  a[7] = not(l3);
  for (i=0; i<=10; i++) {
    l = mk_xor_gate(m, i, a);
    display_def(l, "XOR", i, a);
    printf("\n");
  }
  printf("\n");

  printf("*** GATES ***\n");
  print_gate_table(stdout, &m->htbl);
  printf("\n\n");
}



/*
 * Check models for a single XOR gate
 */
static void check_xor_models(gate_manager_t *m) {
  smt_core_t *core;
  literal_t l1, l2, l3, l;

  core = m->core;
  reset_gate_manager(m);
  reset_smt_core(core);

  l1 = pos_lit(create_boolean_variable(core));
  l2 = pos_lit(create_boolean_variable(core));
  l3 = pos_lit(create_boolean_variable(core));

  l = mk_xor_gate3(m, l1, l2, l3);
  printf("\nAssertion: ");
  display_def3(l, "XOR", l1, l2, l3);
  printf("\n");
  print_gate_table(stdout, &m->htbl);
  printf("\n");

  all_sat(core);
}


/*
 * Check models for a single IFF gate
 */
static void check_iff_models(gate_manager_t *m) {
  smt_core_t *core;
  literal_t l1, l2, l;

  core = m->core;
  reset_gate_manager(m);
  reset_smt_core(core);

  l1 = pos_lit(create_boolean_variable(core));
  l2 = pos_lit(create_boolean_variable(core));

  l = mk_iff_gate(m, l1, l2);
  printf("\nAssertion: ");
  display_def2(l, "IFF", l1, l2);
  printf("\n");
  print_gate_table(stdout, &m->htbl);
  printf("\n");

  all_sat(core);
}


/*
 * Check models for a single ITE gate
 */
static void check_ite_models(gate_manager_t *m) {
  smt_core_t *core;
  literal_t l1, l2, l3, l;

  core = m->core;
  reset_gate_manager(m);
  reset_smt_core(core);

  l1 = pos_lit(create_boolean_variable(core));
  l2 = pos_lit(create_boolean_variable(core));
  l3 = pos_lit(create_boolean_variable(core));

  l = mk_ite_gate(m, l1, l2, l3);
  printf("\nAssertion: ");
  display_def3(l, "ITE", l1, l2, l3);
  printf("\n");
  print_gate_table(stdout, &m->htbl);
  printf("\n");

  all_sat(core);
}


/*
 * Check models for a single OR gate
 */
static void check_or_models(gate_manager_t *m) {
  smt_core_t *core;
  literal_t l;
  literal_t a[4];

  core = m->core;
  reset_gate_manager(m);
  reset_smt_core(core);

  a[0] = pos_lit(create_boolean_variable(core));
  a[1] = pos_lit(create_boolean_variable(core));
  a[2] = pos_lit(create_boolean_variable(core));
  a[3] = pos_lit(create_boolean_variable(core));

  l = mk_or_gate(m, 4, a);
  printf("\nAssertion: ");
  display_def(l, "OR", 4, a);
  printf("\n");
  print_gate_table(stdout, &m->htbl);
  printf("\n");

  all_sat(core);
}


/*
 * Check models for a single AND gate
 */
static void check_and_models(gate_manager_t *m) {
  smt_core_t *core;
  literal_t l;
  literal_t a[4];

  core = m->core;
  reset_gate_manager(m);
  reset_smt_core(core);

  a[0] = pos_lit(create_boolean_variable(core));
  a[1] = pos_lit(create_boolean_variable(core));
  a[2] = pos_lit(create_boolean_variable(core));
  a[3] = pos_lit(create_boolean_variable(core));

  l = mk_and_gate(m, 4, a);
  printf("\nAssertion: ");
  display_def(l, "AND", 4, a);
  printf("\n");
  print_gate_table(stdout, &m->htbl);
  printf("\n");

  all_sat(core);
}


/*
 * Check XOR/ITE/IFF assertions
 */
static void check_xor2_assertion(gate_manager_t *m) {
  smt_core_t *core;
  literal_t l1, l2;

  core = m->core;
  reset_gate_manager(m);
  reset_smt_core(core);

  l1 = pos_lit(create_boolean_variable(core));
  l2 = pos_lit(create_boolean_variable(core));

  assert_xor2(m, l1, l2, true);
  printf("\nAssertion: ");
  display_boolexpr2("XOR", l1, l2);
  printf(" == true\n");
  print_gate_table(stdout, &m->htbl);
  printf("\n");

  all_sat(core);
}

static void check_xor3_assertion(gate_manager_t *m) {
  smt_core_t *core;
  literal_t l1, l2, l3;

  core = m->core;
  reset_gate_manager(m);
  reset_smt_core(core);

  l1 = pos_lit(create_boolean_variable(core));
  l2 = pos_lit(create_boolean_variable(core));
  l3 = pos_lit(create_boolean_variable(core));

  assert_xor3(m, l1, l2, l3, true);
  printf("\nAssertion: ");
  display_boolexpr3("XOR", l1, l2, l3);
  printf(" == true\n");
  print_gate_table(stdout, &m->htbl);
  printf("\n");

  all_sat(core);
}

static void check_xor5_assertion(gate_manager_t *m) {
  smt_core_t *core;
  literal_t a[5];

  core = m->core;
  reset_gate_manager(m);
  reset_smt_core(core);

  a[0] = pos_lit(create_boolean_variable(core));
  a[1] = pos_lit(create_boolean_variable(core));
  a[2] = pos_lit(create_boolean_variable(core));
  a[3] = pos_lit(create_boolean_variable(core));
  a[4] = pos_lit(create_boolean_variable(core));

  assert_xor(m, 5, a, true);

  printf("\nAssertion: ");
  display_boolexpr("XOR", 5, a);
  printf(" == true\n");
  print_gate_table(stdout, &m->htbl);
  printf("\n");

  all_sat(core);
}

static void check_iff_assertion(gate_manager_t *m) {
  smt_core_t *core;
  literal_t l1, l2;

  core = m->core;
  reset_gate_manager(m);
  reset_smt_core(core);

  l1 = pos_lit(create_boolean_variable(core));
  l2 = pos_lit(create_boolean_variable(core));

  assert_iff(m, l1, l2, true);
  printf("\nAssertion: ");
  display_boolexpr2("IFF", l1, l2);
  printf(" == true\n");
  print_gate_table(stdout, &m->htbl);
  printf("\n");

  all_sat(core);
}

static void check_iff_assertion2(gate_manager_t *m) {
  smt_core_t *core;
  literal_t l1, l2;

  core = m->core;
  reset_gate_manager(m);
  reset_smt_core(core);

  l1 = pos_lit(create_boolean_variable(core));
  l2 = not(l1);

  assert_iff(m, l1, l2, true);
  printf("\nAssertion: ");
  display_boolexpr2("IFF", l1, l2);
  printf(" == true\n");
  print_gate_table(stdout, &m->htbl);
  printf("\n");

  all_sat(core);
}

static void check_iff_assertion3(gate_manager_t *m) {
  smt_core_t *core;
  literal_t l1, l2;

  core = m->core;
  reset_gate_manager(m);
  reset_smt_core(core);

  l1 = pos_lit(create_boolean_variable(core));
  l2 = l1;

  assert_iff(m, l1, l2, true);
  printf("\nAssertion: ");
  display_boolexpr2("IFF", l1, l2);
  printf(" == true\n");
  print_gate_table(stdout, &m->htbl);
  printf("\n");

  all_sat(core);
}

static void check_iff_assertion4(gate_manager_t *m) {
  smt_core_t *core;
  literal_t l1, l2;

  core = m->core;
  reset_gate_manager(m);
  reset_smt_core(core);

  l1 = true_literal;
  l2 = false_literal;

  assert_iff(m, l1, l2, true);
  printf("\nAssertion: ");
  display_boolexpr2("IFF", l1, l2);
  printf(" == true\n");
  print_gate_table(stdout, &m->htbl);
  printf("\n");

  all_sat(core);
}

static void check_iff_assertion5(gate_manager_t *m) {
  smt_core_t *core;
  literal_t l1, l2;

  core = m->core;
  reset_gate_manager(m);
  reset_smt_core(core);

  l1 = true_literal;
  l2 = true_literal;

  assert_iff(m, l1, l2, true);
  printf("\nAssertion: ");
  display_boolexpr2("IFF", l1, l2);
  printf(" == true\n");
  print_gate_table(stdout, &m->htbl);
  printf("\n");

  all_sat(core);
}


static void check_ite_assertion(gate_manager_t *m) {
  smt_core_t *core;
  literal_t l1, l2, l3;

  core = m->core;
  reset_gate_manager(m);
  reset_smt_core(core);

  l1 = pos_lit(create_boolean_variable(core));
  l2 = pos_lit(create_boolean_variable(core));
  l3 = pos_lit(create_boolean_variable(core));

  assert_ite(m, l1, l2, l3, true);
  printf("\nAssertion: ");
  display_boolexpr3("ITE", l1, l2, l3);
  printf(" == true\n");
  print_gate_table(stdout, &m->htbl);
  printf("\n");

  all_sat(core);
}




/*
 * Check models for XOR, IFF, and ITE
 */
static void test4(gate_manager_t *m) {
  printf("\n"
	 "*****************\n"
	 "*     TEST4    *\n"
	 "*****************\n");
  check_xor_models(m);
  check_iff_models(m);
  check_ite_models(m);
  check_and_models(m);
  check_or_models(m);

  check_xor2_assertion(m);
  check_xor3_assertion(m);
  check_xor5_assertion(m);

  check_iff_assertion(m);
  check_iff_assertion2(m);
  check_iff_assertion3(m);
  check_iff_assertion4(m);
  check_iff_assertion5(m);

  check_ite_assertion(m);
  printf("\n\n");
}



/******************
 *  GATE MANAGER  *
 *****************/

static smt_core_t core;
static gate_manager_t manager;

int main() {
  init_sat_solver(&core);
  init_gate_manager(&manager, &core);

  test1(&manager);
  test2(&manager);

  reset_gate_manager(&manager);
  reset_smt_core(&core);
  test3(&manager);

  test4(&manager);

  delete_gate_manager(&manager);
  delete_smt_core(&core);
  return 0;
}

