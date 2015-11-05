/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST OF BASIC EGRAPH + CORE FUNCTIONS
 */

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <inttypes.h>


#include "api/yices_globals.h"
#include "solvers/cdcl/smt_core.h"
#include "solvers/cdcl/smt_core_printer.h"
#include "solvers/egraph/egraph.h"
#include "solvers/egraph/egraph_printer.h"

#include "yices.h"



/*
 * Build egraph and core
 */
#define DEFAULT_NVARS 100

static void init_solver(egraph_t *egraph, smt_core_t *core) {
  init_egraph(egraph, __yices_globals.types);
  init_smt_core(core, DEFAULT_NVARS, egraph, egraph_ctrl_interface(egraph),
		egraph_smt_interface(egraph), SMT_MODE_PUSHPOP);
  egraph_attach_core(egraph, core);
}

/*
 * Delete both
 */
static void delete_solver(egraph_t *egraph, smt_core_t *core) {
  delete_egraph(egraph);
  delete_smt_core(core);
}

/*
 * Reset both
 */
static void reset_solver(egraph_t *egraph, smt_core_t *core) {
  reset_smt_core(core);
}


/*
 * Print both
 */
static void print_solver(egraph_t *egraph, smt_core_t *core) {
  printf("--- Terms ---\n");
  print_egraph_terms(stdout, egraph);
  printf("--- Atoms ---\n");
  print_egraph_atoms(stdout, egraph);
  print_egraph_congruence_roots(stdout, egraph);
  printf("--- Classes ---\n");
  print_egraph_root_classes(stdout, egraph);
  printf("--- Clauses ---\n");
  print_clauses(stdout, core);
}


#if 0

/*
 * More details (not used)
 */
static void print_solver_details(egraph_t *egraph, smt_core_t *core) {
  print_egraph_terms_details(stdout, egraph);
  print_egraph_root_classes_details(stdout, egraph);
  print_egraph_atoms(stdout, egraph);
  print_clauses(stdout, core);
}

#endif


/*
 * Global variables: the core + the egraph
 */
static egraph_t egraph;
static smt_core_t core;


/*
 * Test 1: construct simple terms, push/pop
 */
static void test1(void) {
  eterm_t tx, ty;
  occ_t x, y;
  type_t u;

  printf("***********************\n"
	 "*       TEST 1        *\n"
	 "***********************\n\n");

  init_solver(&egraph, &core);

  u = yices_new_uninterpreted_type();

  // create x and y
  printf("---> building x and y\n");
  tx = egraph_make_variable(&egraph, u);
  x = pos_occ(tx);

  ty = egraph_make_variable(&egraph, u);
  y = pos_occ(ty);

  // test push/pop
  printf("---> push\n");
  smt_push(&core);

  // create (eq x y)
  printf("---> building (eq x y)\n");
  (void) egraph_make_eq(&egraph, x, y);

  // create (eq y y)
  printf("---> building (eq x x)\n");
  (void) egraph_make_eq(&egraph, y, y);

  print_solver(&egraph, &core);

  // empty push
  printf("---> push\n");
  smt_push(&core);

  // start search + propagate + end_search
  printf("---> propagation test 1\n");
  start_search(&core);
  smt_process(&core);
  end_search_unknown(&core);
  print_solver(&egraph, &core);

  printf("---> pop 1\n");
  smt_pop(&core);
  print_solver(&egraph, &core);

  // start search + propagate + end_search
  printf("---> propagation test 2\n");
  start_search(&core);
  smt_process(&core);
  end_search_unknown(&core);
  print_solver(&egraph, &core);


  printf("---> pop 2\n");
  smt_pop(&core);
  print_solver(&egraph, &core);

  // reset
  reset_solver(&egraph, &core);
  print_solver(&egraph, &core);

  delete_solver(&egraph, &core);
}


/*
 * Test 2: build distinct terms
 */
static void test2(void) {
  uint32_t i;
  eterm_t aux;
  occ_t a[50];
  literal_t l;
  type_t tau;

  printf("***********************\n"
	 "*       TEST 2        *\n"
	 "***********************\n\n");

  init_solver(&egraph, &core);

  tau = yices_new_uninterpreted_type();

  printf("---> building a_0 ... a_49\n");
  for (i=0; i<50; i++) {
    aux = egraph_make_variable(&egraph, tau);
    a[i] = pos_occ(aux);
  }

  for (i=0; i<40; i++) {
    printf("---> creating (distinct a_%"PRIu32" ... a_%"PRIu32")\n", i, i+5);
    l = egraph_make_distinct(&egraph, 5, a+i);
    printf("---> result = ");
    print_literal(stdout, l);
    printf("\n");
  }

  print_solver(&egraph, &core);
  delete_solver(&egraph, &core);
}


int main(void) {
  yices_init();
  test1();
  test2();
  yices_exit();
  return 0;
}
