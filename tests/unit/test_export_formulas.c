#include <stdio.h>
#include <stdbool.h>
#include <inttypes.h>
#include <stdlib.h>

#include "yices.h"

#define NUM_FORMULAS 10

static term_t good_formula[NUM_FORMULAS];
static term_t easy_sat_formula[NUM_FORMULAS];
static term_t easy_unsat_formula[NUM_FORMULAS];
static term_t bad_formula[NUM_FORMULAS];

static term_t new_var(type_t tau, const char *name) {
  term_t t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, name);
  return t;
}

static void build_formulas(void) {
  type_t bv = yices_bv_type(20);
  term_t x = new_var(bv, "x");
  term_t y = new_var(bv, "y");
  term_t z = new_var(bv, "z");

  // three formulas
  good_formula[0] = yices_bveq_atom(yices_bvmul(x, y), yices_bvconst_uint32(20, 12289));
  good_formula[1] = yices_bveq_atom(yices_bvmul(y, z), yices_bvconst_uint32(20, 20031));
  good_formula[2] = yices_bveq_atom(yices_bvmul(x, z), yices_bvconst_uint32(20, 10227));

  // easy sat: x = y * z
  easy_sat_formula[0] = yices_bveq_atom(x, yices_bvmul(y, z));

  // easy unsat: false
  easy_unsat_formula[0] = yices_bveq_atom(x, y);
  easy_unsat_formula[1] = yices_bvneq_atom(x, y);

  // bad formula: not in QF_BV and not trivially SAT or UNSAR
  type_t tau = yices_real_type();
  term_t i = new_var(tau, "i");
  bad_formula[0] = yices_arith_lt0_atom(i);
}

static void show_formulas(const term_t t[], uint32_t n) {
  if (n == 0) {
    printf("Empty fomulas\n");
  } else {
    printf("Formulas:\n  ");
    yices_pp_term_array(stdout, n, t, 100, 120, 2, false);
  }
  fflush(stdout);
}

static void test_export(const char *filename, uint32_t n, const term_t t[], bool simplify) {
  smt_status_t status;
  int32_t code;

  code = yices_export_formulas_to_dimacs(t, n, filename, simplify, &status);
  printf("\nTest export formulas to '%s': got code %"PRId32"\n", filename, code);
  if (code >= 0) {
    show_formulas(t, n);    
  }
  if (code == 1) {
    printf("Produced DIMACS file `%s`\n", filename);
  } else if (code == 0) {
    printf("Solved by preprocessing: no file produced\n");
    if (status == SMT_STATUS_SAT) {
      printf(" formulas are satisfiable\n");
    } else if (status == SMT_STATUS_UNSAT) {
      printf(" formulas are not satisfiable\n");
    } else {
      printf(" BUG: invalid status\n");
      fflush(stdout);
      exit(1);
    }
  } else if (code < 0) {
    printf("Error in export to dimacs\n");    
    yices_print_error(stdout);
    fflush(stdout);
    if (yices_error_code() == OUTPUT_ERROR) {
      perror(filename);
    }
  } else {
    printf(" BUG: invalid code = %"PRId32"\n", code);
    fflush(stdout);
    exit(1);
  }
}

int main(void) {
  printf("Testing Yices %s (%s, %s)\n", yices_version, yices_build_arch, yices_build_mode);
  yices_init();
  build_formulas();

  test_export("empty-formula1.cnf", 0, easy_sat_formula, false);
  test_export("empty-formula1.cnf", 0, easy_sat_formula, true);

  test_export("easy-formula1.cnf", 1, easy_sat_formula, false);
  test_export("easy-formula2.cnf", 1, easy_sat_formula, true);

  test_export("easy-unsat-formula1.cnf", 2, easy_unsat_formula, false);
  test_export("easy-unsat-formula2.cnf", 2, easy_unsat_formula, true);

  test_export("good-formula1.cnf", 3, good_formula, false);
  test_export("good-formula2.cnf", 3, good_formula, true);

  test_export("bad-formula1.cnf", 1, bad_formula, false);
  test_export("bad-formula2.cnf", 1, bad_formula, true);

  test_export("/usr", 3, good_formula, false);
  
  yices_exit();
  return 0;
}
