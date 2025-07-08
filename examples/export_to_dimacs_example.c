#include <stdio.h>
#include <stdbool.h>
#include <inttypes.h>

#include "yices.h"

#define NUM_FORMULAS 10
static term_t formula[NUM_FORMULAS];

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
  formula[0] = yices_bveq_atom(yices_bvmul(x, y), yices_bvconst_uint32(20, 12289));
  formula[1] = yices_bveq_atom(yices_bvmul(y, z), yices_bvconst_uint32(20, 20031));
  formula[2] = yices_bveq_atom(yices_bvmul(x, z), yices_bvconst_uint32(20, 10227));
}

static void show_formulas(uint32_t n) {
  printf("Formulas:\n  ");
  yices_pp_term_array(stdout, n, formula, 100, 120, 2, false);
  fflush(stdout);
}

static char *status_to_string(smt_status_t status) {
  switch (status) {
  case YICES_STATUS_SAT: return "sat";
  case YICES_STATUS_UNSAT: return "unsat";
  default: return "bug";
  }
}

static void test(void) {
  char filename[40];
  uint32_t n;
  smt_status_t status;
  int32_t code;

  // first round: don't simplify the CNF
  for (n=1; n<=3; n++) {
    show_formulas(n);
    snprintf(filename, 40, "basic%"PRIu32".cnf", n);
    code = yices_export_formulas_to_dimacs(formula, n, filename, false, &status);
    if (code < 0) {
      printf("Export to dimacs failed\n");
      yices_print_error(stdout);
    } else if (code == 0) {
      printf("No dimacs produced: formula solved %s\n", status_to_string(status));
      fflush(stdout);
    } else {
      printf("Successfully exported to file %s\n", filename);
    }
    fflush(stdout);
  }

  // second round: simplify the CNF
  for (n=1; n<=3; n++) {
    show_formulas(n);
    snprintf(filename, 40, "simplified%"PRIu32".cnf", n);
    code = yices_export_formulas_to_dimacs(formula, n, filename, true, &status);
    if (code < 0) {
      printf("Export to dimacs failed\n");
      yices_print_error(stdout);
    } else if (code == 0) {
      printf("No dimacs produced: formula solved %s\n", status_to_string(status));
      fflush(stdout);
    } else {
      printf("Successfully exported to file %s\n", filename);
    }
    fflush(stdout);
  }
}

int main(void) {
  printf("Testing Yices %s (%s, %s)\n", yices_version, yices_build_arch, yices_build_mode);
  yices_init();
  build_formulas();
  test();
  yices_exit();
  return 0;
}
