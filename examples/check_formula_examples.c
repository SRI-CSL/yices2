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

static void test(const char *delegate) {
  model_t *model;
  smt_status_t status;
  uint32_t n;


  if (delegate != NULL) {
    printf("\n=== Testing %s ===\n", delegate);
  } else {
    printf("\n=== No delegate ===\n");
  }
  if (! yices_has_delegate(delegate)) {
    printf("Not supported\n");
  } else {
    for (n=1; n<=3; n++) {
      show_formulas(n);
      status = yices_check_formulas(formula, n, "QF_BV", &model, delegate);
      switch (status) {
      case YICES_STATUS_UNSAT:
	printf("unsat\n");
	break;

      case YICES_STATUS_SAT:
	printf("sat\n");
	printf("model:\n  ");
	yices_pp_model(stdout, model, 100, 120, 2);
	yices_free_model(model);
	break;

      default:
	printf("error\n");
	yices_print_error(stdout);
	printf("\n");
      }
      printf("\n");
    }

  }
  fflush(stdout);
}

int main(void) {
  printf("Testing Yices %s (%s, %s)\n", yices_version, yices_build_arch, yices_build_mode);
  yices_init();
  build_formulas();
  test("cadical");
  test("cryptominisat");
  test("y2sat");
  test(NULL);
  yices_exit();
  return 0;
}
