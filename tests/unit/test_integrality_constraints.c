/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <assert.h>
#include <stdio.h>
#include <inttypes.h>

#include "solvers/simplex/integrality_constraints.h"
#include "terms/rationals.h"
#include "utils/int_vectors.h"


/*
 * VARIABLES
 */

/*
 * Descriptor of a variable
 * - is_int: true if that's an integer variable
 * - is_fixed: true if that's a fixed variable
 * - fixed_value: value if is_fixed is true, unused otherwise (set to zero)
 * - name
 */
typedef struct vardata_s {
  bool is_int;
  bool is_fixed;
  rational_t fixed_value;
  const char *name;
} vardata_t;

#define NVARS 20

static vardata_t var[NVARS];

// variable names
static const char *const names[NVARS] = {
  "x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10", // not fixed
  "y1", "y2", "y3", "y4", "y5", // fixed/integer
  "z1", "z2", "z3", "z4", "z5", // fixed/not-integer
};

// values of fixed variables
static const char *const valstring[NVARS] = {
  NULL, NULL, NULL, NULL,  NULL,  NULL,  NULL,  NULL,  NULL,  NULL,
  "1", "0", "-1", "2", "-7", // fixed/integer
  "0", "1/3", "5", "-3/8", "5/2", // fixed/not-integer
};


/*
 * Initialize this table:
 * - 10 non-fixed variables
 *    5 fixed vars with integer type
 *    5 fixed vars not integer
 */
static void init_vartable(void) {
  uint32_t i;

  for (i=0; i<NVARS; i++) {
    q_init(&var[i].fixed_value);
  }

  for (i=0; i<10; i++) {
    var[i].is_int = true;
    var[i].is_fixed = false;
    var[i].name = names[i];
  }
  for (i=10; i<15; i++) {
    var[i].is_int = true;
    var[i].is_fixed = true;
    q_set_from_string(&var[i].fixed_value, valstring[i]);
    var[i].name = names[i];
  }
  for (i=15; i<NVARS; i++) {
    var[i].is_int = false;
    var[i].is_fixed = true;
    q_set_from_string(&var[i].fixed_value, valstring[i]);
    var[i].name = names[i];
  }
}

static void delete_vartable(void) {
  uint32_t i;

  for (i=0; i<NVARS; i++) {
    q_clear(&var[i].fixed_value);
  }
}

static void show_var(FILE *f, uint32_t i) {
  const char *type;
  const char *fixed;

  assert(i < NVARS);

  type = var[i].is_int ? "int" : "rational";
  fixed = var[i].is_fixed ? "fixed" : "not fixed";

  fprintf(f, "var[%"PRIu32"]: name = %s, type = %s, %s", i, var[i].name, type, fixed);
  if (var[i].is_fixed) {
    fprintf(f, ", value = ");
    q_print(f, &var[i].fixed_value);
  }
  fprintf(f, "\n");
}

static void show_all_vars(FILE *f) {
  uint32_t i;

  fprintf(f, "==== all variables ====\n");
  for (i=0; i<NVARS; i++) {
    show_var(f, i);
  }
  fprintf(f, "\n");
}

static void show_varnames(FILE *f, int32_t *v, uint32_t n) {
  uint32_t i;
  int32_t x;

  if (n == 0) {
    fprintf(f, "{}\n");
  } else {
    x = v[0];
    assert(0 <= x && x < NVARS);
    fprintf(f, "{%s", var[x].name);
    for (i=1; i<n; i++) {
      x = v[i];
      assert(0 <= x && x < NVARS);
      fprintf(f, ", %s", var[x].name);
    }
    fprintf(f, "}\n");
  }  
}

/*
 * DISPLAY CONSTRAINT
 */
static void show_constant(FILE *f, rational_t *a, bool first) {
  if (first) {
    if (q_is_neg(a)) {
      fprintf(f, "- ");
    }
  } else {
    if (q_is_neg(a)) {
      fprintf(f, " - ");
    } else {
      fprintf(f, " + ");
    }
  }
  q_print_abs(f, a);
}

static void show_monomial(FILE *f, rational_t *a, int32_t x, bool first) {
  assert(0 <= x && x < NVARS);
  assert(q_is_nonzero(a));

  show_constant(f, a, first);
  fprintf(f, " %s", var[x].name);
}

static void show_sum(FILE *f, monomial_t *p, uint32_t n, bool first) {
  uint32_t i;

  for (i=0; i<n; i++) {
    show_monomial(f, &p[i].coeff, p[i].var, first);
    first = false;
  }
}

static void show_constraint(FILE *f, int_constraint_t *cnstr) {
  fprintf(f, "  IsInt(");
  show_sum(f, cnstr->sum, cnstr->sum_nterms, true);
  show_sum(f, cnstr->fixed_sum, cnstr->fixed_nterms, false);
  if (q_is_nonzero(&cnstr->constant)) {
    show_constant(f, &cnstr->constant, false);
  }
  fprintf(f, ")\n");
}

static void show_fixed_vars(FILE *f, int_constraint_t *cnstr) {
  uint32_t i, n;
  int32_t x;

  n = cnstr->fixed_nterms;
  if (n == 0) {
    fprintf(f, "No fixed variable\n");
  } else {
    fprintf(f, "Fixed variables:\n");
    for (i=0; i<n; i++) {
      x = cnstr->fixed_sum[i].var;
      fprintf(f, " val[%s] = ", var[x].name);
      q_print(f, &cnstr->fixed_val[i]);
      printf("\n");
    }
  }  
}

static void show_constraint_details(FILE *f, int_constraint_t *cnstr) {
  fprintf(f, "Details\n");
  fprintf(f, "  num_gcd = ");
  q_print(f, &cnstr->num_gcd);
  fprintf(f, "\n");
  fprintf(f, "  den_lcm = ");
  q_print(f, &cnstr->den_lcm);
  fprintf(f, "\n");
  fprintf(f, "  gcd     = ");
  q_print(f, &cnstr->gcd);
  fprintf(f, "\n");
  fprintf(f, "  fixed   = ");
  q_print(f, &cnstr->fixed_constant);
  fprintf(f, "\n");
}


/*
 * Some checks on period/phase computations for variable k
 */

/*
 * Sum of all fixed terms
 */
static void sum_of_fixed_terms(int_constraint_t *cnstr, rational_t *sum) {
  uint32_t i, n;

  q_clear(sum);
  n = cnstr->fixed_nterms;
  for (i=0; i<n; i++) {
    q_addmul(sum, cnstr->fixed_val + i, &cnstr->fixed_sum[i].coeff);
  }
}

/*
 * Get a value of of variable k that satisfies the constraints.
 * - the constraint is (a * var[k] + other vars + fixed sum) is an integer
 * - so a possible solution is to set all non-fixed vars to (z - fixed_sum)/a
 */
static void get_solution_for_var(int_constraint_t *cnstr, uint32_t k, rational_t *val, int32_t z) {
  rational_t qz;

  assert(k < cnstr->sum_nterms);

  q_init(&qz);

  q_set32(&qz, z);
  sum_of_fixed_terms(cnstr, val);
  q_neg(val);
  q_add(val, &qz);
  q_div(val, &cnstr->sum[k].coeff);

  q_clear(&qz);
}
 

/*
 * Check whether cnstr => var[k] = period * integer + phase
 */
static void check_period_and_phase(int_constraint_t *cnstr, uint32_t k, rational_t *period, rational_t *phase) {
  rational_t test_val;
  int32_t x, z;  

  q_init(&test_val);

  x = int_constraint_get_var(cnstr, k);

  for (z = -10; z < 10; z++) {
    get_solution_for_var(cnstr, k, &test_val, z);
    q_sub(&test_val, phase);  // value - phase 
    if (q_divides(period, &test_val)) {
      printf("  passed test for %s = ", var[x].name);
      q_print(stdout, &test_val);
      printf("\n");
    } else {
      printf("*** BUG ***");
      printf("  failed test for %s = ", var[x].name);
      q_print(stdout, &test_val);
      printf("\n");
      fflush(stdout);
      exit(1);
    }
  }

  q_clear(&test_val);
}


/*
 * Test the period/phase computation
 */
static void test_periods_and_phases(int_constraint_t *cnstr) {
  ivector_t v;
  rational_t *p, *q;
  uint32_t i, n;
  int32_t x;

  init_ivector(&v, 10);

  n = int_constraint_num_terms(cnstr);
  for (i=0; i<n; i++) {
    ivector_reset(&v);
    int_constraint_period_of_var(cnstr, i, &v);
    x = int_constraint_get_var(cnstr, i);
    p = int_constraint_period(cnstr);
    q = int_constraint_phase(cnstr);
    printf("Variable %s: period = ", var[x].name);
    q_print(stdout, p);
    printf(", phase = ");
    q_print(stdout, q);
    printf("\n");
    printf("  antecedents: ");
    show_varnames(stdout, v.data, v.size);
    check_period_and_phase(cnstr, i, p, q);
  }

  delete_ivector(&v);
}

/*
 * Run a test:
 * - show the constraint 
 * - check feasibility
 * - print the result
 */
static void run_test(int_constraint_t *cnstr) {
  ivector_t v;
  bool feasible;

  init_ivector(&v, 10);

  printf("Constraint: ");
  show_constraint(stdout, cnstr);
  show_fixed_vars(stdout, cnstr);

  feasible = int_constraint_is_feasible(cnstr, &v);
  if (feasible) {
    printf("Feasible\n");
  } else {
    printf("Not feasible\n");
    printf("conflict vars: ");
    show_varnames(stdout, v.data, v.size);
  }
  show_constraint_details(stdout, cnstr);

  if (feasible) {
    test_periods_and_phases(cnstr);
  }

  fflush(stdout);
  
  delete_ivector(&v);
}

static void test_constraint(void) {
  int_constraint_t test;
  rational_t q;

  q_init(&q);
  init_int_constraint(&test);

  printf("\n"
	 "*****************************\n"
	 "*  TEST1: 5/3 x1 - 2/9 y1   *\n"
	 "*****************************\n"
	 "\n");

  q_set_int32(&q, 5, 3);
  int_constraint_add_mono(&test, &q, 0);
  q_set_int32(&q, -2, 9);
  int_constraint_add_fixed_mono(&test, &q, 10, true, &var[10].fixed_value);
  run_test(&test);

  printf("\n"
	 "************************************\n"
	 "*  TEST2: 5/3 x1 - 2/9 y1 + 7/9 y5 *\n"
	 "************************************\n"
	 "\n");
  reset_int_constraint(&test);
  q_set_int32(&q, 5, 3);
  int_constraint_add_mono(&test, &q, 0);
  q_set_int32(&q, -2, 9);
  int_constraint_add_fixed_mono(&test, &q, 10, true, &var[10].fixed_value);
  q_set_int32(&q, 7, 9);
  int_constraint_add_fixed_mono(&test, &q, 14, true, &var[14].fixed_value);
  run_test(&test);

  printf("\n"
	 "*********************************************\n"
	 "*  TEST3: 5/3 x1 + 1/2 x2 - 2/9 y1 + 7/9 y4 *\n"
	 "*********************************************\n"
	 "\n");
  reset_int_constraint(&test);
  q_set_int32(&q, 5, 3);
  int_constraint_add_mono(&test, &q, 0);
  q_set_int32(&q, 1, 2);
  int_constraint_add_mono(&test, &q, 1);
  q_set_int32(&q, -2, 9);
  int_constraint_add_fixed_mono(&test, &q, 10, true, &var[10].fixed_value);
  q_set_int32(&q, 7, 9);
  int_constraint_add_fixed_mono(&test, &q, 13, true, &var[13].fixed_value);
  run_test(&test);

  printf("\n"
	 "****************************************************\n"
	 "*  TEST4: 5/3 x1 + 1/2 x2 - 2/9 y1 + 7/9 y4 + 1/10 *\n"
	 "****************************************************\n"
	 "\n");
  reset_int_constraint(&test);
  q_set_int32(&q, 5, 3);
  int_constraint_add_mono(&test, &q, 0);
  q_set_int32(&q, 1, 2);
  int_constraint_add_mono(&test, &q, 1);
  q_set_int32(&q, -2, 9);
  int_constraint_add_fixed_mono(&test, &q, 10, true, &var[10].fixed_value);
  q_set_int32(&q, 7, 9);
  int_constraint_add_fixed_mono(&test, &q, 13, true, &var[13].fixed_value);
  q_set_int32(&q, 1, 10);
  int_constraint_add_constant(&test, &q);
  run_test(&test);

  printf("\n"
	 "*************************************************************\n"
	 "*  TEST5: 5/3 x1 + 1/2 x2 - 2/9 y1 + 1/3 y2 + 7/9 y4 + 1/10 *\n"
	 "*************************************************************\n"
	 "\n");
  reset_int_constraint(&test);
  q_set_int32(&q, 5, 3);
  int_constraint_add_mono(&test, &q, 0);
  q_set_int32(&q, 1, 2);
  int_constraint_add_mono(&test, &q, 1);
  q_set_int32(&q, -2, 9);
  int_constraint_add_fixed_mono(&test, &q, 10, true, &var[10].fixed_value);
  q_set_int32(&q, 1, 3);
  int_constraint_add_fixed_mono(&test, &q, 11, true, &var[11].fixed_value);
  q_set_int32(&q, 7, 9);
  int_constraint_add_fixed_mono(&test, &q, 13, true, &var[13].fixed_value);
  q_set_int32(&q, 1, 10);
  int_constraint_add_constant(&test, &q);
  run_test(&test);

  printf("\n"
	 "***************************************************\n"
	 "*  TEST6: 5/3 x1 + 1/2 x2 - 2/9 y1 + 1/3 y2 + z5  *\n"
	 "***************************************************\n"
	 "\n");
  reset_int_constraint(&test);
  q_set_int32(&q, 5, 3);
  int_constraint_add_mono(&test, &q, 0);
  q_set_int32(&q, 1, 2);
  int_constraint_add_mono(&test, &q, 1);
  q_set_int32(&q, -2, 9);
  int_constraint_add_fixed_mono(&test, &q, 10, true, &var[10].fixed_value);
  q_set_int32(&q, 1, 3);
  int_constraint_add_fixed_mono(&test, &q, 11, true, &var[11].fixed_value);
  q_set_int32(&q, 7, 9);
  int_constraint_add_fixed_mono(&test, &q, 13, true, &var[13].fixed_value);
  q_set_int32(&q, 1, 1);
  int_constraint_add_fixed_mono(&test, &q, 19, false, &var[19].fixed_value);
  run_test(&test);

  printf("\n"
	 "***************************************************\n"
	 "*  TEST7: 5/3 x1 + 1/2 x2 - 2/9 y1 + 1/3 y2 + z4  *\n"
	 "***************************************************\n"
	 "\n");
  reset_int_constraint(&test);
  q_set_int32(&q, 5, 3);
  int_constraint_add_mono(&test, &q, 0);
  q_set_int32(&q, 1, 2);
  int_constraint_add_mono(&test, &q, 1);
  q_set_int32(&q, -2, 9);
  int_constraint_add_fixed_mono(&test, &q, 10, true, &var[10].fixed_value);
  q_set_int32(&q, 1, 3);
  int_constraint_add_fixed_mono(&test, &q, 11, true, &var[11].fixed_value);
  q_set_int32(&q, 7, 9);
  int_constraint_add_fixed_mono(&test, &q, 13, true, &var[13].fixed_value);
  q_set_int32(&q, 1, 1);
  int_constraint_add_fixed_mono(&test, &q, 18, false, &var[18].fixed_value);
  run_test(&test);

  printf("\n"
	 "***************************************************\n"
	 "*  TEST8: 5/3 x1 + 1/2 x2 - 2/9 y1 + 1/3 y2 + z3  *\n"
	 "***************************************************\n"
	 "\n");
  reset_int_constraint(&test);
  q_set_int32(&q, 5, 3);
  int_constraint_add_mono(&test, &q, 0);
  q_set_int32(&q, 1, 2);
  int_constraint_add_mono(&test, &q, 1);
  q_set_int32(&q, -2, 9);
  int_constraint_add_fixed_mono(&test, &q, 10, true, &var[10].fixed_value);
  q_set_int32(&q, 1, 3);
  int_constraint_add_fixed_mono(&test, &q, 11, true, &var[11].fixed_value);
  q_set_int32(&q, 7, 9);
  int_constraint_add_fixed_mono(&test, &q, 13, true, &var[13].fixed_value);
  q_set_int32(&q, 1, 1);
  int_constraint_add_fixed_mono(&test, &q, 17, false, &var[17].fixed_value);
  run_test(&test);

  printf("\n"
	 "***************************************************\n"
	 "*  TEST9: 5/3 x1 + 1/2 x2 - 2/9 y1 + 2/3 y2 + z3  *\n"
	 "***************************************************\n"
	 "\n");
  reset_int_constraint(&test);
  q_set_int32(&q, 5, 3);
  int_constraint_add_mono(&test, &q, 0);
  q_set_int32(&q, 1, 2);
  int_constraint_add_mono(&test, &q, 1);
  q_set_int32(&q, -2, 9);
  int_constraint_add_fixed_mono(&test, &q, 10, true, &var[10].fixed_value);
  q_set_int32(&q, 2, 3);
  int_constraint_add_fixed_mono(&test, &q, 11, true, &var[11].fixed_value);
  q_set_int32(&q, 7, 9);
  int_constraint_add_fixed_mono(&test, &q, 13, true, &var[13].fixed_value);
  q_set_int32(&q, 1, 1);
  int_constraint_add_fixed_mono(&test, &q, 17, false, &var[17].fixed_value);
  run_test(&test);

  delete_int_constraint(&test);
  q_clear(&q);
}

int main(void) {
  init_rationals();
  init_vartable();
  show_all_vars(stdout);
  test_constraint();
  delete_vartable();
  cleanup_rationals();
  return 0;
}
