/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <assert.h>
#include <stdbool.h>

#include "solvers/simplex/int_constraint_printer.h"
#include "solvers/simplex/simplex_printer.h"

static void print_sign(FILE *f, bool neg, bool first) {
  if (first) {
    if (neg) {
      fputs("- ", f);
    }
  } else {
    if (neg) {
      fputs(" - ", f);
    } else {
      fputs(" + ", f);
    }
  }
}

static void show_monomial(FILE *f, simplex_solver_t *solver, rational_t *a, int32_t x, bool first) {
  bool negative;
  bool abs_one;

  assert(q_is_nonzero(a));

  negative = q_is_neg(a);
  abs_one = negative ? q_is_minus_one(a) : q_is_one(a);

  print_sign(f, negative, first);
  if (!abs_one) {
    q_print_abs(f, a);
    fprintf(f, " ");
  }
  print_simplex_var(f, solver, x);
}

static void show_constant(FILE *f, rational_t *a, bool first) {
  if (q_is_nonzero(a)) {
    print_sign(f, q_is_neg(a), first);
    q_print_abs(f, a);
  }
}

static void show_sum(FILE *f, simplex_solver_t *solver, monomial_t *p, uint32_t n, bool first) {
  uint32_t i;

  for (i=0; i<n; i++) {
    show_monomial(f, solver, &p[i].coeff, p[i].var, first);
    first = false;
  }
}

static void show_fixed_vars(FILE *f, simplex_solver_t *solver, int_constraint_t *cnstr) {
  uint32_t i, n;
  int32_t x;

  n = cnstr->fixed_nterms;
  if (n == 0) {
    fprintf(f, "No fixed variable\n");
  } else {
    fprintf(f, "Fixed variables:\n");
    for (i=0; i<n; i++) {
      x = cnstr->fixed_sum[i].var;
      fprintf(f, "  val[");
      print_simplex_var(f, solver, x);
      fprintf(f, "] = ");
      q_print(f, &cnstr->fixed_val[i]);
      printf("\n");
    }
  }
}

void print_int_constraint(FILE *f, simplex_solver_t *solver, int_constraint_t *cnstr) {
  bool first;

  fprintf(f, "  IsInt(");
  first = true;
  show_sum(f, solver, cnstr->sum, cnstr->sum_nterms, first);
  first &= (cnstr->sum_nterms == 0);
  show_sum(f, solver, cnstr->fixed_sum, cnstr->fixed_nterms, first);
  first &= (cnstr->fixed_nterms == 0);
  show_constant(f, &cnstr->constant, first);
  fprintf(f, ")\n");
  show_fixed_vars(f, solver, cnstr);
}
