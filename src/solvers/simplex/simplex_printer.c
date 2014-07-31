/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/**************************
 *  PRINT SIMPLEX SOLVER  *
 *************************/

#include <inttypes.h>

#include "solvers/cdcl/smt_core_printer.h"
#include "solvers/egraph/egraph_printer.h"
#include "solvers/simplex/simplex_printer.h"


/*
 * VARIABLE TABLE
 */
static void print_avar(FILE *f, arith_vartable_t *table, thvar_t v) {
  if (arith_var_is_int(table, v)) {
    fprintf(f, "i!%"PRId32, v);
  } else {
    fprintf(f, "z!%"PRId32, v);
  }
}

static void print_avar_power(FILE *f, arith_vartable_t *table, varexp_t *p) {
  print_avar(f, table, p->var);
  if (p->exp > 1) {
    fprintf(f, "^%"PRIu32, p->exp);
  }
}

static void print_avar_product(FILE *f, arith_vartable_t *table, pprod_t *p) {
  int32_t i, n;

  n = p->len;
  if (n == 0) {
    fprintf(f, "1");
  } else {
    i = 0;
    for (;;) {
      print_avar_power(f, table, p->prod + i);
      i ++;
      if (i == n) break;
      fputs(" * ", f);
    }
  }
}

static void print_avar_monomial(FILE *f, arith_vartable_t *table, thvar_t v, rational_t *coeff, bool first) {
  bool negative;
  bool abs_one;

  negative = q_is_neg(coeff);

  if (negative) {
    if (first) {
      fputs("- ", f);
    } else {
      fputs(" - ", f);
    }
    abs_one = q_is_minus_one(coeff);
  } else {
    if (! first) {
      fputs(" + ", f);
    }
    abs_one = q_is_one(coeff);
  }

  if (v == const_idx) {
    q_print_abs(f, coeff);
  } else {
    if (! abs_one) {
      q_print_abs(f, coeff);
      fputs(" * ", f);
    }
    print_avar(f, table, v);
  }
}

static void print_avar_poly(FILE *f, arith_vartable_t *table, polynomial_t *p) {
  uint32_t i, n;

  n = p->nterms;
  if (n == 0) {
    fputc('0', f);
  } else {
    for (i=0; i<n; i++) {
      print_avar_monomial(f, table, p->mono[i].var, &p->mono[i].coeff, i == 0);
    }
  }
}


void print_arith_vartable(FILE *f, arith_vartable_t *table) {
  uint32_t i, n;

  n = table->nvars;
  for (i=0; i<n; i++) {
    print_avar(f, table, i);
    switch (arith_var_kind(table, i)) {
    case AVAR_FREE:
      break;

    case AVAR_POLY:
      fputs(" := ", f);
      print_avar_poly(f, table, arith_var_poly_def(table, i));
      break;

    case AVAR_PPROD:
      fputs(" := ", f);
      print_avar_product(f, table, arith_var_product_def(table, i));
      break;

    case AVAR_CONST:
      fputs(" := ", f);
      q_print(f, arith_var_rational_def(table, i));
      break;
    }

    if (arith_var_has_eterm(table, i)) {
      fputs(" --> ", f);
      print_eterm_id(f, arith_var_eterm(table, i));
    }
    fputc('\n', f);
  }
}


/*
 * ARITHMETIC ATOMS
 */
static void print_arith_atom_op(FILE *f, arithatm_tag_t tag) {
  switch (tag) {
  case GE_ATM:
    fputs(" >= ", f);
    break;
  case LE_ATM:
    fputs(" <= ", f);
    break;
  case EQ_ATM:
    fputs(" == ", f);
    break;
  default:
    fputs(" <badop> ", f);
    break;
  }
}

static void print_arith_atom(FILE *f, arith_vartable_t *table, arith_atom_t *atom) {
  print_avar(f, table, var_of_atom(atom));
  print_arith_atom_op(f, tag_of_atom(atom));
  q_print(f, &atom->bound);
}

void print_arith_atomtable(FILE *f, arith_vartable_t *vtbl, arith_atomtable_t *atbl) {
  uint32_t i, n;
  arith_atom_t *a;

  n = atbl->natoms;
  a = atbl->atoms;
  for (i=0; i<n; i++) {
    print_bvar(f, a[i].boolvar);
    fputs(" := ", f);
    print_arith_atom(f, vtbl, a + i);
    fputs("\t\t", f);
    print_bval(f, bvar_value(atbl->core, a[i].boolvar));
    fputc('\n', f);
  }
}


/*
 * MATRIX
 */

// space for correct alignment when we print xxx[i] in a matrix with n rows
static void print_space(FILE *f, uint32_t i, uint32_t n) {
  uint32_t k;

  k = 1;
  while (10 * k <= i) {
    k *= 10;
  }

  while (10 * k < n) {
    fputc(' ', f);
    k *= 10;
  }
}


// row is printed as a_1 x_1 + .... + a_n x_n == 0
static void print_row(FILE *f, arith_vartable_t *vtbl, row_t *row) {
  uint32_t i, n;
  thvar_t x;
  bool first;

  first = true;
  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      print_avar_monomial(f, vtbl, x, &row->data[i].coeff, first);
      first = false;
    }
  }
  if (first) {
    // nothing printed so the row is empty
    fputc('0', f);
  }
  fputs(" == 0", f);
}


void print_matrix(FILE *f, arith_vartable_t *vtbl, matrix_t *matrix) {
  uint32_t i, n;

  n = matrix->nrows;
  for (i=0; i<n; i++) {
    fprintf(f, "  row[%"PRIu32"]:   ", i);
    print_space(f, i, n);
    print_row(f, vtbl, matrix->row[i]);
    fputc('\n', f);
  }
  fputc('\n', f);
}


void print_elim_matrix(FILE *f, arith_vartable_t *vtbl, elim_matrix_t *elim) {
  uint32_t i, n;

  n = elim->nrows;
  for (i=0; i<n; i++) {
    fprintf(f, "  elim[%"PRIu32"]:   ", i);
    print_space(f, i, n);
    print_avar_poly(f, vtbl, elim->row[i]);
    fputs("  (", f);
    print_avar(f, vtbl, elim->base_var[i]);
    fputs(")\n", f);
  }
  fputc('\n', f);
}


void print_fixed_var_vector(FILE *f, arith_vartable_t *vtbl, fvar_vector_t *fvars) {
  uint32_t i, n;

  n = fvars->nvars;
  for (i=0; i<n; i++) {
    fprintf(f, "  fixed[%"PRIu32"]:   ", i);
    print_space(f, i, n);
    print_avar(f, vtbl, fvars->fvar[i].var);
    fputs(" == ", f);
    q_print(f, &fvars->fvar[i].value);
    fputc('\n', f);
  }
  fputc('\n', f);
}



/*
 * Bounds on variable x
 */
static void print_avar_bounds(FILE *f, simplex_solver_t *solver, thvar_t x) {
  int32_t lb, ub;

  lb = arith_var_lower_index(&solver->vtbl, x);
  ub = arith_var_upper_index(&solver->vtbl, x);
  if (lb >= 0 || ub >= 0) {
    fputs("  ", f);
    if (lb >= 0) {
      xq_print(f, solver->bstack.bound + lb);
      fputs(" <= ", f);
    }
    print_avar(f, &solver->vtbl, x);
    if (ub >= 0) {
      fputs(" <= ", f);
      xq_print(f, solver->bstack.bound + ub);
    }
    fputc('\n', f);
  }
}


/*
 * Value of variable x
 */
static void print_avar_value(FILE *f, arith_vartable_t *vtbl, thvar_t x) {
  fputs("  val[", f);
  print_avar(f, vtbl, x);
  fputs("] = ", f);
  xq_print(f, arith_var_value(vtbl, x));
}


/*
 * Bounds + value of x + row where x is basic
 */
static void print_avar_full(FILE *f, simplex_solver_t *solver, thvar_t x) {
  int32_t lb, ub, r;

  lb = arith_var_lower_index(&solver->vtbl, x);
  ub = arith_var_upper_index(&solver->vtbl, x);
  r = matrix_basic_row(&solver->matrix, x);

  fputs("  ", f);
  print_avar(f, &solver->vtbl, x);
  fputs(" = ", f);
  xq_print(f, arith_var_value(&solver->vtbl, x));
  fputc('\t', f);

  if (lb >= 0 || ub >= 0) {
    if (lb >= 0) {
      xq_print(f, solver->bstack.bound + lb);
      fputs(" <= ", f);
    }
    print_avar(f, &solver->vtbl, x);
    if (ub >= 0) {
      fputs(" <= ", f);
      xq_print(f, solver->bstack.bound + ub);
    }
  } else {
    fputs("no bounds", f);
  }

  if (r >= 0) {
    fprintf(f, "\t\tbasic in row[%"PRIu32"]\n", r);
  } else {
    fprintf(f, "\t\tnon basic\n");
  }
}


/*
 * Bounds + value of x
 */
static void print_avar_bounds_and_value(FILE *f, simplex_solver_t *solver, thvar_t x) {
  int32_t lb, ub;

  lb = arith_var_lower_index(&solver->vtbl, x);
  ub = arith_var_upper_index(&solver->vtbl, x);

  fputs("  ", f);
  print_avar(f, &solver->vtbl, x);
  fputs(" = ", f);
  xq_print(f, arith_var_value(&solver->vtbl, x));

  if (lb >= 0 || ub >= 0) {
    fputc('\t', f);
    if (lb >= 0) {
      xq_print(f, solver->bstack.bound + lb);
      fputs(" <= ", f);
    }
    print_avar(f, &solver->vtbl, x);
    if (ub >= 0) {
      fputs(" <= ", f);
      xq_print(f, solver->bstack.bound + ub);
    }
  }

  fputc('\n', f);
}


/*
 * Simplex components
 */
void print_simplex_vars(FILE *f, simplex_solver_t *solver) {
  print_arith_vartable(f, &solver->vtbl);
}

void print_simplex_atoms(FILE *f, simplex_solver_t *solver) {
  print_arith_atomtable(f, &solver->vtbl, &solver->atbl);
}

void print_simplex_atom(FILE *f, simplex_solver_t *solver, int32_t id) {
  print_arith_atom(f, &solver->vtbl, arith_atom(&solver->atbl, id));
}

void print_simplex_row(FILE *f, simplex_solver_t *solver, row_t *row) {
  print_row(f, &solver->vtbl, row);
}

void print_simplex_matrix(FILE *f, simplex_solver_t *solver) {
  print_matrix(f, &solver->vtbl, &solver->matrix);
}

void print_simplex_saved_rows(FILE *f, simplex_solver_t *solver) {
  pvector_t *v;
  uint32_t i, n;

  v = &solver->saved_rows;
  n = v->size;
  for (i=0; i<n; i++) {
    fprintf(f, "saved[%"PRIu32"]: ", i);
    print_avar_poly(f, &solver->vtbl, v->data[i]);
    fputc('\n', f);
  }
  fputc('\n', f);
}


void print_simplex_basic_vars(FILE *f, simplex_solver_t *solver) {
  matrix_t *matrix;
  uint32_t i, n;
  int32_t x;

  matrix = &solver->matrix;
  n = matrix->nrows;
  for (i=0; i<n; i++) {
    fprintf(f, "  row[%"PRIu32"]: ", i);
    x = matrix->base_var[i];
    if (x >=0 ) {
      fputs("basic var = ", f);
      print_avar(f, &solver->vtbl, x);
      fputc('\n', f);
    } else {
      fputs("no basic var\n", f);
    }
  }
  fputc('\n', f);
}


void print_simplex_bounds(FILE *f, simplex_solver_t *solver) {
  uint32_t i, n;

  n = num_arith_vars(&solver->vtbl);
  for (i=0; i<n; i++) {
    print_avar_bounds(f, solver, i);
  }
}

void print_simplex_assignment(FILE *f, simplex_solver_t *solver) {
  uint32_t i, n;

  n = num_arith_vars(&solver->vtbl);
  for (i=0; i<n; i++) {
    print_avar_value(f, &solver->vtbl, i);
    fputc('\n', f);
  }
}

void print_simplex_bounds_and_assignment(FILE *f, simplex_solver_t *solver) {
  uint32_t i, n;

  n = num_arith_vars(&solver->vtbl);
  for (i=0; i<n; i++) {
    print_avar_bounds_and_value(f, solver, i);
  }
  fputc('\n', f);
}

void print_simplex_allvars(FILE *f, simplex_solver_t *solver) {
  uint32_t i, n;

  n = num_arith_vars(&solver->vtbl);
  for (i=0; i<n; i++) {
    print_avar_full(f, solver, i);
  }
  fputc('\n', f);
}


void print_simplex_vars_summary(FILE *f, simplex_solver_t *solver) {
  arith_vartable_t *table;
  uint32_t i, n;
  int32_t lb, ub;

  table = &solver->vtbl;
  n = num_arith_vars(table);
  for (i=0; i<n; i++) {
    lb = arith_var_lower_index(&solver->vtbl, i);
    ub = arith_var_upper_index(&solver->vtbl, i);

    if (matrix_is_basic_var(&solver->matrix, i)) {
      fputs(" b ", f);
    } else {
      fputs("   ", f);
    }
    print_avar(f, table, i);
    fputs(" = ", f);
    xq_print(f, arith_var_value(&solver->vtbl, i));


    if (lb >= 0 || ub >= 0) {
      fputs("\t", f);
      if (lb >= 0) {
        xq_print(f, solver->bstack.bound + lb);
        fputs(" <= ", f);
      }
      print_avar(f, &solver->vtbl, i);
      if (ub >= 0) {
        fputs(" <= ", f);
        xq_print(f, solver->bstack.bound + ub);
      }
    }

    if (arith_var_has_eterm(table, i)) {
      fputs("\t\teterm: ", f);
      print_eterm_id(f, arith_var_eterm(table, i));
    }
    if (arith_var_def_is_poly(table, i)) {
      fputs("\t\tdef: ", f);
      print_avar_poly(f, table, arith_var_poly_def(table, i));
    } else if (arith_var_def_is_product(table, i)) {
      fputs("\t\tdef: ", f);
      print_avar_product(f, table, arith_var_product_def(table, i));
    }
    fputc('\n', f);
  }
  fputc('\n', f);
}


void print_simplex_vardef(FILE *f, simplex_solver_t *solver, thvar_t v) {
  arith_vartable_t *table;

  table = &solver->vtbl;
  print_avar(f, table, v);
  if (arith_var_def_is_poly(table, v)) {
    fputs(" := ", f);
    print_avar_poly(f, table, arith_var_poly_def(table, v));
  } else if (arith_var_def_is_product(table, v)) {
    fputs(" := ", f);
    print_avar_product(f, table, arith_var_product_def(table, v));
  }
  fputc('\n', f);
}

void print_simplex_var(FILE *f, simplex_solver_t *solver, thvar_t v) {
  print_avar(f, &solver->vtbl, v);
}

void print_simplex_var_value(FILE *f, simplex_solver_t *solver, thvar_t v) {
  xq_print(f, arith_var_value(&solver->vtbl, v));
}

void print_simplex_var_bounds(FILE *f, simplex_solver_t *solver, thvar_t v) {
  print_avar_bounds(f, solver, v);
}

void print_simplex_atomdef(FILE *f, simplex_solver_t *solver, bvar_t v) {
  void *atm;
  arith_atom_t *a;
  int32_t i;

  atm = get_bvar_atom(solver->core, v);
  i = arithatom_tagged_ptr2idx(atm);
  a = arith_atom(&solver->atbl, i);
  assert(a->boolvar == v);
  print_bvar(f, v);
  fputs(" := ", f);
  print_arith_atom(f, &solver->vtbl, a);
  fputc('\n', f);
}


void print_simplex_atom_of_literal(FILE *f, simplex_solver_t *solver, literal_t l) {
  void *atm;
  arith_atom_t *a;
  bvar_t v;
  int32_t i;

  v = var_of(l);
  assert(bvar_has_atom(solver->core, v));
  atm = bvar_atom(solver->core, v);
  assert(atom_tag(atm) == ARITH_ATM_TAG);
  i = arithatom_tagged_ptr2idx(atm);
  a = arith_atom(&solver->atbl, i);
  assert(a->boolvar == v);

  if (is_neg(l)) {
    fputs("(not ", f);
  }
  print_arith_atom(f, &solver->vtbl, a);
  if (is_neg(l)) {
    fputc(')', f);
  }
}


void print_simplex_buffer(FILE *f, simplex_solver_t *solver) {
  poly_buffer_t *b;
  uint32_t i, n;

  b = &solver->buffer;
  n = b->nterms;
  if (n == 0) {
    fputc('0', f);
  } else {
    for (i=0; i<n; i++) {
      print_avar_monomial(f, &solver->vtbl, b->mono[i].var, &b->mono[i].coeff, i == 0);
    }
  }
}


void print_simplex_bound(FILE *f, simplex_solver_t *solver, uint32_t i) {
  fprintf(f, "bound[%"PRIu32"]: ", i);
  if (i < solver->bstack.top) {
    print_avar(f, &solver->vtbl, solver->bstack.var[i]);
    if (arith_tag_get_type(solver->bstack.tag[i]) == ATYPE_UB) {
      fputs(" <= ", f);
    } else {
      fputs(" >= ", f);
    }
    xq_print(f, solver->bstack.bound + i);
  } else {
    fprintf(f, "<INVALID BOUND INDEX>");
  }
}




/*
 * FLAGS/BASE LEVEL
 */
static char *bool2string(bool x) {
  return x ? "true" : "false";
}

void print_simplex_flags(FILE *f, simplex_solver_t *solver) {
  fprintf(f, "base level:     %"PRIu32"\n", solver->base_level);
  fprintf(f, "decision level: %"PRIu32"\n", solver->decision_level);
  fprintf(f, "matrix ready:   %s\n", bool2string(solver->matrix_ready));
  fprintf(f, "tableau ready:  %s\n", bool2string(solver->tableau_ready));
  fprintf(f, "save rows:      %s\n", bool2string(solver->save_rows));
}



/*
 * Print row in a simplified form: replace fixed variables by their value
 */
void print_simplex_reduced_row(FILE *f, simplex_solver_t *solver, row_t *row) {
  arith_vartable_t *vtbl;
  arith_bstack_t *bstack;
  rational_t q;
  uint32_t i, n;
  thvar_t x;
  bool first;
  int32_t l, u;

  vtbl = &solver->vtbl;
  bstack = &solver->bstack;

  // compute the constant
  q_init(&q);
  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      l = arith_var_lower_index(&solver->vtbl, x);
      u = arith_var_upper_index(&solver->vtbl, x);
      if (l >= 0 && u >= 0 && xq_eq(bstack->bound + l, bstack->bound + u)) {
        // x is a a fixed variable
        assert(xq_eq(bstack->bound + l, arith_var_value(vtbl, x)));
        assert(xq_is_rational(arith_var_value(vtbl, x)));
        q_addmul(&q, &row->data[i].coeff, &arith_var_value(vtbl, x)->main);
      }
    }
  }

  // print the non-constant monomials and q
  first = true;
  if (q_is_nonzero(&q)) {
    print_avar_monomial(f, vtbl, const_idx, &q, first);
    first = false;
  }

  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      l = arith_var_lower_index(&solver->vtbl, x);
      u = arith_var_upper_index(&solver->vtbl, x);
      if (l < 0 || u < 0 || xq_neq(bstack->bound + l, bstack->bound + u)) {
        // x is not a fixed variable
        print_avar_monomial(f, vtbl, x, &row->data[i].coeff, first);
        first = false;
      }
    }
  }

  if (first) {
    // nothing printed so the row is empty
    fputc('0', f);
  }
  fputs(" == 0", f);

  q_clear(&q);
}



/*
 * Variant of print_simplex_bounds
 */
void print_simplex_bounds2(FILE *f, simplex_solver_t *solver) {
  uint32_t i, n;
  int32_t lb, ub;

  n = num_arith_vars(&solver->vtbl);
  for (i=0; i<n; i++) {
    lb = arith_var_lower_index(&solver->vtbl, i);
    ub = arith_var_upper_index(&solver->vtbl, i);
    if (lb >= 0 && ub >= 0) {
      if (xq_neq(solver->bstack.bound + lb, solver->bstack.bound + ub)) {
        fputs("  ", f);
        xq_print(f, solver->bstack.bound + lb);
        fprintf(f, " <= x_%"PRIu32" <= ", i);
        xq_print(f, solver->bstack.bound + ub);
        fputc('\n', f);
      }
    } else if (lb >= 0) {
      fputs("  ", f);
      xq_print(f, solver->bstack.bound + lb);
      fprintf(f, " <= x_%"PRIu32"\n", i);
    } else if (ub >= 0) {
      fprintf(f, "  x_%"PRIu32" <= ", i);
      xq_print(f, solver->bstack.bound + ub);
      fputc('\n', f);
    }
  }
}


