/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Print functions for diophantine solver
 */

#include <assert.h>
#include <inttypes.h>

#include "solvers/simplex/dsolver_printer.h"
#include "utils/int_bags.h"
#include "utils/memalloc.h"


/*
 * Print status flag
 */
static const char * const status2string[] = {
  "ready",
  "trivially unsat",
  "unsat by GCD test",
  "simplified",
  "satisfiable",
  "unsat",
};


void dsolver_print_status(FILE *f, dsolver_t *solver) {
  int32_t k;

  fprintf(f, "Status: %s\n", status2string[dsolver_status(solver)]);
  k = dsolver_unsat_row(solver);
  if (k >= 0) {
    fprintf(f, "unsat row = %"PRId32" (id = %"PRId32")\n", k, dsolver_unsat_row_id(solver));
  }
}



/*
 * Hack: this is copied from diophantine_systems.c
 *
 * Search for an element with r_idx == i in the column
 * - return the index k of that element if it's found
 * - return -1 otherwise
 */
static int32_t find_row(dcolumn_t *c, int32_t i) {
  uint32_t l, h, k;

  l = 0;
  h = c->nelems;
  if (h == 0) return -1;

  // binary search
  for (;;) {
    k = (l + h)/2;
    assert(l <= k && k < h);
    if (k == l) break;
    if (c->data[k].r_idx > i) {
      h = k;
    } else {
      l = k;
    }
  }

  if (c->data[k].r_idx == i) {
    return k;
  } else {
    return -1;
  }
}


/*
 * Print monomial (* a <prefix>_<x>)
 */
static void dsolver_print_monomial(FILE *f, rational_t *a, int32_t x, char prefix) {
  if (q_is_one(a)) {
    fprintf(f, "%c_%"PRId32, prefix, x);
  } else if (q_is_minus_one(a)) {
    fprintf(f, "(- %c_%"PRId32")", prefix, x);
  } else {
    fprintf(f, "(* ");
    q_print(f, a);
    fprintf(f, " %c_%"PRId32")", prefix, x);
  }
}



/*
 * Print a polynomial p
 * - prefix =  variable prefix name ('x' or 'i')
 */
static void dsolver_print_poly(FILE *f, polynomial_t *p, char prefix) {
  uint32_t i, n;
  int32_t x;

  n = p->nterms;
  if (n == 0) {
    fprintf(f, "0");

  } else if (n == 1) {
    x = p->mono[0].var;
    if (x == const_idx) {
      q_print(f, &p->mono[0].coeff);
    } else {
      dsolver_print_monomial(f, &p->mono[0].coeff, p->mono[0].var, prefix);
    }
  } else {

    fprintf(f, "(+");
    i = 0;
    x = p->mono[i].var;
    if (x == const_idx) {
      fprintf(f, " ");
      q_print(f, &p->mono[i].coeff);
      i ++;
    }
    while (i < n) {
      fprintf(f, " ");
      dsolver_print_monomial(f, &p->mono[i].coeff, p->mono[i].var, prefix);
      i ++;
    }
    fprintf(f, ")");
  }
}



/*
 * Print a row:
 * - r = row index
 * - v = array of columns where i occurs (as an int_bag)
 * Assumptions on v:
 * - it contains valid column indices with no repetition
 *   (negative numbers in v are skipped, cf. int_bags)
 * - for every k in v, column k is non-null and contain an element for row r
 */
static void dsolver_print_row_core(FILE *f, dsolver_t *solver, int32_t r, int32_t *v) {
  dcolumn_t *c, *b;
  uint32_t i, n, m;
  int32_t k, j;
  char prefix;

  /* if main_rows is 0, variables are written x_<xx>
   * otherwise, variables are written i_<xxx>
   */
  if (solver->main_rows == 0) {
    prefix = 'x';
  } else {
    prefix = 'i';
  }

  // j = constant index for row r, j == -1 means constant = 0
  b = solver->constant_column;
  j = find_row(b, r);

  if (v == NULL) {
    m = 0;
    n = 0;
  } else {
    m = ibag_nelems(v);
    n = ibag_size(v);
  }

  if (m == 0 && j < 0) {
    fprintf(f, "(= 0 0)");
  } else {

    if (m > 1 || j >= 0) {
      fprintf(f, "(= (+");
    } else {
      fprintf(f, "(=");
    }

    // print the matrix element
    for (i=0; i<n; i++) {
      if (v[i] >= 0) {
        assert(v[i] < solver->ncolumns);
        c = solver->column[v[i]];
        assert(c != NULL);
        k = find_row(c, r);
        assert(k >= 0);

        fprintf(f, " ");
        dsolver_print_monomial(f, &c->data[k].coeff, c->var, prefix);
      }
    }

    // print the constant
    if (j >= 0) {
      fprintf(f, " ");
      q_print(f, &b->data[j].coeff);
    }

    // close parentheses
    if (m > 1 || j >= 0) {
      fprintf(f, ") 0)");
    } else {
      fprintf(f, " 0)");
    }
  }
}


/*
 * Print a row:
 * - r = row index
 * - v = array of columns where i occurs (as an integer vector)
 */
static void dsolver_print_row_vector(FILE *f, dsolver_t *solver, int32_t r, ivector_t *v) {
  dcolumn_t *c, *b;
  uint32_t i, n;
  int32_t k, j;

  // j = constant index for row r, j == -1 means constant = 0
  b = solver->constant_column;
  j = find_row(b, r);
  n = v->size;

  if (n == 0 && j < 0) {
    fprintf(f, "(= 0 0)");
  } else {

    if (n > 1 || j >= 0) {
      fprintf(f, "(= (+");
    } else {
      fprintf(f, "(=");
    }

    // print the matrix element
    for (i=0; i<n; i++) {
      assert(0 <= v->data[i] && v->data[i] < solver->ncolumns);
      c = solver->column[v->data[i]];
      assert(c != NULL);
      k = find_row(c, r);
      assert(k >= 0);

      fprintf(f, " ");
      dsolver_print_monomial(f, &c->data[k].coeff, c->var, 'x');
    }

    // print the constant
    if (j >= 0) {
      fprintf(f, " ");
      q_print(f, &b->data[j].coeff);
    }

    // close parentheses
    if (n > 1 || j >= 0) {
      fprintf(f, ") 0)");
    } else {
      fprintf(f, " 0)");
    }
  }
}



/*
 * Print a solution row:
 * - x = variable defined by that row
 * - r = the row index
 * - v = column indices (as an int_bag)
 */
static void dsolver_print_sol_row_core(FILE *f, dsolver_t *solver, int32_t x, int32_t r, int32_t *v) {
  dcolumn_t *c, *b;
  uint32_t i, n, m;
  int32_t k, j;

  // j = constant index for row r, j == -1 means constant = 0
  b = solver->constant_column;
  j = find_row(b, r);

  if (v == NULL) {
    n = 0;
    m = 0;
  } else {
    m = ibag_nelems(v);
    n = ibag_size(v);
  }

  if (m == 0 && j < 0) {
    fprintf(f, "(= x_%"PRId32" 0)", x);
  } else {

    if (m > 1 || j >= 0) {
      fprintf(f, "(= x_%"PRId32" (+", x);
    } else {
      fprintf(f, "(= x_%"PRId32, x);
    }

    // print the constant first
    if (j >= 0) {
      fprintf(f, " ");
      q_print(f, &b->data[j].coeff);
    }

    // print the matrix element
    for (i=0; i<n; i++) {
      if (v[i] >= 0) {
        assert(v[i] < solver->ncolumns);
        c = solver->column[v[i]];
        assert(c != NULL);
        k = find_row(c, r);
        assert(k >= 0);

        fprintf(f, " ");
        dsolver_print_monomial(f, &c->data[k].coeff, c->var, 'i');
      }
    }

    if (m > 1 || j >= 0) {
      fprintf(f, "))");
    } else {
      fprintf(f, ")");
    }
  }

}





/*
 * Print the active row as an equation
 */
void dsolver_print_active_row(FILE *f, dsolver_t *solver) {
  int32_t k;

  k = solver->active_row;
  if (k < 0) {
    fprintf(f, "no active row\n");
  } else {
    fprintf(f, "active row[%"PRId32"]: ", k);
    dsolver_print_row_vector(f, solver, k, &solver->aux_vector);
    fprintf(f, "\n");
  }
}



/*
 * Print row k
 */
void dsolver_print_row(FILE *f, dsolver_t *solver, int32_t k) {
  assert(0 <= k && k < solver->nrows);
  dsolver_print_row_core(f, solver, k, solver->row[k]);
  fprintf(f, "\n");
}


/*
 * Print all the rows (including the empty rows)
 */
void dsolver_print_rows(FILE *f, dsolver_t *solver) {
  int32_t i, n;

  n = solver->nrows;
  for (i=0; i<n; i++) {
    fprintf(f, "row[%"PRId32"]: ", i);
    dsolver_print_row(f, solver, i);
  }
}





/*
 * Print the main rows (skip the empty ones)
 */
void dsolver_print_main_rows(FILE *f, dsolver_t *solver) {
  int32_t i, n;

  n = solver->main_rows;
  for (i=0; i<n; i++) {
    if (solver->row[i] != NULL) {
      fprintf(f, "row[%"PRId32"]: ", i);
      dsolver_print_row(f, solver, i);
    }
  }
}



/*
 * Print elimination record k
 */
void dsolver_print_elim_record(FILE *f, dsolver_t *solver, int32_t k) {
  int32_t x;

  assert(0 <= k && k < solver->elim.nelems);
  x = solver->elim.data[k].var;
  fprintf(f, "(= x_%"PRId32" ", x);
  dsolver_print_poly(f, solver->elim.data[k].poly, 'x');
  fprintf(f, ")\n");
}


/*
 * Print all elimination records
 */
void dsolver_print_elim_rows(FILE *f, dsolver_t *solver) {
  int32_t i, n;

  n = solver->elim.nelems;
  for (i=0; i<n; i++) {
    fprintf(f, "elim[%"PRId32"]: ", i);
    dsolver_print_elim_record(f, solver, i);
  }
}




/*
 * Print solution row for variable x
 */
void dsolver_print_sol_row(FILE *f, dsolver_t *solver, int32_t x) {
  int32_t r;

  assert(1 <= x && x < solver->nvars);
  r = solver->sol_row[x];
  if (r < 0) {
    fprintf(f, "no solution found for x_%"PRId32"\n", x);
  } else {
    assert(0 <= r && r < solver->nrows);
    if (r < solver->main_rows) {
      fprintf(f, "elim[%"PRId32"]: ", r);
      dsolver_print_elim_record(f, solver, r);
      fprintf(f, "\n");
    } else {
      fprintf(f, "def[%"PRId32"]: ", r);
      dsolver_print_sol_row_core(f, solver, x, r, solver->row[r]);
      fprintf(f, "\n");
    }
  }
}


/*
 * Print all the definition rows
 */
void dsolver_print_sol_rows(FILE *f, dsolver_t *solver) {
  int32_t *rows2var;
  uint32_t i, n;
  int32_t j, x;

  // collect the mapping from row id to the corresponding variable
  n = solver->nrows;
  rows2var = (int32_t *) safe_malloc(n * sizeof(int32_t));
  for (i=0; i<n; i++) {
    rows2var[i] = -1;
  }

  n = solver->nvars;
  x = solver->main_rows;
  for (i=0; i<n; i++) {
    j = solver->sol_row[i];
    if (j >= x) {
      assert(j < solver->nrows && rows2var[j] < 0);
      rows2var[j] = i;
    }
  }

  // print all
  n = solver->nrows;
  for (i=solver->main_rows; i<n; i++) {
    x = rows2var[i];
    fprintf(f, "def[%"PRId32"]: ", i);
    dsolver_print_sol_row_core(f, solver, x, i, solver->row[i]);
    fprintf(f, "\n");
  }


  safe_free(rows2var);
}



/*
 * Print the rows_to_process heap
 */
void dsolver_print_rows_to_process(FILE *f, dsolver_t *solver) {
  uint32_t i, n;
  int32_t *h;

  n = generic_heap_nelems(&solver->rows_to_process);
  h = solver->rows_to_process.heap;

  if (n == 0) {
    fprintf(f, "Rows to process: []\n");
  } else {
    fprintf(f, "Rows to process: [%"PRId32, h[1]);
    for (i=2; i<=n; i++) {
      fprintf(f, " %"PRId32, h[i]);
    }
    fprintf(f, "]\n");
  }
}




/*
 * Print the solved columns
 */
void dsolver_print_solved_columns(FILE *f, dsolver_t *solver) {
  dcolumn_t *c;
  uint32_t j, n;
  int32_t r, k;

  n = solver->nsolved;
  if (n == 0) {
    fprintf(f, "No solved columns\n");
  } else {
    fprintf(f, "Solved columns:\n");
    for (r=0; r<solver->nrows; r++) {
      fprintf(f, "row[%"PRId32"]:", r);
      for (j=0; j<n; j++) {
        c = solver->solved_columns[j];
        k = find_row(c, r);
        if (k >= 0) {
          fprintf(f, " ");
          dsolver_print_monomial(f, &c->data[k].coeff, c->var, 'i');
        }
      }
      fprintf(f, "\n");
    }
  }
}



/*
 * Print the basic solution
 */
void dsolver_print_solution(FILE *f, dsolver_t *solver) {
  uint32_t i, n;

  if (solver->base_sol == NULL) {
    fprintf(f, "No solution computed\n");
  } else {
    fprintf(f, "Solution\n");
    n = solver->nvars;
    for (i=0; i<n; i++) {
      if (solver->sol_row[i] >= 0) {
        fprintf(f, "  x_%"PRIu32" = ", i);
        q_print(f, dsolver_get_value(solver, i));
        fprintf(f, "\n");
      }
    }
  }
}



/*
 * Print the general solution
 */
void dsolver_print_gen_solution(FILE *f, dsolver_t *solver) {
  polynomial_t *p;
  uint32_t i, n;

  if (solver->gen_sol == NULL) {
    fprintf(f, "No general solution computed\n");
  } else {
    fprintf(f, "General solution: %"PRIu32" parameters, %"PRIu32" variables\n", solver->num_params, solver->nvars);
    n = solver->nvars;
    for (i=0; i<n; i++) {
      p = dsolver_gen_sol(solver, i);
      if (p != NULL && solver->sol_row[i] >= 0) {
        fprintf(f, "  x_%"PRIu32" = ", i);
        dsolver_print_poly(f, p, 'i');
        fprintf(f, "\n");
      }
    }
  }
}



/*
 * Print a row in a matrix or tableau
 * - a variable k of index 1 ... m-1 is printed as x_<k>
 * - a variable k of index m ... is printed as i_<k>
 */
static void dsolver_print_matrix_row(FILE *f, row_t *row, int32_t m) {
  uint32_t i, n;
  int32_t x;
  char prefix;

  n = row->size;
  if (n == 0) {
    fputs("(= 0 0)", f); // empty row (should not happen)
  } else {

    if (n == 1) {
      fputs("(=", f);
    } else {
      fputs("(= (+", f);
    }

    for (i=0; i<n; i++) {
      x = row->data[i].c_idx;
      if (x >= 0) {
        fputc(' ', f);
        if (x == const_idx) {
          q_print(f, &row->data[i].coeff);
        } else {
          prefix = x < m ? 'x' : 'i';
          dsolver_print_monomial(f, &row->data[i].coeff, x, prefix);
        }
      }
    }

    if (n == 1) {
      fputs("0)", f);
    } else {
      fputs(") 0)", f);
    }
  }
}


/*
 * Print a variable x
 * - m = as above = index of the first variable printed as i_<k>
 */
static void dsolver_print_var(FILE *f, int32_t x, int32_t m) {
  char prefix;
  prefix = x < m ? 'x' : 'i';
  fprintf(f, "%c_%"PRId32, prefix, x);
}


/*
 * Print matrix or tableau
 */
void dsolver_print_tableau(FILE *f, matrix_t *matrix, int32_t param_idx) {
  uint32_t i, n;
  int32_t x;

  n = matrix->nrows;
  for (i=0; i<n; i++) {
    fprintf(f, "  row[%"PRIu32, i);
    x = matrix_basic_var(matrix, i);
    if (x >= 0) {
      fputs(", ", f);
      dsolver_print_var(f, x, param_idx);
    }
    fputs("]:  ", f);
    dsolver_print_matrix_row(f, matrix->row[i], param_idx);
    fputc('\n', f);
  }
}



