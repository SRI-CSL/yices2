#include <stdlib.h>
#include <stdio.h>

#include "rationals.h"
#include "vectors.h"
#include "buffers.h"
#include "matrices.h"
#include "matrix_printers.h"


/*
 * Format: each triple is <c_idx, a, b> to
 * represent element a/b with column index c_idx.
 * Triple <-1, 0, 0> is the end of the row.
 */
static int row_test[200][3] = {
  { 0, -1, 1}, { 3, -2, 1}, { 5, 1, 1}, { 2, -7, 8}, { -1, 0, 0},
  { 0, -1, 2}, { 2, 2, 1}, {4, 1, 2}, {7, 1, 4}, {-1, 0, 0},
  { 1, 1, 1}, { 2, 1, 3}, { 3, -1, 3}, { 10, 2, 3}, {-1, 0, 0},
  { 5, 3, 1}, { 10, 2, 1}, {6, -1, 1}, {3, 1, 4}, {-1, 0, 0},
  { 6, 2, 1}, { 7, -2, 1}, { 11, -3, 5}, {0, 1, 2}, {-1, 0, 0},
  { 6, 1, 1}, { 8, -1, 1}, {12, 1, 1}, {2, -3, 1}, {-1, 0, 0},
  { 9, 1, 1}, {12, 2, 1}, {14, -1, 4}, {2, 5, 1}, {-1, 0, 0},
  {10, -3, 1}, {13, 1, 4}, {15, 1, 4}, {0, 1, 4}, {-1, 0, 0},
  {10, 2, 1}, {13, 1, 3}, {2, -1, 2}, {3, 7, 5}, {8, 1, 3}, {-1, 0, 0},
  { 9, 1, 1}, {7, 1, 1}, {12, 1, 1}, {-1, 0, 0},
  { -1, 0, 0},
};



static int elim_test[16] = {
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
};

static int check_test[10] = {
  0, 1, 2, 3, 4, 5, 6, 7, 8, 10
};



/*
 * Global variables:
 */
static vector_t *build_vector;


/*
 * Build a matrix from row data.
 */
static void build_from_rows(matrix_t *m, int d[][3], int n) {
  int i, t, c_idx, den, num;

  t = 0;
  for (i=0; i<n; i++) {
    empty_vector(build_vector);
    c_idx = d[t][0];
    while (c_idx >= 0) {
      num = d[t][1];
      den = d[t][2];
      if (den == 1) {
	add_int_elem_to_vector(&build_vector, c_idx, num);
      } else {
	add_si_elem_to_vector(&build_vector, c_idx, num, den);
      }
      t ++;
      c_idx = d[t][0];
    }
    add_vector_as_new_row(m, build_vector);
    t ++;
  }
}



static void print_factorization(factorization_t *fact) {
  printf("\nMatrix U\n");
  print_triangular_matrix_poly(stdout, &fact->umatrix);
  //  printf("\n");
  //  print_triangular_matrix(stdout, &fact->umatrix);
  printf("\nMatrix L\n");
  print_triangular_matrix_poly(stdout, &fact->lmatrix);
  printf("\nETA FILE\n");
  print_eta_file(stdout, &fact->f);
  fflush(stdout);
  
}


static void extract_column(compact_matrix_t *m, int c_idx, buffer_t *buffer) {
  int *vindex;
  vector_elem_t *v;

  vindex = m->columns.vindex;
  v = m->columns.vblock + vindex[c_idx];
  clear_buffer(buffer);
  copy_vectelem_in_buffer(buffer, v, vindex[c_idx + 1] - vindex[c_idx]);
}

static void set_row(int r_idx, buffer_t *buffer) {
  clear_buffer(buffer);
  set_int_elem_in_buffer(buffer, r_idx, 1);
}


/*
 * Refactor: recompute LU factorization for fact, keeping the same
 * basic variables.
 */
static void refactor(factorization_t *fact, compact_matrix_t *m) {
  int i, n, p, c;
  int *base;

  n = fact->dim;
  p = fact->nvars;

  if (n != m->nrows || p != m->ncolumns) {
    printf("**** Refactor: incompatible dimensions ****\n");
    printf("fact->dim = %d, m->nrows = %d\n", n, m->nrows);
    printf("fact->nvars = %d, m->ncolumns = %d\n", p, m->ncolumns);
    return;
  }

  base = (int *) malloc(n * sizeof(int));

  for (i=0; i<p; i++) {
    c = fact->var_col[i];
    if (c >= 0) {
      base[c] = i;
    }
  }

  if (compute_factorization(fact, m, base) < 0) {
    printf("\n**** Refactor: singular matrix ****\n");
  }

  free(base);
}

/*
 * Check an LU factorization:
 * - m = compact matrix
 * - fact = factorization
 */
static void check_factorization(factorization_t *fact, compact_matrix_t *m) {
  int i, n, p, c;
  buffer_t *buffer;

  n = fact->dim;
  p = fact->nvars;
  if (n != m->nrows || p != m->ncolumns) {
    printf("**** Check factorization: incompatible dimensions ****\n");
    printf("fact->dim = %d, m->nrows = %d\n", n, m->nrows);
    printf("fact->nvars = %d, m->ncolumns = %d\n", p, m->ncolumns);
    return;
  }

  buffer = new_buffer(n);

  for (i=0; i<p; i++) {
    c = fact->var_col[i];
    if (c >= 0) {
      printf("Checking basic variable x%d: ", i);
      extract_column(m, i, buffer);
      factorization_solve_column(fact, buffer, 0);
      if (buffer->nelems == 1 && 
	  buffer->tag[c] == ACTIVE_COEFF &&
	  rat_is_one(buffer->q + c)) {
	printf("OK\n");
      } else {
	printf("Failed\n\n");
	printf("--- Column x%d ---\n", i);
	print_vectelem(stdout, m->columns.vblock + m->columns.vindex[i], 
		       m->columns.vindex[i+1] - m->columns.vindex[i], "C");
	printf("\n--- Solution  ---\n");
	print_buffer(stdout, buffer, "x");
	printf("\n");
	fflush(stdout);       
      }
    }
  }

  delete_buffer(buffer);
}

/*
 * Print all columns after an LU factorization:
 * - m = compact matrix
 * - fact = factorization
 */
static void check_all_factorization(factorization_t *fact, compact_matrix_t *m) {
  int i, n, c, p;
  buffer_t *buffer;

  n = fact->dim;
  p = fact->nvars;
  if (n != m->nrows || p != m->ncolumns) {
    printf("**** Check all factorization: incompatible dimensions ****\n");
    printf("fact->dim = %d, m->nrows = %d\n", n, m->nrows);
    printf("fact->nvars = %d, m->ncolumns = %d\n", p, m->ncolumns);
    return;
  }

  buffer = new_buffer(n);

  for (i=0; i<p; i++) {
    c = fact->var_col[i];
    if (c >= 0) {
      printf("\n---- Variable x%d (basic in column %d) ----\n", i, c);
    } else {
      printf("\n---- Variable x%d (nonbasic) ----\n", i);
    }
    extract_column(m, i, buffer);
    print_buffer(stdout, buffer, "C");
    printf("\n");
    factorization_solve_column(fact, buffer, 0);
    printf("\n--- Solution  ---\n");
    print_buffer(stdout, buffer, "x");
    printf("\n");
    fflush(stdout);
  }  

  for (i=0; i<n; i++) {
    printf("\n---- Row %d ----\n", i);
    set_row(i, buffer);
    print_buffer(stdout, buffer, "R");
    printf("\n");
    factorization_solve_row(fact, buffer);
    printf("\n--- Solution ---\n");
    print_buffer(stdout, buffer, "y");
    printf("\n");
    fflush(stdout);
  }

  delete_buffer(buffer);
}


/*
 * Print all rows after an LU factorization:
 * - m = compact matrix
 * - fact = factorization
 */
static void gen_all_rows(factorization_t *fact, compact_matrix_t *m) {
  int i, j, n, p, q, r;
  buffer_t *buffer, *row_buffer;
  int *vindex;
  vector_elem_t *v;

  n = fact->dim;
  p = fact->nvars;
  if (n != m->nrows || p != m->ncolumns) {
    printf("**** Check all factorization: incompatible dimensions ****\n");
    printf("fact->dim = %d, m->nrows = %d\n", n, m->nrows);
    printf("fact->nvars = %d, m->ncolumns = %d\n", p, m->ncolumns);
    return;
  }

  buffer = new_buffer(n);
  row_buffer = new_buffer(p);
  vindex = m->rows.vindex;

  for (i=0; i<n; i++) {
    printf("\n---- Row %d ----\n", i);
    set_row(i, buffer);
    print_buffer(stdout, buffer, "R");
    printf("\n");
    factorization_solve_row(fact, buffer);
    printf("\n--- Solution ---\n");
    print_buffer(stdout, buffer, "y");
    printf("\n");

    // compute the row
    q = buffer->nelems;
    for (j=0; j<q; j++) {
      r = buffer->active[j];
      v = m->rows.vblock + vindex[r];
      addmul_vectelem_to_buffer(row_buffer, v, vindex[r+1] - vindex[r], buffer->q + r);
    }

    printf("\n--- Row %d ---\n", i);
    normalize_buffer(row_buffer);
    print_buffer(stdout, row_buffer, "a");      
    clear_buffer(row_buffer);

    fflush(stdout);
  }

  delete_buffer(buffer);
  delete_buffer(row_buffer);
}


static void basic_test() {
  gauss_matrix_t *m1;
  compact_matrix_t *full_mat;
  factorization_t *fact;
  buffer_t *buffer;
  int i, j, x;

  m1 = new_gauss_matrix(0, 0);
  build_from_rows(&m1->m, row_test, 11);
  printf("\n **** Original matrix ****\n");
  print_matrix_poly(stdout, &m1->m);
  printf("\n");
  fflush(stdout);

  printf("\nTRIANGULATION\n\n");
  gauss_elim_prepare(m1);
  eliminate_all_columns(m1);
  full_mat = construct_triangular_matrix(m1);
  printf("\n**** Extracted full matrix ****\n");
  print_compact_matrix(stdout, full_mat);
  printf("\n\n");
  fflush(stdout);


  buffer = new_buffer(full_mat->nrows);

  // check factorization
  fact = create_factorization(full_mat);
  printf("\n**** Initial factorization ****\n");
  print_factorization(fact);
  check_factorization(fact, full_mat);

  // test LU fact
  printf("\n**** LU Fact: columns 0 to 8 and 10 ****\n");
  x = compute_factorization(fact, full_mat, check_test);
  if (x >= 0) {
    check_factorization(fact, full_mat);
  } else {
    printf("\n**** Singular matrix ****\n");
    goto end;
  }

  // test LU fact
  printf("\n**** LU Fact: columns 0 to 9 ****\n");
  x = compute_factorization(fact, full_mat, elim_test);
  if (x >= 0) {
    check_factorization(fact, full_mat);
  } else {
    printf("\n**** Singular matrix ****\n");
    goto end;
  }

  // one update
  i = 10;
  j = 0;
  extract_column(full_mat, i, buffer);
  printf("\n*** LU Update: %d replaces %d\n", i, j);
  factorization_solve_column(fact, buffer, 1);
  x = update_factorization(fact, j, i);
  if (x >= 0) {
    check_factorization(fact, full_mat);
  } else {
    printf("\n**** Singular matrix ****\n");
    goto end;
  }

  i = 11;
  j = 3;
  extract_column(full_mat, i, buffer);
  printf("\n*** LU Update: %d replaces %d\n", i, j);
  factorization_solve_column(fact, buffer, 1);
  x = update_factorization(fact, j, i);
  if (x >= 0) {
    check_factorization(fact, full_mat);
  } else {
    printf("\n**** Singular matrix ****\n");
    goto end;
  }

  i = 12;
  j = 5;
  extract_column(full_mat, i, buffer);
  printf("\n*** LU Update: %d replaces %d\n", i, j);
  factorization_solve_column(fact, buffer, 1);
  x = update_factorization(fact, j, i);
  if (x >= 0) {
    check_factorization(fact, full_mat);
  } else {
    printf("\n**** Singular matrix ****\n");
    goto end;
  }

  i = 13;
  j = 1;
  extract_column(full_mat, i, buffer);
  printf("\n*** LU Update: %d replaces %d\n", i, j);
  factorization_solve_column(fact, buffer, 1);
  x = update_factorization(fact, j, i);
  if (x >= 0) {
    check_factorization(fact, full_mat);
  } else {
    printf("\n**** Singular matrix ****\n");
    goto end;
  }

  i = 14;
  j = 7;
  extract_column(full_mat, i, buffer);
  printf("\n*** LU Update: %d replaces %d\n", i, j);
  factorization_solve_column(fact, buffer, 1);
  x = update_factorization(fact, j, i);
  if (x >= 0) {
    check_factorization(fact, full_mat);
  } else {
    printf("\n**** Singular matrix ****\n");
    goto end;
  }

  i = 15;
  j = 12;
  extract_column(full_mat, i, buffer);
  printf("\n*** LU Update: %d replaces %d\n", i, j);
  factorization_solve_column(fact, buffer, 1);
  x = update_factorization(fact, j, i);
  if (x >= 0) {
    check_factorization(fact, full_mat);
  } else {
    printf("\n**** Singular matrix ****\n");
    goto end;
  }

  printf("\n**** Factorization ****\n");
  print_factorization(fact);
  printf("\n\n");
  check_all_factorization(fact, full_mat);
  printf("\n\n**** All rows ****\n");
  gen_all_rows(fact, full_mat);


  printf("\n**** Double check ****\n");
  refactor(fact, full_mat);
  printf("\n**** Factorization ****\n");
  print_factorization(fact);
  printf("\n\n");
  check_all_factorization(fact, full_mat);
  printf("\n\n**** All rows ****\n");
  gen_all_rows(fact, full_mat);

 end:
  delete_buffer(buffer);
  delete_gauss_matrix(m1);
  delete_compact_matrix(full_mat);
  delete_factorization(fact);
}



int main() {
  init_rationals();
  build_vector = new_vector(0);

  basic_test();

  cleanup_and_delete_vector(build_vector);
  cleanup_rationals();

  return 0;
}
