#include <stdlib.h>
#include <stdio.h>


#include "rationals.h"
#include "vectors.h"
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


#include "spider.h"
#include "abz5.h"
#include "f9-20.h"


/*
 * Global variables:
 * - bank, vector v.
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



#if 0
/*
 * Build a matrix from column data.
 */
static void build_from_columns(matrix_t *m, int d[][3], int n) {
  int i, t, r_idx, den, num;
  mpq_ptr q;

  t = 0;
  for (i=0; i<n; i++) {
    empty_vector(build_vector, &bank);
    r_idx = d[t][0];
    while (r_idx >= 0) {
      num = d[t][1];
      den = d[t][2];    
      if (den == 1) {
	add_int_elem_to_vector(&build_vector, r_idx, num);
      } else {
	q = get_mpq(&bank);
	mpq_set_si(q, num, den);
	mpq_canonicalize(q);
	add_mpq_elem_to_vector(&build_vector, r_idx, q);
      }
      t ++;
      r_idx = d[t][0];
    }
    add_column(m, build_vector);
    t ++;
  }
}



/*
 * Build a matrix from column data.
 */
static void set_from_columns(matrix_t *m, int d[][3], int n) {
  int i, t, r_idx, den, num;
  mpq_ptr q;

  t = 0;
  for (i=0; i<n; i++) {
    empty_vector(build_vector, &bank);
    r_idx = d[t][0];
    while (r_idx >= 0) {
      num = d[t][1];
      den = d[t][2];    
      if (den == 1) {
	add_int_elem_to_vector(&build_vector, r_idx, num);
      } else {
	q = get_mpq(&bank);
	mpq_set_si(q, num, den);
	mpq_canonicalize(q);
	add_mpq_elem_to_vector(&build_vector, r_idx, q);
      }
      t ++;
      r_idx = d[t][0];
    }
    set_column(m, i, build_vector);
    t ++;
  }
}

static int elim_test[16] = {
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
};

#endif


static void basic_test() {
  gauss_matrix_t *m1;
  compact_matrix_t *full_mat;
  factorization_t *fact;

  printf("\n\nROW TEST\n");
  m1 = new_gauss_matrix(0, 0);
  build_from_rows(&m1->m, row_test, 11);
  printf("\n **** Original matrix ****\n");
  print_matrix_poly(stdout, &m1->m);
  printf("\n");
  fflush(stdout);

  printf("\nTRIANGULATION\n\n");
  gauss_elim_prepare(m1);
  eliminate_all_columns(m1);
  printf("\n**** After triangulation ****\n");
  print_matrix_details(stdout, &m1->m);
  printf("\n**** Triangular submatrix ****\n");
  print_elim_rows(stdout, m1);
  printf("\n Column list:\n\t");
  print_elim_columns(stdout, m1);
  printf("\n");
  printf("\n Column order:\n");
  print_column_positions(stdout, m1);
  fflush(stdout);

  full_mat = construct_triangular_matrix(m1);
  printf("\n**** Extracted full matrix ****\n");
  print_compact_matrix(stdout, full_mat);
  printf("\n\n");
  fflush(stdout);

  // check factorization
  fact = create_factorization(full_mat);
  printf("\n**** Factorization ****\n");
  printf("\nMatrix L\n");
  print_triangular_matrix_poly(stdout, &fact->lmatrix);
  printf("\n");
  print_triangular_matrix(stdout, &fact->lmatrix);
  printf("\nMatrix U\n");
  print_triangular_matrix_poly(stdout, &fact->umatrix);
  printf("\n");
  print_triangular_matrix(stdout, &fact->umatrix);
  printf("\nETA FILE\n");
  print_eta_file(stdout, &fact->f);
  fflush(stdout);

  delete_gauss_matrix(m1);
  delete_compact_matrix(full_mat);
  delete_factorization(fact);
}


static void simplification_test(char *name, 
				int row_data[][3], int nrows,
				int elim[], int nelim) {

  gauss_matrix_t *m1;
  compact_matrix_t *elim_mat;
  compact_matrix_t *diag_mat;
  factorization_t *fact;


  printf("\n\n%s\n", name);
  m1 = new_gauss_matrix(0, 0);
  build_from_rows(&m1->m, row_data, nrows);
  printf("\n **** Original matrix ****\n");
  print_matrix_poly(stdout, &m1->m);
  fflush(stdout);

  printf("\nPARTIAL ELIMINATION\n");
  gauss_elim_prepare(m1);
  eliminate_columns(m1, elim, nelim);
  printf("\n**** After Elimination ****\n");
  print_matrix_details(stdout, &m1->m);
  printf("\n**** Triangular submatrix ****\n");
  print_elim_rows(stdout, m1);
  printf("\n Column list:\n\t");
  print_elim_columns(stdout, m1);
  printf("\n");
  //  printf("\n Column order:\n");
  //  print_column_positions(stdout, m1);
  fflush(stdout);

  elim_mat = construct_triangular_row_matrix(m1);
  printf("\n**** Extracted row matrix ****\n");
  print_compact_matrix(stdout, elim_mat);
  printf("\n\n");
  fflush(stdout);
 

  printf("\nTRIANGULATION\n");
  clear_eliminated_rows(m1);
  eliminate_all_columns(m1);
  printf("\n**** After Triangulation ****\n");
  print_matrix_details(stdout, &m1->m);
  printf("\n**** Triangular submatrix ****\n");
  print_elim_rows(stdout, m1);
  printf("\n Column list:\n\t");
  print_elim_columns(stdout, m1);
  printf("\n");
  //  printf("\n Column order:\n");
  //  print_column_positions(stdout, m1);
  fflush(stdout);
  
  diag_mat = construct_triangular_matrix(m1);
  printf("\n**** Extracted full matrix ****\n");
  print_compact_matrix(stdout, diag_mat);
  printf("\n\n");
  fflush(stdout);
 
  // check factorization
  fact = create_factorization(diag_mat);
  printf("\n**** Factorization ****\n");
  printf("\nMatrix L\n");
  print_triangular_matrix_poly(stdout, &fact->lmatrix);
  printf("\n");
  print_triangular_matrix(stdout, &fact->lmatrix);
  printf("\nMatrix U\n");
  print_triangular_matrix_poly(stdout, &fact->umatrix);
  printf("\n");
  print_triangular_matrix(stdout, &fact->umatrix);
  printf("\nETA FILE\n");
  print_eta_file(stdout, &fact->f);
  fflush(stdout);


  delete_compact_matrix(diag_mat);
  delete_compact_matrix(elim_mat);
  delete_gauss_matrix(m1);
}


int main() {
  init_rationals();
  build_vector = new_vector(0);

  basic_test();

  simplification_test("SPIDER TEST", spider_test, SPIDER_NROWS, 
		      spider_elim, SPIDER_NONSLACK);

  simplification_test("ABZ5 TEST", abz_atoms, ABZ_NROWS, 
		      abz_elim, ABZ_NONSLACK);

  simplification_test("FISCHER TEST", fischer_test, NROWS, 
		      fischer_elim, 290);


  cleanup_and_delete_vector(build_vector);
  cleanup_rationals();

  return 0;
}
