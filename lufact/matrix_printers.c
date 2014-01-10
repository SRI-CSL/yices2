/*
 * Output functions for matrice-related 
 * data structures
 *
 * Created 2006/02/16.
 * Based on print functions in verctors.c and matrices.c
 */

#ifdef PRINT 

#include <stdio.h>

#include "matrix_types.h"
#include "rationals.h"
#include "lists.h"



/*
 * Print monomial r * var_idx: 
 * - the output is "r * <prefix><var_idx>" unless r is +1 or -1.
 *   (where prefix is typically "x" or "y")
 * - if r is +1, the output is "x<var_idx>"
 * - if r is -1, the output is "- x<var_idx>"
 * empty_flag indicates whether a + sign should be added 
 * - if empty_flag is non-zero, no sign is added if r = +1 or if r is positive.
 */
static void print_monomial(FILE *f, rat_t *r, int var_idx, int empty_flag, char *prefix) {
  int sgn;
  
  sgn = rat_sgn(r);
  if (sgn < 0) { 
    rat_neg(r);
    if (empty_flag) {
      fprintf(f, "- ");
    } else {
      fprintf(f, " - ");
    }
  } else if (! empty_flag) {
    fprintf(f, " + ");
  }

  if (rat_is_one(r)) {
    fprintf(f, "%s%d", prefix, var_idx);
  } else {
    rat_print(f, r);
    fprintf(f, " * %s%d", prefix, var_idx);
  }

  if (sgn < 0) {
    rat_neg(r);
  }
}



/***************
 *   VECTORS   *
 **************/

/*
 * Print v as a column vector.
 * Each non-element is printed as "name[index] = value"
 */
void print_vectelem(FILE *f, vector_elem_t *v, int n, char *name) {
  int i, idx;

  for (i=0; i<n; i++) {
    idx = v[i].idx;
    fprintf(f, " %s[%d] = ", name, idx);
    rat_print(f, &v[i].coeff);
    fprintf(f, "\n");
  }
}

/*
 * Print details of vector *v
 */
void print_vector(FILE *f, vector_t *v, char *name) {
  int i, n, k;

  fprintf(f, "Vector %s (addr = %p)\n", name, v);
  if (v != NULL) {
    n = v->size;
    fprintf(f, "Capacity = %d\n", v->capacity);
    fprintf(f, "Size = %d\n", n);
    fprintf(f, "Elements\n");
    for (i=0; i<n; i++) {
      k = v->data[i].idx;
      fprintf(f, "  %s[%d] = ", name, k);
      rat_print(f, &v->data[i].coeff);
      fprintf(f, "\n");
    }
  }
  fprintf(f, "---\n");
}


/* 
 * Print buffer as a vector
 */
void print_buffer(FILE *f, buffer_t *buffer, char *name) {
  int i, n, idx;

  n = buffer->nelems;
  for (i=0; i<n; i++) {
    idx = buffer->active[i];
    fprintf(f, "%s[%d] = ", name, idx);
    rat_print(f, buffer->q + idx);
    fprintf(f, "\n");
  }
}


/*************
 *   LISTS   *
 ************/

/*
 * Print a list of integers (row/column indices)
 */
void print_list(FILE *f, list_t *list) {
  list_elem_t *d;
  int i;

  d = list->data;
  i = d[list->list_id].next;
  while (i >= 0) {
    fprintf(f, " %d", i);
    i = d[i].next;
  }
}


/*
 * Print a list in reverse order
 */
void print_reverse_list(FILE *f, list_t *list) {
  list_elem_t *d;
  int i;

  d = list->data;
  i = d[list->list_id].pre;
  while (i >= 0) {
    fprintf(f, " %d", i);
    i = d[i].pre;
  }
}




/**************
 *  MATRICES  *
 *************/

static void print_row_vector(FILE *f, matrix_t *m, int j) {
  int i, n, k;
  mat_vector_t *r;

  r = m->row + j;
  n = r->size;

  fprintf(f, "Row %d: %d elements\n", j, r->nelems);
  fprintf(f, "size = %d, capacity = %d\n", n, r->capacity);

  fprintf(f, "free list: ");
  k = r->free;
  while (k >= 0) {
    fprintf(f, " %d", k);
    k = r->data[k].ptr;
  }

  fprintf(f, "\ndata\n");
  for (i=0; i<n; i++) {
    k = r->data[i].idx;
    if (k >= 0) {
      fprintf(f, "elem[%d] = <%d, %d, ", i, k, r->data[i].ptr);
      rat_print(f, &r->data[i].coeff);
      fprintf(f, "> \n");
    }
  }
  fprintf(f, "---\n");
}



static void print_column_vector(FILE *f, matrix_t *m, int j) {
  int i, n, k;
  mat_vector_t *v;

  v = m->column + j;
  n = v->size;

  fprintf(f, "Column %d: %d elements\n", j, v->nelems);
  fprintf(f, "size = %d, capacity = %d\n", n, v->capacity);

  fprintf(f, "free list:");
  k = v->free;
  while (k >= 0) {
    fprintf(f, " %d", k);
    k = v->data[k].ptr;
  }

  fprintf(f, "\ndata\n");
  for (i=0; i<n; i++) {
    k = v->data[i].idx;
    if (k >= 0) {
      fprintf(f, "elem[%d] = <%d, %d, ", i, k, v->data[i].ptr);
      rat_print(f, &v->data[i].coeff);
      fprintf(f, "> \n");
    }
  }
  fprintf(f, "---\n");
}


void print_matrix_details(FILE *f, matrix_t *m) {
  int i, n;

  fprintf(f, "MATRIX %p\n", m);
  fprintf(f, "nrows = %d\n", m->nrows);
  fprintf(f, "ncolumns = %d\n", m->ncolumns);
  fprintf(f, "row cap = %d\n", m->row_cap);
  fprintf(f, "column cap = %d\n", m->column_cap);
  fprintf(f, "-------------\n");

  n = m->nrows;
  for (i=0; i<n; i++) {
    print_row_vector(f, m, i);
  }
  fprintf(f, "\n");

  n = m->ncolumns;
  for (i=0; i<n; i++) {
    print_column_vector(f, m, i);
  }
  fprintf(f, "\n");
}


void print_matrix(FILE *f, matrix_t *m) {
  int i, j, n, p, idx;
  mat_vector_t *row;
  mat_vector_t *col;

  fprintf(f, "----- ROWS -----\n");
  n = m->nrows;  
  for (i=0; i<n; i++) {
    fprintf(f, "%4d:", i);
    row = m->row + i;
    p = row->size;
    for (j=0; j<p; j++) {
      idx = row->data[j].idx;
      if (idx >= 0) {
	fprintf(f, " %d:[%d, %d, ", j, idx, row->data[j].ptr);
	rat_print(f, &row->data[j].coeff);
	fprintf(f, "]");
      }
    }
    fprintf(f, "\n");
  }

  fprintf(f, "\n--- COLUMNS ----\n");
  n = m->ncolumns;
  for (i=0; i<n; i++) {
    fprintf(f, "%4d:", i);
    col = m->column + i;
    p = col->size;
    for (j=0; j<p; j++) {
      idx = col->data[j].idx;
      if (idx >= 0) {
	fprintf(f, " %d:[%d, %d, ", j, idx, col->data[j].ptr);
	rat_print(f, &col->data[j].coeff);
	fprintf(f, "]");
      }
    }
    fprintf(f, "\n");
  }
}


void print_matrix_rows(FILE *f, matrix_t *m) {
  int i, j, p, n, idx;
  mat_vector_t *row;

  n = m->nrows;
  for (i=0; i<n; i++) {
    fprintf(f, "%4d:", i);
    row = m->row + i;
    p = row->size;
    for (j=0; j<p; j++) {
      idx = row->data[j].idx;
      if (idx >= 0) {
	fprintf(f, " [%d, ", idx);
	rat_print(f, &row->data[j].coeff);
	fprintf(f, "]");
      }
      fprintf(f, "\n");
    }
    fprintf(f, "\n");
  }
}


static void print_row_poly(FILE *f, mat_vector_t *row) {
  int p, empty, j, idx;

  p = row->size;
  empty = 1;
  for (j=0; j<p; j++) {
    idx = row->data[j].idx;
    if (idx >= 0) {
      print_monomial(f, &row->data[j].coeff, idx, empty, "x");
      empty = 0;
    }
  }
}

static void print_column_poly(FILE *f, mat_vector_t *column) {
  int p, i, idx;

  p = column->size;
  for (i=0; i<p; i++) {
    idx = column->data[i].idx;
    if (idx >= 0) {
      fprintf(f, " %d[%d]", idx, column->data[i].ptr);
    }
  }
  fprintf(f, "\n");
}

void print_matrix_poly(FILE *f, matrix_t *m) {
  int i, n;

  n = m->nrows;
  for (i=0; i<n; i++) {
    fprintf(f, "%5d:  ", i);
    if (m->row[i].nelems == 0) {
      fprintf(f, "0");
    } else {
      print_row_poly(f, m->row + i);
    }

    fprintf(f, "\n");
  }
}


void print_matrix_columns_poly(FILE *f, matrix_t *m) {
  int i, n;

  n = m->nrows;
  for (i=0; i<n; i++) {
    fprintf(f, " x%-4d:  ", i);
    print_column_poly(f, m->column + i);
  }
}


static void print_row_list(FILE *f, matrix_t *m, list_t *list) {
  int r;

  r = first_of_list(list);
  while (r >= 0) {
    fprintf(f, "%4d:  ", r);
    if (m->row[r].nelems == 0) {
      fprintf(f, "0 *****\n");
    } else {
      print_row_poly(f, m->row + r);
      fprintf(f, "\n");
    }
    r = next_in_list(list, r);
  }
}

void print_elim_rows(FILE *f, gauss_matrix_t *m) {
  print_row_list(f, &m->m, &m->perm.row_list);
}


static void print_columns(FILE *f, list_t *list) {
  int c, k;

  c = first_of_list(list);
  k = 12;
  while (c >= 0) {
    fprintf(f, " x%-5d", c);
    c = next_in_list(list, c);
    k --;
    if (k == 0) {
      fprintf(f, "\n\t");
      k = 12;
    }
  }
  fprintf(f, "\n");
}

void print_elim_columns(FILE *f, gauss_matrix_t *m) {
  print_columns(f, &m->perm.col_list);
}


void print_column_positions(FILE *f, gauss_matrix_t *m) {
  int c;

  for (c=0; c < m->m.ncolumns; c++) {
    fprintf(f, "   x%d: %d\n", c, m->perm.col_order[c]);
  }
}


void print_row_positions(FILE *f, gauss_matrix_t *m) {
  int r;

  for (r=0; r < m->m.nrows; r++) {
    fprintf(f, " %5d: %d\n", r, m->perm.row_order[r]);
  }
}



/*********************************************
 * FOR TESTING ONLY: PRINT EQUATION U x = a  *
 ********************************************/


/*
 * Write equation m x = a 
 */
void print_equation(FILE *f, matrix_t *m, buffer_t *a) {
  int i, n;

  n = m->nrows;
  for (i=0; i<n; i++) {
    fprintf(f, "%5d:  ", i);
    if (m->row[i].nelems == 0) {
      fprintf(f, "0");
    } else {
      print_row_poly(f, m->row + i);
    }

    if (i < a->dim && a->tag[i] == ACTIVE_COEFF) {
      fprintf(f, "  =  ");
      rat_print(f, a->q + i);
      fprintf(f, "\n");
    } else {
      fprintf(f, "  =  0\n");
    }
  }
}


/* 
 * Print buffer as a "solution" to an equation
 */
void print_solution(FILE *f, buffer_t *buffer) {
  int i, n, idx;

  n = buffer->nelems;
  for (i=0; i<n; i++) {
    idx = buffer->active[i];
    fprintf(f, "x%d = ", idx);
    rat_print(f, buffer->q + idx);
    fprintf(f, "\n");
  }
}


/*
 * Print equation y m = b
 */
void print_colequation(FILE *f, matrix_t *m, buffer_t *b) {
  int i, n;

  n = m->ncolumns;
  for (i=0; i<n; i++) {
    fprintf(f, "%5d:  ", i);
    if (m->column[i].nelems == 0) {
      fprintf(f, "0");
    } else {
      print_row_poly(f, m->column + i);
    }

    if (i < b->dim && b->tag[i] == ACTIVE_COEFF) {
      fprintf(f, "  =  ");
      rat_print(f, b->q + i);
      fprintf(f, "\n");
    } else {
      fprintf(f, "  =  0\n");
    }
  }
}

/************************
 *   COMPACT MATRICES   *
 ***********************/

static void print_compact_row_poly(FILE *f, vector_array_t *v, int i) {
  vector_elem_t *vector;
  int p, empty, k, idx;

  vector = v->vblock;
  p = v->vindex[i+1];
  empty = 1;
  for (k = v->vindex[i]; k<p; k++) {
    idx = vector[k].idx;
    print_monomial(f, &vector[k].coeff, idx, empty, "x");
    empty = 0;
  }
  fprintf(f, "\n");
}


static void print_compact_column_poly(FILE *f, vector_array_t *v, int i) {
  vector_elem_t *vector;
  int p, k, idx;

  vector = v->vblock;
  p = v->vindex[i+1];
  for (k = v->vindex[i]; k<p; k++) {
    idx = vector[k].idx;
    fprintf(f, "[%d, ", idx);
    rat_print(f, &vector[k].coeff);
    fprintf(f, "] ");
  }
  fprintf(f, "\n");
}

void print_compact_matrix(FILE *f, compact_matrix_t *m) {
  int i, n, k;
  vector_array_t *v;


  fprintf(f, "COMPACT MATRIX %p\n", m);
  fprintf(f, "nrows = %d\n", m->nrows);
  fprintf(f, "ncolumns = %d\n", m->ncolumns);
  fprintf(f, "diag_size = %d\n", m->diag_size);
  fprintf(f, "vsize = %d\n\n", m->vsize);

  n = m->nrows;
  v = &m->rows;
  for (i=0; i<n; i++) {
    fprintf(f, "%5d:  ", i);
    print_compact_row_poly(f, v, i);
  }

  n = m->diag_size;
  fprintf(f, "\nColumn order:\n\t");
  k = 12;
  for (i = 0; i<n; i++) {
    fprintf(f, " x%-5d", m->col_list[i]);
    k --;
    if (k == 0) {
      fprintf(f, "\n\t");
      k = 12;
    }
  }

  n = m->ncolumns;

  //  fprintf(f, "\n\nColumn status:\n");
  //  for (i = 0; i<n; i++) {
  //    if (m->col_status[i] < 0) {
  //      fprintf(f, "  x%-5d: free variable\n", i);
  //    } else {
  //      fprintf(f, "  x%-5d: diagonal variable in row %d\n", i, m->col_status[i]);
  //    }
  //  }

  v = &m->columns;
  if (v->vindex != NULL) {
    fprintf(f, "\n\n---- Columns ----\n");
    for (i=0; i<n; i++) {
      fprintf(f, "  x%-5d:  ", i);
      print_compact_column_poly(f, v, i);
    }
  } else {
    fprintf(f, "\n\nNo column data\n");
  }
}



/**************************
 *  TRIANGULAR MATRICES   *
 *************************/

void print_triangular_matrix(FILE *f, triangular_matrix_t *m) {
  int i, n, c, p;

  fprintf(f, "TRIANGULAR MATRIX %p\n", m);
  fprintf(f, "nrows = %d\n", m->m.nrows);
  fprintf(f, "ncolumns = %d\n\n", m->m.ncolumns);

  print_matrix(f, &m->m);

  fprintf(f, "\n--- Diagonal ---\n");
  n = m->m.nrows;
  for (i=0; i<n; i++) {
    c = m->diag_column[i];
    p = m->row_dptr[i];
    fprintf(f, " m[%d,%d] = ", i, c);
    rat_print(f, &m->m.row[i].data[p].coeff);
    fprintf(f, "\n");
  }
  fprintf(f, "\n");
}


void print_triangular_matrix_poly(FILE *f, triangular_matrix_t *m) {
  int i, n, c, p;

  fprintf(f, "TRIANGULAR MATRIX %p\n", m);
  fprintf(f, "nrows = %d\n", m->m.nrows);
  fprintf(f, "ncolumns = %d\n\n", m->m.ncolumns);

  print_matrix_poly(f, &m->m);

  fprintf(f, "\n--- Diagonal ---\n");
  n = m->m.nrows;
  for (i=0; i<n; i++) {
    c = m->diag_column[i];
    p = m->row_dptr[i];
    fprintf(f, " m[%d,%d] = ", i, c);
    rat_print(f, &m->m.row[i].data[p].coeff);
    fprintf(f, "\n");
  }
  fprintf(f, "\n");
}


/****************
 *  ETA FILES   *
 ***************/

/*
 * Eta file f
 */
void print_eta_file(FILE *f, eta_file_t *e) {
  vector_elem_t *v;
  int i, n;
  int *vindex;

  fprintf(f, "ETA FILE %p\n", e);
  fprintf(f, "vector capacity: %d\n", e->vector_capacity);
  fprintf(f, "vblock capacity: %d\n", e->vblock_capacity);
  fprintf(f, "number of eta-lists: %d\n", e->nvectors);
  fprintf(f, "number of elements: %d\n", e->ncoeffs);

  n = e->nvectors;
  vindex = e->vindex;
  for (i=0; i<n; i++) {
    fprintf(f, "eta[%d]: idx = %d\n", i, e->row_index[i]);
    v = e->vblock + vindex[i];
    print_vectelem(f, v, vindex[i+1] - vindex[i], "e");
    fprintf(f, "--\n");
  }

  fprintf(f, "\n");
}


#if 0

/*
 * basis b
 */
void print_basis(FILE *f, basis_t *b) {
  int i, n;
  list_t *list;

  fprintf(f, "BASIS %p\n\n", b);
  print_eta_file(f, b->lfile);

  fprintf(f, "U MATRIX\n\n");
  print_matrix_rows(f, b->umatrix);

  fprintf(f, "\nCOLUMN ORDER:\n");
  list = &b->umatrix->triangle_columns;
  i = first_of_list(list);
  while (i >= 0) {
    fprintf(f, " %5d", i);
    i = next_in_list(list, i);
  }
  fprintf(f, "\n");

  fprintf(f, "\nROW ORDER:\n");
  list = &b->umatrix->triangle_rows;
  i = first_of_list(list);
  while (i >= 0) {
    fprintf(f, " %5d", i);
    i = next_in_list(list, i);
  }
  fprintf(f, "\n");


  fprintf(f, "\nMAPPING\n");
  n = b->nvars;
  for (i=0; i<n; i++) {
    if (b->var_col[i] >= 0) {
      fprintf(f, "   x%-5d --> basic in column %d\n", i, b->var_col[i]);
    } else {
      fprintf(f, "   x%-5d --> non basic\n", i);
    }
  }

  fprintf(f, "\nEND BASIS\n\n");
}

#endif

#endif
