/*
 * SPARSE MATRICES: 
 * 1) CONSTRUCTION AND BASIC OPERATIONS.
 * 2) GAUSSIAN ELIMINATION/LU FACTORIZATION OPERATIONS
 */

#include <limits.h>
#include <assert.h>

#include "memalloc.h"
#include "matrix_types.h"
#include "rationals.h"
#include "buffers.h"
#include "vectors.h"


// #define DEBUG 1

#ifdef DEBUG
#define PRINT 1
#include <stdio.h>
#include "matrix_printers.h"

FILE *out = stdout;

#endif



#ifndef TRUE
#define TRUE 1
#endif

#ifndef FALSE
#define FALSE 0
#endif



/**************************** 
 *  ROW AND COLUMN VECTORS  *
 ***************************/

/*
 * Initialize a row or column vector.
 * \param n = initial capacity (n must be >= 0).
 */
static inline void init_mat_vector(mat_vector_t *v, int n) {
  v->capacity = n;
  v->size = 0;
  v->nelems = 0;
  v->free = -1;
  v->data = (mat_elem_t *) safe_malloc(n * sizeof(mat_elem_t));
}

/*
 * Delete a row or column vector
 */
static inline void delete_mat_vector(mat_vector_t *v) {
  safe_free(v->data);
}


/*
 * Adjust the capacity of row or column vector v to have room
 * for at least n elements
 * - keep all elements already in v. 
 * - No effect if v->capacity is already at least n.
 */
static inline void adjust_mat_vector_capacity(mat_vector_t *v, int n) {
  if (v->capacity < n) {
    v->data = (mat_elem_t *) safe_realloc(v->data, n * sizeof(mat_elem_t));
    v->capacity = n;
  }
}


/*
 * Allocate a row element in a row vector v
 * - return the index of this element in v->data
 * - expand v if it's full
 */
static int alloc_mat_elem(mat_vector_t *v) {
  int n, new_cap;

  n = v->free;
  if (n >= 0) {
    v->free = v->data[n].ptr;
  } else {
    n = v->size;
    v->size = n + 1;
    if (n == v->capacity) {
      new_cap = n + (n >> 1) + 1;
      v->data = (mat_elem_t *) safe_realloc(v->data, new_cap * sizeof(mat_elem_t));
      v->capacity = new_cap;
    }
  }
  v->nelems ++;

  return n;
}



/*
 * Free  element of index ptr in v
 */
static inline void free_mat_elem(mat_vector_t *v, int ptr) {
  v->data[ptr].idx = -1;
  v->data[ptr].ptr = v->free;
  v->free = ptr;
  v->nelems --;
}




/*
 * Return pointer to element of given index in v->data
 * or -1 if idx does not occur in v
 */
static int get_mat_vector_ptr(mat_vector_t *v, int idx) {
  int i, n;

  n = v->size;
  for (i=0; i<n; i++) {
    if (v->data[i].idx == idx) {
      return i;
    }
  }

  return -1;
}




/***********************
 *  MATRIX ALLOCATION  *
 **********************/

/*
 * Initialize m for nrows and ncolumns.
 * All rows and columns are empty.
 * Row and column capacities are set to nrows and ncolumns.
 */
static void init_matrix(matrix_t *m, int nrows, int ncolumns) {
  int i;
  mat_vector_t *v;

  m->row_cap = nrows;
  m->column_cap = ncolumns;
  m->nrows = nrows;
  m->ncolumns = ncolumns;

  v = (mat_vector_t *) safe_malloc(nrows * sizeof(mat_vector_t));
  for (i=0; i<nrows; i++) {
    init_mat_vector(v + i, DEFAULT_ROW_VECTOR_SIZE);
  }
  m->row = v;

  v = (mat_vector_t *) safe_malloc(ncolumns * sizeof(mat_vector_t));
  for (i=0; i<ncolumns; i++) {
    init_mat_vector(v + i, DEFAULT_COLUMN_VECTOR_SIZE);
  }

  m->column = v;
}


/*
 * Create a new matrix with nrows and ncolumns.
 * The row and column capacities are also set to nrows/ncolumns.
 */
matrix_t *new_matrix(int nrows, int ncolumns) {
  matrix_t *tmp;

  tmp = (matrix_t *) safe_malloc(sizeof(matrix_t));
  init_matrix(tmp, nrows, ncolumns);

  return tmp;
}


/*
 * Increase the capacity of the row array.
 * \param n = minimal capacity requested.
 * - the new capacity is max(n, old-cap * 1.5).
 * - nrows is not changed.
 */
void expand_row_capacity(matrix_t *m, int n) {
  int new_cap;

  new_cap = m->row_cap;
  new_cap += (new_cap >> 1) + 1;
  if (new_cap < n) {
    new_cap = n;
  }

  m->row = (mat_vector_t *) safe_realloc(m->row, new_cap * sizeof(mat_vector_t));
  m->row_cap = new_cap;
}



/*
 * Increase the capacity of the column-descriptor array.
 * \param n = minimal capacity requested.
 * - the new capacity is max(n, old-cap * 1.5).
 * - ncolumns is not changed.
 */
void expand_column_capacity(matrix_t *m, int n) {
  int new_cap;

  new_cap = m->column_cap;
  new_cap += (new_cap >> 1) + 1;
  if (new_cap < n) {
    new_cap = n;
  }

  m->column = 
    (mat_vector_t *) safe_realloc(m->column, new_cap * sizeof(mat_vector_t));
  m->column_cap = new_cap;
}



/*
 * Make room in the row descriptor array for at least n rows.
 * - if n is no more than m->nrows, nothing is done.
 * - otherwise, sufficient space is allocated for n rows and 
 *   the new rows are initialized.
 */
void adjust_nrows(matrix_t *m, int n) {
  int i, new_cap;
  mat_vector_t *row_d;

  if (m->nrows < n) {
    row_d = m->row;
    new_cap = m->row_cap;
    if (new_cap < n) {
      new_cap += (new_cap >> 1) + 1;
      if (new_cap < n) {
	new_cap = n;
      }
      row_d =
	(mat_vector_t *) safe_realloc(row_d, new_cap * sizeof(mat_vector_t));
      m->row = row_d;
      m->row_cap = new_cap;
    }

    for (i=m->nrows; i<n; i++) {
      init_mat_vector(row_d + i, DEFAULT_ROW_VECTOR_SIZE);
    }
    m->nrows = n;
  }
}


/*
 * Make room in the column descriptor array for at least n columns.
 * - if n is no more than m->ncolumns, nothing is done.
 * - otherwise, sufficient space is allocated for n columns and 
 *   the descriptors of all the new columns are initialized.
 */
void adjust_ncolumns(matrix_t *m, int n) {
  int i, new_cap;
  mat_vector_t *col_d;

  if (m->ncolumns < n) {
    col_d = m->column;
    new_cap = m->column_cap;
    if (new_cap < n) {
      new_cap += (new_cap >> 1) + 1;
      if (new_cap < n) {
	new_cap = n;
      }
      col_d = (mat_vector_t *) safe_realloc(col_d, new_cap * sizeof(mat_vector_t));
      m->column = col_d;
      m->column_cap = new_cap;
    }

    for (i=m->ncolumns; i<n; i++) {
      init_mat_vector(col_d + i, DEFAULT_COLUMN_VECTOR_SIZE);
    }
    m->ncolumns = n;
  }
}


/*
 * Remove the empty elements from row r_idx and update the columns.
 * - requires 0 <= r_idx <= m->nrows - 1 (row of that index exists).
 */
void compact_row(matrix_t *m, int r_idx) {
  mat_vector_t *row;
  int i, j, c, p, n;

  row = m->row + r_idx;
  if (row->free < 0) return;

  n = row->size;
  j = 0;
  for (i=0; i<n; i++) {
    c = row->data[i].idx;
    if (c >= 0) {
      p = row->data[i].ptr;
      row->data[j] = row->data[i];
      m->column[c].data[p].ptr = j;
      j ++;
    }
  }
  row->size = j;
  row->free = -1;
}



/*
 * Remove the empty elements from column c_idx and update the row ptrs.
 * - requires 0 <= c_idx <= m->ncolumns - 1.
 */
void compact_column(matrix_t *m, int c_idx) {
  mat_vector_t *column;
  int i, j, r, p, n;

  column = m->column + c_idx;
  if (column->free < 0) return;

  n = column->size;
  j = 0;
  for (i=0; i<n; i++) {
    r = column->data[i].idx;
    if (r >= 0) {
      p = column->data[i].ptr;
      column->data[j] = column->data[i];
      m->row[r].data[p].ptr = j;
      j ++;
    }
  }
  column->size = j;
  column->free = -1;
}



/*
 * Free internal arrays in m
 */
static void cleanup_matrix(matrix_t *m) {
  int i, n;

  n = m->nrows;
  for (i=0; i<n; i++) {
    delete_mat_vector(m->row + i);
  }
  safe_free(m->row);

  n = m->ncolumns;
  for (i=0; i<n; i++) {
    delete_mat_vector(m->column + i);
  }
  safe_free(m->column);  
}


/*
 * Delete matrix m
 */
void delete_matrix(matrix_t *m) {
  cleanup_matrix(m);
  safe_free(m);
}






/**********************************
 *  ADDITION OF ROWS AND COLUMNS  *
 *********************************/

/*
 * Clear row r_idx: remove all its elements and update
 * the column dependencies. Also free all mpq elements 
 * from the row.
 * - Preconditions: 0 <= r_idx <= m->nrows - 1
 *                  row = m->row + r_idx
 * - result: row r_idx is empty:
 *     m->row[r_idx].free = -1, 
 *     m->row[r_idx].size = 0,
 *     m->row[r_idx].nelems = 0.
 */
static void clear_row(matrix_t *m, int r_idx, mat_vector_t *row) {
  int i, n, c, p;

  n = row->size;
  for (i=0; i<n; i++) {
    c = row->data[i].idx;
    if (c >= 0) {
      // release coefficient
      rat_clear(&row->data[i].coeff);
      // delete the column dependency
      p = row->data[i].ptr;
      free_mat_elem(m->column + c, p);
    }
  }

  row->size = 0;
  row->free = -1;
  row->nelems = 0;
}


/*
 * Clear column c_idx: remove all its elements.
 * Also free all mpq elements in the column.
 * - Preconditions: 0 <= c_idx <= m->ncolumns - 1
 *                  col = m->column + c_idx
 */
static void clear_column(matrix_t *m, int c_idx, mat_vector_t *col) {
  int i, n, r, p;

  n = col->size;
  for (i=0; i<n; i++) {
    r = col->data[i].idx;
    if (r >= 0) {
      // release coeff
      rat_clear(&col->data[i].coeff);
      // remove the row element
      p = col->data[i].ptr;
      free_mat_elem(m->row + r, p);
    }
  }

  col->size = 0;
  col->free = -1;
  col->nelems = 0;
}




/*
 * Auxiliary function: copy vector v into a row of index r_idx.
 * Add a column dependency for each element.
 * - v is an array of vector_elem_t
 * - n = number of elements in v
 * 
 * Precondition:
 * - v does not contain duplicate indices
 * - there's enough room in row and row is empty.
 * - there's a column for every index of v
 * - row = m->row + r_idx
 */
static void copy_vectelem_in_row(matrix_t *m, vector_elem_t *v, int n,
				 int r_idx, mat_vector_t *row) {
  int i, c, p;
  mat_elem_t *re;
  mat_vector_t *column;

  row->size = n;
  row->nelems = n;
  re = row->data;
  for (i=0; i<n; i++) {
    // copy index and coefficient
    c = v[i].idx;
    re[i].idx = c;
    rat_set(&re[i].coeff, &v[i].coeff);
    // set column dependency
    column = m->column + c;
    p = alloc_mat_elem(column);
    column->data[p].idx = r_idx;
    column->data[p].ptr = i;
    column->data[p].coeff = re[i].coeff;
    // set ptr
    re[i].ptr = p;
  }
}


/*
 * Auxiliary function: copy vector v into a column of index c_idx.
 * Add the elements of v to their row vector, record the dependencies
 * in column.
 * - v is an array of n vector_elem_t objects
 * 
 * Precondition:
 * - v does not contain duplicate indices
 * - there's enough room in column and column is empty.
 * - there's a row for every index of v
 * - column = m->column + c_idx
 */
static void copy_vectelem_in_column(matrix_t *m, vector_elem_t *v, int n,
				    int c_idx, mat_vector_t *column) {
  int i, r, p;
  mat_elem_t *ce;
  mat_vector_t *row;

  column->size = n;
  column->nelems = n;
  ce = column->data;
  for (i=0; i<n; i++) {
    r = v[i].idx;
    // copy element
    ce[i].idx = r;
    rat_set(&ce[i].coeff, &v[i].coeff);
    // set row dependency
    row = m->row + r;
    p = alloc_mat_elem(row);
    row->data[p].idx = c_idx;
    row->data[p].ptr = i;
    row->data[p].coeff = ce[i].coeff;
    // set ptr
    ce[i].ptr = p;    
  }
}


/*
 * Auxiliary function: copy a buffer into a row of index r_idx.
 * 
 * Pcecondition:
 * - there's enough room in row: row->capacity >= buffer->nelems
 * - row is empty
 * - there's a column for every index in buffer->active
 * - row = m->row + r_idx
 */
static void copy_buffer_in_row(matrix_t *m, buffer_t *buffer,
			       int r_idx, mat_vector_t *row) {
  int i, n, c, p;
  mat_elem_t *re;
  mat_vector_t *column;

  n = buffer->nelems;
  row->size = n;
  row->nelems = n;
  re = row->data;
  for (i=0; i<n; i++) {
    c = buffer->active[i];
    // copy index and coefficient
    re[i].idx = c;
    rat_set(&re[i].coeff, buffer->q + c);
    // add column dependency
    column = m->column + c;
    p = alloc_mat_elem(column);
    column->data[p].idx = r_idx;
    column->data[p].ptr = i;
    column->data[p].coeff = re[i].coeff;
    // set c_ptr
    re[i].ptr = p;
  }
}



/*
 * Auxiliary function: copy a buffer into a column of index c_idx.
 * Add the elements of buffer to their row vector, record the dependencies
 * in column.
 * 
 * Precondition:
 * - there's enough room in column: column->capacity >= buffer->nelems
 * - column is empty.
 * - there's a row for every index of v
 * - column = m->column + c_idx
 */
static void copy_buffer_in_column(matrix_t *m, buffer_t *buffer,
				  int c_idx, mat_vector_t *column) {
  int i, n, r, p;
  mat_elem_t *ce;
  mat_vector_t *row;

  n = buffer->nelems;
  column->size = n;
  column->nelems = n;
  ce = column->data;
  for (i=0; i<n; i++) {
    r = buffer->active[i];
    // copy index and coefficient
    ce[i].idx = r;
    rat_set(&ce[i].coeff, buffer->q + r);
    // set row dependency
    row = m->row + r;
    p = alloc_mat_elem(row);
    row->data[p].idx = c_idx;
    row->data[p].ptr = i;
    row->data[p].coeff = ce[i].coeff;
    // set ptr
    ce[i].ptr = p;    
  }
}




/*
 * Auxiliary functions: set a new element in a given column to constant c
 * The element is added at the end of the column (using colum->size).
 * 
 * Precondition:
 * - column = m->column + c_idx
 * - there's enough room for the new element in column
 * - the row r_idx exists in m
 * - column does not already contain an element with index r_idx
 */
static void add_int_elem_in_column(matrix_t *m, int c_idx, int r_idx, int c,
				   mat_vector_t *column) {
  int n, p;
  mat_vector_t *row;

  // element is stored in colum->data[n] and row->data[p].
  n = column->size;
  row = m->row + r_idx;
  p = alloc_mat_elem(row);

  // copy in column
  column->data[n].idx = r_idx;
  column->data[n].ptr = p;
  rat_set_long(&column->data[n].coeff, c);
  
  // copy in row
  row->data[p].idx = c_idx;
  row->data[p].ptr = n;
  row->data[p].coeff = column->data[n].coeff;
  
  column->size = n + 1;
  column->nelems ++;
}


static void add_rat_elem_in_column(matrix_t *m, int c_idx, int r_idx, rat_t *c,
				   mat_vector_t *column) {
  int n, p;
  mat_vector_t *row;

  // element is stored in colum->data[n] and row->data[p].
  n = column->size;
  row = m->row + r_idx;
  p = alloc_mat_elem(row);

  // copy in column
  column->data[n].idx = r_idx;
  column->data[n].ptr = p;
  rat_set(&column->data[n].coeff, c);
  
  // copy in row
  row->data[p].idx = c_idx;
  row->data[p].ptr = n;
  row->data[p].coeff = column->data[n].coeff;
  
  column->size = n + 1;
  column->nelems ++;
}


/*
 * Add fraction num/den as last element in column
 *
 * Preconditions:
 * - column = m->column + c_idx
 * - there's enough room for the new element in column
 * - the row r_idx exists in m
 * - column does not already contain an element with index r_idx
 */
static void add_fraction_in_column(matrix_t *m, int c_idx, int r_idx, rat_t *num, 
				   rat_t *den, mat_vector_t *column) {

  int n, p;
  mat_vector_t *row;
  rat_t *aux;

  // element is stored in colum->data[n] and row->data[p].
  n = column->size;
  row = m->row + r_idx;
  p = alloc_mat_elem(row);

  // copy in column
  column->data[n].idx = r_idx;
  column->data[n].ptr = p;
  aux = &column->data[n].coeff;
  rat_set(aux, num);
  rat_div(aux, den);  
  
  // copy in row
  row->data[p].idx = c_idx;
  row->data[p].ptr = n;
  row->data[p].coeff = column->data[n].coeff;
  
  column->size = n + 1;
  column->nelems ++;  
}



/*
 * Get largest index of vector v
 * - v must be non NULL
 * - returns -1 if v is empty
 */
static int max_index_in_vectelem(vector_elem_t *v, int n) {
  int max, i, idx;

  max = -1;
  for (i=0; i<n; i++) {
    idx = v[i].idx;
    if (idx > max) {
      max = idx;
    }
  }

  return max;
}



/*
 * Largest active index of buffer
 */
static int max_index_in_buffer(buffer_t *buffer) {
  int max, i, n, idx;

  max = -1;
  n = buffer->nelems;

  for (i=0; i<n; i++) {
    idx = buffer->active[i];
    if (idx > max) {
      max = idx;
    }
  }

  return max;
}


/*
 * ROW ADDITION
 *
 * - create a new row and store it as the last row of the matrix. 
 * - adjust the arrays of rows and columns if necessary to make
 *   room for the new row.
 *
 * The new row is assigned row index = m->nrows, then m->nrows is
 * incremented. The array of columns is adjusted if necessary so that
 * there's a column for every index in v.
 */

/*
 * New row is given as an array v of n vector elements
 */
void add_vectelem_as_new_row(matrix_t *m, vector_elem_t *v, int n) {
  int r_idx, max_c;
  mat_vector_t *row;

  r_idx = m->nrows;
  if (r_idx == m->row_cap) {
    expand_row_capacity(m, DEFAULT_ROW_CAPACITY);
  }
  max_c = max_index_in_vectelem(v, n);
  adjust_ncolumns(m, max_c + 1);

  m->nrows = r_idx + 1;

  // initialize m->row[r_idx]; initial capacity = size of v
  row = m->row + r_idx;
  init_mat_vector(row, n);
  copy_vectelem_in_row(m, v, n, r_idx, row);
  
}


/*
 * New row is given as a vector_t structure
 */
void add_vector_as_new_row(matrix_t *m, vector_t *v) {
  add_vectelem_as_new_row(m, v->data, v->size);
}



/*
 * New row is given as a buffer
 */
void add_buffer_as_new_row(matrix_t *m, buffer_t *buffer) {
  int r_idx, max_c;
  mat_vector_t *row;

  r_idx = m->nrows;
  if (r_idx == m->row_cap) {
    expand_row_capacity(m, DEFAULT_ROW_CAPACITY);
  }
  max_c = max_index_in_buffer(buffer);
  adjust_ncolumns(m, max_c + 1);

  m->nrows = r_idx + 1;

  // initialize m->row[r_idx]; initial capacity = size of buffer
  row = m->row + r_idx;
  init_mat_vector(row, buffer->nelems);
  copy_buffer_in_row(m, buffer, r_idx, row);  
}



/*
 * COLUMN ADDITION
 *
 * Create a new column and add it as the last column of m
 * row and column arrays are adjusted to have enough room if 
 * necessary.
 */

/*
 * New column is given as an array of n vector_elem_t elements
 */
void add_vectelem_as_new_column(matrix_t *m, vector_elem_t *v, int n) {
  int c_idx, max_r;
  mat_vector_t *column;

  c_idx = m->ncolumns;
  if (c_idx == m->column_cap) {
    expand_column_capacity(m, DEFAULT_COL_CAPACITY);
  }

  max_r = max_index_in_vectelem(v, n);
  adjust_nrows(m, max_r + 1);

  m->ncolumns = c_idx + 1;

  column = m->column + c_idx;
  init_mat_vector(column, n);   // initialize m->column[c_idx]
  copy_vectelem_in_column(m, v, n, c_idx, column);
}


/*
 * Add a new column
 * \param v = vector of column elements
 * The new column is assigned index m->ncolumns.
 */
void add_vector_as_new_column(matrix_t *m, vector_t *v) {
  add_vectelem_as_new_column(m, v->data, v->size);
}


/*
 * New column is given as a buffer
 */
void add_buffer_as_new_column(matrix_t *m, buffer_t *buffer) {
  int c_idx, max_r;
  mat_vector_t *column;

  c_idx = m->ncolumns;
  if (c_idx == m->column_cap) {
    expand_column_capacity(m, DEFAULT_COL_CAPACITY);
  }

  max_r = max_index_in_buffer(buffer);
  adjust_nrows(m, max_r + 1);

  m->ncolumns = c_idx + 1;

  column = m->column + c_idx;
  init_mat_vector(column, buffer->nelems);   // initialize m->column[c_idx]
  copy_buffer_in_column(m, buffer, c_idx, column);
}




/*
 * COPY VECTORS INTO EXISTING ROWS OR COLUMNS
 */

/*
 * Set row of index r_idx equal to v.
 * - requires 0 <= r_idx <= m->nrows - 1 
 *   and all column indices in v must be between 0 and m->ncolumns - 1.
 * - the function returns -1 and does nothing if that's not satisfied.
 *   otherwise, it returns 0.
 */
int store_vectelem_in_row(matrix_t *m, int r_idx, vector_elem_t *v, int n) {
  mat_vector_t *row;

  if (r_idx >= m->nrows || max_index_in_vectelem(v, n) >= m->ncolumns) {
    return -1;
  }

  row = m->row + r_idx;
  clear_row(m, r_idx, row);
  adjust_mat_vector_capacity(row, n);
  copy_vectelem_in_row(m, v, n, r_idx, row);

  return 0;
}


/*
 * Same thing, with v given as a vector_t
 */
int store_vector_in_row(matrix_t *m, int r_idx, vector_t *v) {
  return store_vectelem_in_row(m, r_idx, v->data, v->size);
}


/*
 * Same thing with v given as a buffer
 */
int store_buffer_in_row(matrix_t *m, int r_idx, buffer_t *buffer) {
  mat_vector_t *row;

  if (r_idx >= m->nrows || max_index_in_buffer(buffer) >= m->ncolumns) {
    return -1;
  }

  row = m->row + r_idx;
  clear_row(m, r_idx, row);
  adjust_mat_vector_capacity(row, buffer->nelems);
  copy_buffer_in_row(m, buffer, r_idx, row);  

  return 0;
}



/*
 * Set column of index c_idx equal to v
 * - requires 0 <= c_idx <= m->ncolumns - 1
 *   and all indices in v must be between 0 and m->nrows - 1.
 * - returns -1 and does nothing if that's not true. (not really,
 *   does not check for c_idx < 0).
 * - returns 0 and sets the column otherwise.
 */
int store_vectelem_in_column(matrix_t *m, int c_idx, vector_elem_t *v, int n) {
  mat_vector_t *column;

  if (c_idx >= m->ncolumns || max_index_in_vectelem(v, n) >= m->nrows) {
    return -1;
  }

  column = m->column + c_idx;
  clear_column(m, c_idx, column);
  adjust_mat_vector_capacity(column, n);
  copy_vectelem_in_column(m, v, n, c_idx, column);

  return 0;
}


/*
 * Same thing, with v given as a vector_t
 */
int store_vector_in_column(matrix_t *m, int c_idx, vector_t *v) {
  return store_vectelem_in_column(m, c_idx, v->data, v->size);
}


/*
 * Same thing, with v given as a buffer
 */
int store_buffer_in_column(matrix_t *m, int c_idx, buffer_t *buffer) {
  mat_vector_t *column;

  if (c_idx >= m->ncolumns || max_index_in_buffer(buffer) >= m->nrows) {
    return -1;
  }

  column = m->column + c_idx;
  clear_column(m, c_idx, column);
  adjust_mat_vector_capacity(column, buffer->nelems);
  copy_buffer_in_column(m, buffer, c_idx, column);

  return 0;
}



/*
 * Less safe version: to be used only if it's known that nrows
 * and ncolumns are large enough
 */
#if 0

static void fast_store_vectelem_in_row(matrix_t *m, int r_idx, vector_elem_t *v, int n) {
  mat_vector_t *row;

  row = m->row + r_idx;
  clear_row(m, r_idx, row);
  adjust_mat_vector_capacity(row, n);
  copy_vectelem_in_row(m, v, n, r_idx, row);
}

#endif

static void fast_store_vectelem_in_column(matrix_t *m, int c_idx, vector_elem_t *v, int n) {
  mat_vector_t *column;

  column = m->column + c_idx;
  clear_column(m, c_idx, column);
  adjust_mat_vector_capacity(column, n);
  copy_vectelem_in_column(m, v, n, c_idx, column);
}




/*
 * Clear matrix m:
 * set all columns and rows to 0
 */
void clear_matrix(matrix_t *m) {
  int i, j, n, p;
  mat_vector_t *row;
  mat_vector_t *column;

  n = m->nrows;
  for (i=0; i<n; i++) {
    row = m->row + i;
    p = row->size;
    for (j=0; j<p; j++) {
      rat_clear(&row->data[j].coeff);
    }
    row->size = 0;
    row->free = -1;
    row->nelems = 0;
  }

  n = m->ncolumns;
  for (i=0; i<n; i++) {
    column = m->column + i;
    column->size = 0;
    column->free = -1;
    column->nelems = 0;
  }
}














/***********************************************
 *   LISTS AND PERMUTATIONS: INLINE FUNCTIONS  *
 **********************************************/

/*
 * Allocate a list-element array for as many as nl lists
 * of elements between 0 and n-1.
 * Room for nl headers is allocated in tmp[-nl] ... tmp[-1],
 * elements are stored in tmp[0] ... tmp[n-1].
 */
static inline list_elem_t *new_list_array(int n, int nl) {
  return (list_elem_t *) safe_malloc((n + nl) * sizeof(list_elem_t)) + nl;
}


/*
 * Resize a list-element array for n elements
 * nl = number of lists.
 */
static inline list_elem_t *resize_list_array(list_elem_t *p, int n, int nl) {
  return (list_elem_t *) safe_realloc(p - nl, (n + nl) * sizeof(list_elem_t)) + nl;
}


/*
 * Delete a list-elem array with nl lists or nl partitions.
 */
static inline void delete_list_array(list_elem_t *p, int nl) {
  if (p != NULL) {
    safe_free(p - nl);
  }
}


/*
 * Initialize a list of given id, in permutation array p
 * - must make sure id < 0 and there's room for that id in *p
 */
static inline void init_list(list_t *list, int id, list_elem_t *p) {  
  list->list_id = id;
  list->data = p;
  p[id].next = id;
  p[id].pre = id;
}


/*
 * Insert element i before element k
 */
static inline void list_insert_before(list_elem_t *p, int k, int i) {
  int pre_k;

  pre_k = p[k].pre;
  p[i].pre = pre_k;
  p[i].next = k;
  p[pre_k].next = i;
  p[k].pre = i;
}


/*
 * Insert element i after element k
 */
static inline void list_insert_after(list_elem_t *p, int k, int i) {
  int next_k;

  next_k = p[k].next;
  p[i].next = next_k;
  p[i].pre = k;
  p[k].next = i;
  p[next_k].pre = i;
}


/*
 * Remove element i from its current list
 */
static inline void list_remove(list_elem_t *p, int i) {
  int pre_i, next_i;

  pre_i = p[i].pre;
  next_i = p[i].next;
  p[pre_i].next = next_i;
  p[next_i].pre = pre_i;
}


/*
 * Add element i at the end of a list
 * - require list to be initialized first.
 * - i is an index in array list->data
 */
static inline void add_last_to_list(list_t *list, int i) {
  int k;
  list_elem_t *d;

  k = list->list_id;
  d = list->data;
  list_insert_before(d, k, i);
}


/*
 * Add element i at the beginning of a list
 * - require list to be initialized
 * - i is an index in array list->data
 */
static inline void add_first_to_list(list_t *list, int i) {
  int k;
  list_elem_t *d;

  k = list->list_id;
  d = list->data;
  list_insert_after(d, k, i);
}


/*
 * Remove element i from a list
 */
static inline void remove_from_list(list_t *list, int i) {
  list_remove(list->data, i);
}


/*
 * Circular shift:
 * - take sublist starting from i and ending by j
 * - apply a circular permutation to that sublist: move j before i
 */
static inline void circular_shift(list_t *list, int i, int j) {
  list_remove(list->data, j);
  list_insert_before(list->data, i, j);
}


/*
 * Circular shift in the reverse direction
 * - sublist starting from i and ending by j
 * - move i after j
 */
static inline void reverse_circular_shift(list_t *list, int i, int j) {
  list_remove(list->data, i);
  list_insert_after(list->data, j, i);
}


/*
 * Check whether list is empty
 */
static inline int is_list_empty(list_t *list) {
  return list->data[list->list_id].next < 0;
}

static inline int is_list_nonempty(list_t *list) {
  return list->data[list->list_id].next >= 0;
}


/*
 * Empty list
 */
static inline void clear_list(list_t *list) {
  int i;

  i = list->list_id;
  list->data[i].pre = i;
  list->data[i].next = i;
}


/*
 * Get the first/last element of list.
 * - returns a negative number if the list is empty
 */
static inline int first_of_list(list_t *list) {
  return list->data[list->list_id].next;
}

static inline int last_of_list(list_t *list) {
  return list->data[list->list_id].pre;
}


/*
 * Successor and predecessor of i in list
 * - next returns a negative number if i is the last element
 * - previous returns a negative number if i is the first element
 */
static inline int next_in_list(list_t *list, int i) {
  return list->data[i].next;
}

static inline int previous_in_list(list_t *list, int i) {
  return list->data[i].pre;
}



/*
 * Initialize a partition structure for n elements and p partitions.
 */
static void init_partition(partition_t *part, int n, int p) {
  int i;
  list_elem_t *perm;

  part->nelems = n;
  part->nparts = p;
  perm = new_list_array(n, p);
  part->data = perm;

  for (i = -p; i<0; i++) {
    perm[i].next = i;
    perm[i].pre = i;
  }
}


#if 0

/*
 * Resize partition for n elements
 */
static void resize_partition(partition_t *part, int n) {
  list_elem_t *perm;

  if (part->nelems < n) {
    perm = resize_list_array(part->data, n, part->nparts);
    part->nelems = n;
    part->data = perm;
  }
}

#endif


/*
 * Delete partition
 */
static void delete_partition(partition_t *part) {
  delete_list_array(part->data, part->nparts);
  part->data = NULL;
  part->nparts = 0;
  part->nelems = 0;
}


/*
 * Clear a partition: empty all the lists
 */
static void clear_partition(partition_t *part) {
  int i;
  list_elem_t *perm;

  perm = part->data;
  for (i = - part->nparts; i<0; i++) {
    perm[i].next = i;
    perm[i].pre = i;
  }
}


/*
 * Add element i to partition p (in last position).
 */
static void partition_add(partition_t *part, int i, int p) {
  list_insert_before(part->data, -p, i);
}

/*
 * Remove element i from its current list
 */
static void partition_remove(partition_t *part, int i) {
  list_remove(part->data, i);
}


/*
 * Move element i from its current list to list p
 */
static void partition_move(partition_t *part, int i, int p) {
  list_remove(part->data, i);
  list_insert_before(part->data, -p, i);
}


/*
 * Get first element of list p in a partition
 * - returns a negative number if that list is empty
 */
static inline int partition_get_first(partition_t *part, int p) {
  return part->data[-p].next;
}

/*
 * Get successor of i in partition:
 * - returns a negative number if i is the last element
 * in its list.
 */
static inline int partition_get_next(partition_t *part, int i) {
  return part->data[i].next;
}




/****************************
 *  ROW/COLUMN PERMUTATION  *
 ***************************/

/*
 * Initialize a permutation structure for nrows and ncolumns.
 * Allocate the internal arrays and set row list/column list to empty lists.
 */
static void init_permutation(permutation_t *perm, int nrows, int ncolumns) {
  list_elem_t *base;
  int i;

  // column list (empty)
  base = new_list_array(ncolumns, 1);
  perm->col_perm_base = base;
  init_list(&perm->col_list, -1, base);

  // row list (empty)
  base = new_list_array(nrows, 1);
  perm->row_perm_base = base;
  init_list(&perm->row_list, -1, base);

  perm->size = 0;

  // tags/positions: all -1 initially
  perm->col_order = (int *) safe_malloc(ncolumns * sizeof(int));
  for (i=0; i<ncolumns; i++) {
    perm->col_order[i] = -1;
  }

  perm->row_order = (int *) safe_malloc(nrows * sizeof(int));
  for (i=0; i<nrows; i++) {
    perm->row_order[i] = -1;
  }
}


/*
 * Cleanup: free the internal arrays.
 */
static void cleanup_permutation(permutation_t *perm) {
  delete_list_array(perm->col_perm_base, 1);
  delete_list_array(perm->row_perm_base, 1);
  safe_free(perm->col_order);
  safe_free(perm->row_order);
}



/*
 * Reset: empty the lists
 */
static void reset_permutation(permutation_t *perm, int nrows, int ncolumns) {
  int i;

  perm->size = 0;
  clear_list(&perm->col_list);
  clear_list(&perm->row_list);

  for (i=0; i<ncolumns; i++) {
    perm->col_order[i] = -1;
  }

  for (i=0; i<nrows; i++) {
    perm->row_order[i] = -1;
  }
}


/*
 * Store pair r_idx/c_idx in the partition:
 * - r_idx is stored at the end of row_list
 * - c_idx is stored at the end of col_list.
 */
static void permutation_add(permutation_t *perm, int r_idx, int c_idx) {
  int i;

  // r_idx/c_idx must not be already in the lists
  assert(perm->row_order[r_idx] < 0 && perm->col_order[c_idx] < 0);

  add_last_to_list(&perm->row_list, r_idx);
  add_last_to_list(&perm->col_list, c_idx);

  i = perm->size;
  perm->row_order[r_idx] = i;
  perm->col_order[c_idx] = i;
  perm->size = i + 1;
}








/*******************************
 *  PIVOT-SELECTION HEURISTIC  *
 ******************************/

#if DEBUG

static int empty_partition(partition_t *part, int p) {
  return part->data[-p].next < 0;
}

static void print_partition(partition_t *part, int p) {
  int i;
  list_elem_t *perm;

  perm = part->data;
  i = perm[-p].next;
  while (i >= 0) {
    printf(" %d", i);
    i = perm[i].next;
  }
  printf("\n");
}


static void print_pivoter(pivoter_t *piv, int nrows, int ncolumns) {
  int i;

  printf("\n\nRow partition\n");
  for (i=0; i<=PARTITION_SIZE; i++) {
    if (! empty_partition(&piv->row_partition, i + 1)) {
      printf("Size %d: ", i);
      print_partition(&piv->row_partition, i + 1);
    }
  }

  printf("Row counts:");
  for (i=0; i<nrows; i++) {
    printf(" %d", piv->row_count[i]);
  }  

  printf("\nColumn partition\n");
  for (i=0; i<=PARTITION_SIZE; i++) {
    if (! empty_partition(&piv->col_partition, i + 1)) {
      printf("Size %d: ", i);
      print_partition(&piv->col_partition, i + 1);
    }
  }

  printf("Column counts:");
  for (i=0; i<ncolumns; i++) {
    printf(" %d", piv->col_count[i]);
  }
  printf("\n\n");
}

#endif

/*
 * Initialize pivoter structure for nrows and ncolumns
 */
static void init_pivoter(pivoter_t *piv, int nrows, int ncolumns) {
  // partitions
  init_partition(&piv->row_partition, nrows, PARTITION_SIZE + 1);
  init_partition(&piv->col_partition, ncolumns, PARTITION_SIZE + 1);

  // row/column counts
  piv->row_count = (int *) safe_malloc(nrows * sizeof(int));
  piv->col_count = (int *) safe_malloc(ncolumns * sizeof(int));
}


/*
 * Cleanup: delete allocated arrays
 */
static void cleanup_pivoter(pivoter_t *piv) {
  delete_partition(&piv->row_partition);
  delete_partition(&piv->col_partition);
}


/*
 * Get partition index for a row or column of size s
 * size 0 --> partition 1
 * size 1 --> partition 2
 * ...
 * size >= PARTITION_SIZE --> index = PARTITION_SIZE + 1
 */
static inline int partition_index(int s) {
  s ++;
  return (s > PARTITION_SIZE+1) ? (PARTITION_SIZE+1) : s;
}





/*
 * Check whether given v contains at least one idx x
 * that's marked for elimination (i.e., such that, count[x] >= 0)
 */
static int elim_index_occurs_in_vector(mat_vector_t *v, int *count) {
  int i, n, x;

  n = v->size;
  for (i=0; i<n; i++) {
    x = v->data[i].idx;
    if (x >= 0 && count[x] >= 0) {
      return TRUE;
    }
  }

  return FALSE;
}



/*
 * Markowitz's heuristic: scan a row or column 
 * vector to find the best column or row index.
 *
 * The best index is the one with smallest count.
 * - a pointer to the best element is returned.
 *   i.e., k such that v->data[k] = <idx, j, coeff>)
 *   with idx = best index
 * - if the vector is empty, then -1 is returned
 */
static int best_index_in_vector(mat_vector_t *v, int *count) {
  int i, n, x, min, best_i, ne;

  best_i = -1;
  min = INT_MAX;
  n = v->size;
  for (i=0; i<n; i++) {
    x = v->data[i].idx;
    if (x >= 0) {
      ne = count[x];
      assert (ne >= 0);
      if (ne < min) {
	min = ne;
	best_i = i;
      }
    }
  }

  return best_i;
}


/*
 * Same function for partial elimination: picks the best index
 * among those that have non-negative count.
 */
static int best_elim_index_in_vector(mat_vector_t *v, int *count) {
  int i, n, x, min, best_i, ne;

  best_i = -1;
  min = INT_MAX;
  n = v->size;
  for (i=0; i<n; i++) {
    x = v->data[i].idx;
    if (x >= 0) {
      ne = count[x];
      if (0 <= ne && ne < min) {
	min = ne;
	best_i = i;
      }
    }
  }

  return best_i;  
}



/*
 * Abbreviations
 */
static inline int best_row_in_column(pivoter_t *piv, mat_vector_t *column) {
  return best_index_in_vector(column, piv->row_count);
}

static inline int best_column_in_row(pivoter_t *piv, mat_vector_t *row) {
  return best_index_in_vector(row, piv->col_count);
}

static inline int best_elim_row_in_column(pivoter_t *piv, mat_vector_t *column) {
  return best_elim_index_in_vector(column, piv->row_count);
}

static inline int best_elim_column_in_row(pivoter_t *piv, mat_vector_t *row) {
  return best_elim_index_in_vector(row, piv->col_count);
}





/*
 * Initialize pivoter for full elimination:
 * - all non-empty rows/columns of m are marked for elimination
 */
static void prepare_elimination(pivoter_t *piv, matrix_t *m) {
  int i, n, s;

  clear_partition(&piv->col_partition);
  clear_partition(&piv->row_partition);

  n = m->ncolumns;
  for (i=0; i<n; i++) {
    s = m->column[i].nelems;
    if (s > 0) {
      piv->col_count[i] = s;
      partition_add(&piv->col_partition, i, partition_index(s));
    } else {
      piv->col_count[i] = PTAG_EMPTY;
    }
  }

  n = m->nrows;
  for (i=0; i<n; i++) {
    s = m->row[i].nelems;
    if (s > 0) {
      piv->row_count[i] = s;
      partition_add(&piv->row_partition, i, partition_index(s));
    } else {
      piv->row_count[i] = PTAG_EMPTY;
    }
  }  
}


/*
 * Initialize pivoter for partial elimination
 * - col = array of columns to eliminate
 * - p = size of col
 * - all non-empty columns of col are marked for elimination
 * - columns not in col are marked with PTAG_TO_KEEP
 * - all non-empty rows that contain at least one 
 *   column of col are marked for elimination
 */
static void prepare_partial_elimination(pivoter_t *piv, matrix_t *m, int *col, int p) {
  int i, c, n, s;

  clear_partition(&piv->col_partition);
  clear_partition(&piv->row_partition);

  n = m->ncolumns;
  for (i=0; i<n; i++) {
    piv->col_count[i] = PTAG_TO_KEEP;
  }

  for (i=0; i<p; i++) {
    c = col[i];
    if (piv->col_count[c] == PTAG_TO_KEEP) {
      // just to make sure c does not get added twice to col_partition
      s = m->column[c].nelems;
      if (s > 0) {
	piv->col_count[c] = s;
	partition_add(&piv->col_partition, c, partition_index(s));
      } else {
	piv->col_count[c] = PTAG_EMPTY;
      }
    }
  }

  n = m->nrows;
  for (i=0; i<n; i++) {
    s = m->row[i].nelems;
    if (s > 0 && elim_index_occurs_in_vector(m->row + i, piv->col_count)) {
      piv->row_count[i] = s;
      partition_add(&piv->row_partition, i, partition_index(s));
    } else {
      piv->row_count[i] = PTAG_EMPTY;
    }
  }  
}

/*
 * Pivot selection: select a pair row/column 
 * that minimize (count[r] - 1) * (count[c] - 1)
 *
 * Assumes that no row or column with count = 1 is present
 * (i.e., no singleton row or column).
 *
 * The function returns 1 if a pair is found
 * or 0 if the column or row partition is empty.
 *
 * The result is stored in *row = i, *column = j
 * and *c_ptr = k where
 * column[j] ->data[k] = element corresponding to row i
 *
 * MAX_ATTEMPTS is a bound on the number of columns and 
 * rows explored.
 */
#define MAX_ATTEMPTS 50

static int pivot_selection(matrix_t *m, pivoter_t *piv, int *row, int *r_ptr, int *column, int *c_ptr) {
  int k, i, c, r, nattempts;
  int score, best_score;

  // Search for best row/column pair, by considering columns 
  // and rows in order of increasing size. Stop after MAX_ATTEMPTS 
  // rows or columns have been examined.

  nattempts = MAX_ATTEMPTS;
  best_score = INT_MAX;
  *row = -1;
  *column = -1;
  *c_ptr = -1;
  *r_ptr = -1;

  for (k = 2; k < PARTITION_SIZE; k ++) {
    // check columns of size k
    c = partition_get_first(&piv->col_partition, k+1);
    while (c >= 0) {
      i = best_row_in_column(piv, m->column + c);
      assert(i >= 0);

      r = m->column[c].data[i].idx;
      score = (k - 1) * (piv->row_count[r] - 1);

      if (score < best_score) {
	best_score = score;
	*row = r;
	*column = c;
	*c_ptr = i;
	*r_ptr = m->column[c].data[i].ptr;
      }
      nattempts --;
      if (nattempts == 0) goto done;
      c = partition_get_next(&piv->col_partition, c);
    }
    
    // best possible score in non-explored 
    // rows and columns: column of size k+1, row of size k
    if (best_score <= k * (k - 1)) goto done;

    // check rows of size k
    r = partition_get_first(&piv->row_partition, k+1);
    while (r >= 0) {
      i = best_column_in_row(piv, m->row + r);
      assert(i >= 0);

      c = m->row[r].data[i].idx;
      score = (k - 1) * (piv->col_count[c] - 1);

      if (score < best_score) {
	best_score = score;
	*row = r;
	*column = c;
	*c_ptr = m->row[r].data[i].ptr;
	*r_ptr = i;
      }
      nattempts --;
      if (nattempts == 0) goto done;
      r = partition_get_next(&piv->row_partition, r);
    }

    if (best_score <= k * k) goto done;
  }

  // last set: columns of size at least PARTITION_SIZE
  c = partition_get_first(&piv->col_partition, k+1);
  while (c >= 0) {
    i = best_row_in_column(piv, m->column + c);
    assert(i >= 0);

    r = m->column[c].data[i].idx;
    score = (piv->col_count[c] - 1) * (piv->row_count[r] - 1);

    if (score < best_score) {
      best_score = score;
      *row = r;
      *column = c;
      *c_ptr = i;
      *r_ptr = m->column[c].data[i].ptr;
    }
    nattempts --;
    if (nattempts == 0) goto done;
    c = partition_get_next(&piv->col_partition, c);
  }

  if (*row < 0) {
    return 0;
  }

 done:
#ifdef DEBUG
  printf("nattempts = %d\n", nattempts);
#endif
  return 1;
}



/*
 * Pivot selection: variant for partial elimination: 
 * only columns with non-negative count can be chosen.
 *
 * The function returns 1 if a pair is found
 * or 0 if the column or row partition is empty.
 *
 * The result is stored in *row = i, *column = j
 * and *c_ptr = k where
 * column[j] ->data[k] = element corresponding to row i
 *
 */
static int pivot_selection_partial(matrix_t *m, pivoter_t *piv, 
				   int *row, int *r_ptr, int *column, int *c_ptr) {
  int k, i, c, r, nattempts;
  int score, best_score;


  // Search for best row/column pair, by considering columns 
  // and rows in order of increasing size. Stop after MAX_ATTEMPTS 
  // rows or columns have been examined.

  nattempts = MAX_ATTEMPTS;
  best_score = INT_MAX;
  *row = -1;
  *column = -1;
  *c_ptr = -1;
  *r_ptr = -1;

  for (k = 2; k < PARTITION_SIZE; k ++) {
    // check columns of size k
    c = partition_get_first(&piv->col_partition, k+1);
    while (c >= 0) {
      i = best_row_in_column(piv, m->column + c);
      assert(i >= 0);

      r = m->column[c].data[i].idx;
      score = (k - 1) * (piv->row_count[r] - 1);

      if (score < best_score) {
	best_score = score;
	*row = r;
	*column = c;
	*c_ptr = i;
	*r_ptr = m->column[c].data[i].ptr;
      }
      nattempts --;
      if (nattempts == 0) goto done;
      c = partition_get_next(&piv->col_partition, c);
    }
    
    // best possible score in non-explored 
    // rows and columns: column of size k+1, row of size k
    if (best_score <= k * (k - 1)) goto done;

    // check rows of size k
    r = partition_get_first(&piv->row_partition, k+1);
    while (r >= 0) {
      i = best_elim_column_in_row(piv, m->row + r);
      if (i >= 0) {
	c = m->row[r].data[i].idx;
	score = (k - 1) * (piv->col_count[c] - 1);

	if (score < best_score) {
	  best_score = score;
	  *row = r;
	  *column = c;
	  *c_ptr = m->row[r].data[i].ptr;
	  *r_ptr = i;
	}

	nattempts --;
	if (nattempts == 0) goto done;
	r = partition_get_next(&piv->row_partition, r);


      } else {
	// r contains no column indices to eliminate. 
	// remove it from piv->row_partition
	c = partition_get_next(&piv->row_partition, r);
	partition_remove(&piv->row_partition, r);
	piv->row_count[r] = PTAG_EMPTY;
	r = c;

	nattempts --;
	if (nattempts == 0 && *row >= 0) goto done;
      }
    }

    if (best_score <= k * k) goto done;
  }

  // last set: columns of size at least PARTITION_SIZE
  c = partition_get_first(&piv->col_partition, k+1);
  while (c >= 0) {
    i = best_row_in_column(piv, m->column + c);
    assert(i >= 0);

    r = m->column[c].data[i].idx;
    score = (piv->col_count[c] - 1) * (piv->row_count[r] - 1);

    if (score < best_score) {
      best_score = score;
      *row = r;
      *column = c;
      *c_ptr = i;
      *r_ptr = m->column[c].data[i].ptr;
    }
    nattempts --;
    if (nattempts == 0) goto done;
    c = partition_get_next(&piv->col_partition, c);
  }

  if (*row < 0) {
    return 0;
  }

 done:
#ifdef DEBUG
  printf("nattempts = %d\n", nattempts);
#endif
  return 1;
}





/***************************************
 * ROW OPERATIONS USED IN ELIMINATION  *
 **************************************/

/*
 * Variant of clear_row that also updates the column partition
 */
static void clear_row_and_update(matrix_t *m, pivoter_t *piv, int r_idx, mat_vector_t *row) {
  int i, n, c, p;

  n = row->size;
  for (i=0; i<n; i++) {
    c = row->data[i].idx;
    if (c >= 0) {
      // release coefficient
      rat_clear(&row->data[i].coeff);
      // delete the column dependency
      p = row->data[i].ptr;
      free_mat_elem(m->column + c, p);
      // update the partition: move c to its new set
      if (piv->col_count[c] >= 0) {
	piv->col_count[c] --;
	partition_move(&piv->col_partition, c, partition_index(piv->col_count[c]));
      }
    }
  }

  row->size = 0;
  row->free = -1;
  row->nelems = 0;
}


/*
 * Variant of copy_buffer_in_row that also updates the column partition
 * and empties the buffer.
 */
static void copy_buffer_in_row_and_update(matrix_t *m, pivoter_t *piv, buffer_t *buffer,
					  int r_idx, mat_vector_t *row) {
  int i, n, c, p;
  mat_elem_t *re;
  mat_vector_t *column;

  n = buffer->nelems;
  row->size = n;
  row->nelems = n;
  re = row->data;
  for (i=0; i<n; i++) {
    c = buffer->active[i];
    // clear tag in buffer
    buffer->tag[c] = ZERO_COEFF;

    // copy index and coefficient
    re->idx = c;
    rat_set(&re->coeff, buffer->q + c);
    // add column dependency
    column = m->column + c;
    p = alloc_mat_elem(column);
    column->data[p].idx = r_idx;
    column->data[p].ptr = i;
    column->data[p].coeff = re->coeff;
    // set back pointer
    re->ptr = p;

    // update the column partition
    if (piv->col_count[c] >= 0) {
      piv->col_count[c] ++;
      partition_move(&piv->col_partition, c, partition_index(piv->col_count[c]));
    }

    re ++;
  }

  buffer->nelems = 0;
}


/*
 * Replace row of index r_idx by buffer.
 * Side effect: buffer is emptied.
 * Update the column and row partitions.
 */
static void replace_row(matrix_t *m, pivoter_t *piv, int r_idx, buffer_t *buffer) {
  mat_vector_t *row;

  normalize_buffer(buffer);
  row = m->row + r_idx;
  clear_row_and_update(m, piv, r_idx, row);
  adjust_mat_vector_capacity(row, buffer->nelems);
  copy_buffer_in_row_and_update(m, piv, buffer, r_idx, row);

  piv->row_count[r_idx] = m->row[r_idx].nelems;
  partition_move(&piv->row_partition, r_idx, partition_index(piv->row_count[r_idx]));
}



/*
 * Detach a row of index r_idx:
 * - remove dependencies: remove r_idx from all column vectors
 * - update the column partition.
 */
static void detach_row(matrix_t *m, pivoter_t *piv, int r_idx) {
  mat_vector_t *row;
  int i, n, c, p;

  // clear all dependencies in that row
  row = m->row + r_idx;
  n = row->size;
  for (i=0; i<n; i++) {
    c = row->data[i].idx;
    if (c >= 0) {
      p = row->data[i].ptr;
      free_mat_elem(m->column + c, p);
      // update the column partition
      if (piv->col_count[c] >= 0) {
	assert(piv->col_count[c] > 0);
	piv->col_count[c] --;
	partition_move(&piv->col_partition, c, partition_index(piv->col_count[c]));
      }
    }
  }
}



/*
 * Move r_idx/c_idx into the row/column lists
 * and remove them from the partitions.
 */
static void end_elim_step(pivoter_t *piv, int r_idx, int c_idx) {
  partition_remove(&piv->row_partition, r_idx);
  partition_remove(&piv->col_partition, c_idx);

  piv->row_count[r_idx] = PTAG_EMPTY;
  piv->col_count[c_idx] = PTAG_EMPTY;
}





/**************************
 *  GAUSSIAN ELIMINATION  *
 *************************/

/*
 * Allocation of a new gauss matrix
 * nrows = initial number of rows
 * ncolumns = initial number of columns
 * The perm/pivot structures are not initalized yet.
 * The buffer is not allocated
 */
gauss_matrix_t *new_gauss_matrix(int nrows, int ncolumns) {
  gauss_matrix_t *tmp;

  tmp = (gauss_matrix_t *) safe_malloc(sizeof(gauss_matrix_t));
  init_matrix(&tmp->m, nrows, ncolumns);

  tmp->buffer = NULL;
  rat_init(&tmp->r0);

  return tmp;
}


/*
 * Initialize the elim structure and allocate buffer.
 */
void gauss_elim_prepare(gauss_matrix_t *m) {
  init_permutation(&m->perm, m->m.nrows, m->m.ncolumns);
  init_pivoter(&m->pv, m->m.nrows, m->m.ncolumns);
  m->row_dptr = (int *) safe_malloc(m->m.nrows * sizeof(int));
  m->buffer = new_buffer(m->m.ncolumns);
}


/*
 * Delete matrix m
 */
void delete_gauss_matrix(gauss_matrix_t *m) {
  cleanup_matrix(&m->m);
  cleanup_permutation(&m->perm);
  cleanup_pivoter(&m->pv);
  safe_free(m->row_dptr);
  delete_buffer(m->buffer);
  rat_clear(&m->r0);
}



/*
 * One step of Gaussian elimination: special case when the column
 * contains a single non-zero element
 * \param c_idx = column index
 */
static void gauss_elim_singleton_column(gauss_matrix_t *m, int c_idx) {
  int i, r_idx;
  mat_vector_t *column;

  // find the unique row index in this column
  column = m->m.column + c_idx;
  i = 0;
  for (;;) {
    r_idx = column->data[i].idx;
    if (r_idx >= 0) break;
    i ++;
  }

#ifdef DEBUG
  printf("Gauss elim: x%d, row %d (singleton column)\n", c_idx, r_idx);

  if (i >= column->size) {
    printf("**** BUG: bad index in gauss_elim_singleton_column\n");
    fflush(stdout);
  }
#endif

  m->row_dptr[r_idx] = column->data[i].ptr; // diagonal pointer for row r_idx
  detach_row(&m->m, &m->pv, r_idx);

  permutation_add(&m->perm, r_idx, c_idx);
  end_elim_step(&m->pv, r_idx, c_idx);
}



/*
 * One step of Gaussian elimination: special case when the row
 * contains a single non-zero element (or a single non-zero
 * marked for elimination).
 * \param r_idx = row index
 * \param r_ptr = pointer in row r_idx to the non-zero element
 */
static void gauss_elim_singleton_row(gauss_matrix_t *m, int r_idx, int r_ptr) {
  mat_vector_t *column, *row;
  int c_idx, i, n, r, p;

  row = m->m.row + r_idx;
  c_idx = row->data[r_ptr].idx;
  column = m->m.column + c_idx;

#ifdef DEBUG
  printf("Gauss elim: x%d, row %d (singleton row)\n", c_idx, r_idx);
#endif

  m->row_dptr[r_idx] = r_ptr; // diagonal pointer for row[r_idx] = r_ptr  


  // clear all coefficients in column c_idx, 
  // except the pivot (the one at row r_idx).
  n = column->size;
  for (i=0; i<n; i++) {
    r = column->data[i].idx;
    if (r >= 0 && r != r_idx) {
      // clear coefficient m[r, c_idx]
      rat_clear(&column->data[i].coeff);
      // remove the row element
      p = column->data[i].ptr;
      free_mat_elem(m->m.row + r, p);
      // update the row partition
      partition_move(&m->pv.row_partition, r, partition_index(m->m.row[r].nelems));
    }
  }

  // empty column c_idx (row r_idx is detached).
  column->size = 0;
  column->nelems = 0;
  column->free = -1;

  permutation_add(&m->perm, r_idx, c_idx);
  end_elim_step(&m->pv, r_idx, c_idx);
}


/*
 * Gaussian elimination: general case
 * \param c_idx = column index
 * \param r_idx = row index
 * \param c_ptr = index of element r_idx in colum[c_idx].data
 * \param r_ptr = index of element c_idx in row[r_idx].data
 *
 * The pivot element m[r_idx, c_idx] is non-zero.
 * - for every active rows r such that m[r, c_idx] /= 0,
 *   replace row[r] by row[r] - (m[r, c_idx]/m[r_idx, c_idx]) * row[r_idx]
 * - move r_idx and c_idx into the eliminated lists
 * - update dependencies.
 */
static void gauss_elim(gauss_matrix_t *m, int c_idx, int r_idx, int c_ptr, int r_ptr) {
  mat_vector_t *column;
  mat_vector_t *row, *pivot_row;
  mat_elem_t *ce;
  int i, n, r;
  rat_t *pv_coeff, *factor;

  // auxiliary rational variables.
  factor = &m->r0;

  // get pivot coeff
  column = m->m.column + c_idx;
  pv_coeff = &column->data[c_ptr].coeff;
  pivot_row = m->m.row + r_idx;  

  // set diag pointers for r_idx
  m->row_dptr[r_idx] = r_ptr;

#ifdef DEBUG
  printf("Gauss elim: x%d, row %d (row size = %d, col size = %d)\n", c_idx, r_idx,
	 m->m.row[r_idx].nelems, m->m.column[c_idx].nelems);

  if (rat_is_zero(pv_coeff)) {
    printf("**** BUG: zero pivot ****\n");
    fflush(stdout);
  }
#endif

  // Elimination loop
  n = column->size;
  ce = column->data;

  for (i=0; i<n; i++) {
    r = ce[i].idx;
    if (r >= 0 && r != r_idx) {
      // eliminate c_idx from row r
      row = m->m.row + r;
      // factor = m[r, c_idx]/m[r_idx, c_idx] 
      //      = column->data[i].coeff / pv_coeff
      rat_set(factor, &ce[i].coeff);
      rat_div(factor, pv_coeff);
      // elimination (via buffer).
      copy_mat_vector_in_buffer(m->buffer, row);
      submul_mat_vector_from_buffer(m->buffer, pivot_row, factor);
      replace_row(&m->m, &m->pv, r, m->buffer);

      rat_clear(factor);
    }
  }

  detach_row(&m->m, &m->pv, r_idx);

  permutation_add(&m->perm, r_idx, c_idx);
  end_elim_step(&m->pv, r_idx, c_idx);
}




/*
 * Eliminate a set of columns from a matrix m
 * - array col contains the indices of the columns to eliminate
 * - n = number of elements in col
 * - must be used after call to gauss_elim_prepare
 */
void eliminate_columns(gauss_matrix_t *m, int col[], int n) {
  int c, cp, r, rp;

  reset_permutation(&m->perm, m->m.nrows, m->m.ncolumns);
  prepare_partial_elimination(&m->pv, &m->m, col, n);  

 loop: 
  //  print_pivoter(&m->pv, m->m.nrows, m->m.ncolumns);

  // try singleton columns first
  c = partition_get_first(&m->pv.col_partition, 2);
  if (c >= 0) {
    gauss_elim_singleton_column(m, c);
    goto loop;
  }

  // singleton rows
  r = partition_get_first(&m->pv.row_partition, 2);
  while (r >= 0) {
    rp = best_column_in_row(&m->pv, m->m.row + r);
    if (rp >= 0) {
      gauss_elim_singleton_row(m, r, rp);
      goto loop;
    }
    r = partition_get_next(&m->pv.row_partition, r);
  }

  // General case:
  if (pivot_selection_partial(&m->m, &m->pv, &r, &rp, &c, &cp)) {
    gauss_elim(m, c, r, cp, rp);
    goto loop;
  }
}



/*
 * Clear all rows of m that are in the eliminated row list
 * These rows are detached from the rest of m: they do
 * not occur in the columns.
 */
void clear_eliminated_rows(gauss_matrix_t *m) {
  list_t *l;
  int i, j, n;
  mat_vector_t *row;

  l = &m->perm.row_list;

  // scan eliminated rows and release all rational coefficients.
  // then empty the rows.
  i = first_of_list(l);
  while (i >= 0) {
    row = m->m.row + i;
    n = row->size;
    for (j=0; j<n; j++) {
      rat_clear(&row->data[j].coeff);
    }
    row->size = 0;
    row->free = -1;
    row->nelems = 0;

    i = next_in_list(l, i);
  }

}


/*
 * Full triangulation.
 */
void eliminate_all_columns(gauss_matrix_t *m) {
  int c, cp, r, rp;

  reset_permutation(&m->perm, m->m.nrows, m->m.ncolumns);
  prepare_elimination(&m->pv, &m->m);

 loop: 
  //  print_pivoter(&m->pv, m->m.nrows, m->m.ncolumns);

  // try singleton columns first
  c = partition_get_first(&m->pv.col_partition, 2);
  if (c >= 0) {
    gauss_elim_singleton_column(m, c);
    goto loop;
  }

  // singleton rows
  r = partition_get_first(&m->pv.row_partition, 2);
  if (r >= 0) {
    rp = best_column_in_row(&m->pv, m->m.row + r);
    assert (rp >= 0);
    gauss_elim_singleton_row(m, r, rp);
    goto loop;
  }

  // General case:
  if (pivot_selection(&m->m, &m->pv, &r, &rp, &c, &cp)) {
    gauss_elim(m, c, r, cp, rp);
    goto loop;
  }
}




/**************************************************************
 *  COMPACT MATRICES: STORE RESULTS OF GAUSSIAN ELIMINATION   *
 *************************************************************/

/*
 * Initialize a vector array:
 * \param n = number of vectors
 * \param vb_size = total number of elements to be stored 
 *                = sum of the lengths of the vectors
 */
static void init_vector_array(vector_array_t *v, int n, int vb_size) {
  v->nvectors = n;
  v->vindex = (int *) safe_malloc((n + 1) * sizeof(int));
  v->vblock = (vector_elem_t *) safe_malloc(vb_size * sizeof(vector_elem_t));
}


/*
 * Create a compact matrix to store the triangular sub-matrix of m
 * (i.e., the matrix formed by elim->row_list)
 * Only the rows are stored by this function.
 *
 * Rows are renumbered from 0 to n-1 where n is the number of 
 * triangular rows. The diagonal element in each row is stored in
 * first position. Columns are not renumbered. They have the same
 * index in the compact matrix as in m.
 */
compact_matrix_t *construct_triangular_row_matrix(gauss_matrix_t *m) {
  compact_matrix_t *tmp;
  list_t *list;
  mat_vector_t *row;
  vector_elem_t *vblock;
  int i, j, k, vsize, dsize;
  int n, p, idx, diag_idx;
  
  // compute vector size
  vsize = 0;
  list = &m->perm.row_list;
  i = first_of_list(list);
  while (i >= 0) {
    row = m->m.row + i;
    vsize += row->nelems;
    i = next_in_list(list, i);
  }

  // dsize = number of rows in triangle list
  dsize = m->perm.size;

  // allocate the matrix and its components
  tmp = (compact_matrix_t *) safe_malloc(sizeof(compact_matrix_t));
  tmp->nrows = dsize;
  tmp->ncolumns = m->m.ncolumns;
  tmp->diag_size = dsize;
  tmp->col_list = (int *) safe_malloc(dsize * sizeof(int));
  tmp->col_order = (int *) safe_malloc(m->m.ncolumns * sizeof(int));

  tmp->vsize = vsize;
  init_vector_array(&tmp->rows, dsize, vsize);

  // empty column array
  tmp->columns.nvectors = 0;
  tmp->columns.vindex = NULL;
  tmp->columns.vblock = NULL;

  // copy the column position array into col_order
  // also set the column permutation in col_list
  n = m->m.ncolumns;
  for (i=0; i<n; i++) {
    j = m->perm.col_order[i];
    if (j >= 0) {
      tmp->col_order[i] = j;
      tmp->col_list[j] = i;
    } else {
      tmp->col_order[i] = -1; // not on diagonal
    }
  }


  // store the rows and setup the row-permutation array
  vblock = tmp->rows.vblock;

  j = 0;   // row index in compact matrix
  k = 0;   // index in tmp->rows.vblock = vblock

  list = &m->perm.row_list;
  i = first_of_list(list);
  while (i >= 0) {
    // row i in m becomes row j in the compact matrix
    tmp->rows.vindex[j] = k;

    // copy the row
    row = m->m.row + i;
    n = row->size;

    // put the diagonal element first.
    p = m->row_dptr[i];
    diag_idx = row->data[p].idx;
    rat_set(&vblock[k].coeff, &row->data[p].coeff);
    vblock[k].idx = diag_idx;
    k++;

    // rest of the row
    for (p=0; p<n; p++) {
      idx = row->data[p].idx;
      if (idx >= 0 && idx != diag_idx) {
	rat_set(&vblock[k].coeff, &row->data[p].coeff);
	vblock[k].idx = idx;
	k++;
      }
    }

    // next triangle row
    j ++;
    i = next_in_list(list, i);
  }
  tmp->rows.vindex[j] = k;

  return tmp;
}


/*
 * Compute the column data for a compact matrix m
 * - assumes that the row data has been set
 */
void build_columns(compact_matrix_t *m) {
  int i, j, k, l, n, nc, nr;
  int *row_index, *col_index;
  vector_elem_t *row_block, *col_block;

  // allocate column-vector array
  n = m->vsize;
  nc = m->ncolumns;
  nr = m->nrows;
  init_vector_array(&m->columns, nc, n);

  row_index = m->rows.vindex;
  row_block = m->rows.vblock;
  col_index = m->columns.vindex;
  col_block = m->columns.vblock;

  // store size of column i into col_index[i+1]
  for (i=0; i <= nc; i++) {
    col_index[i] = 0;
  }
  for (i=0; i<n; i++) {
    j = row_block[i].idx + 1;
    col_index[j] ++;
  }

  // store start of column i into col_index[i+1]
  j = 0;
  for (i=1; i <= nc; i++) {
    k = col_index[i];
    col_index[i] = j;
    j += k;
  }

  // copy elements from row_block to col_block
  j = 0;
  for (i=0; i < nr; i++) {
    n = row_index[i+1];
    while (j < n) {
      l = row_block[j].idx + 1;
      k = col_index[l];
      col_block[k].idx = i;
      rat_set(&col_block[k].coeff, &row_block[j].coeff);
      col_index[l] = k + 1;
      j ++;
    }
  }

}


/*
 * Create a compact matrix to store the triangular sub-matrix of m
 * (i.e., the matrix formed by the list of triangle rows)
 * Bot rows and columns are constructed by this function.
 *
 * Rows are renumbered from 0 to n-1 where n is the number of 
 * triangle rows. Columns are not renumbered.
 */
compact_matrix_t *construct_triangular_matrix(gauss_matrix_t *m) {
  compact_matrix_t *result;

  result = construct_triangular_row_matrix(m);
  build_columns(result);

  return result;
}

/**
 *  Delete a compact matrix
 */
void delete_compact_matrix(compact_matrix_t *m) {
  safe_free(m->col_list);
  safe_free(m->col_order);

  safe_free(m->rows.vindex);
  safe_free(m->rows.vblock);

  safe_free(m->columns.vindex);
  safe_free(m->columns.vblock);

  safe_free(m);
}




/*******************
 *  DFS STRUCTURE  *
 ******************/  

/*
 * For a triangular square matrix m, one can construct
 * a row-dependency and a column-dependency graph.
 * In column-dependency graph: 
 *   edge i --> j means that j occurs as an index in column i
 *   (i.e., a_ji is non-zero)
 * In row-dependency graph:
 *   edge i --> j means that j occurs as an index in row i
 *   (i.e., a_ij is non-zero).
 *
 * For solving linear equations A x = a or y A = b where
 * A is a triangular matrix and a and b are sparse,
 * we use DFS search in the column-dependency or
 * row-dependency graphs. (Gilbert & Peierls technique).
 */

/*
 * Initialize a dfs structure for an n by n matrix
 */
static void init_dfs(dfs_t *d, int n) {
  int i;

  d->size = n;
  d->top = -1;
  d->head = END_OF_LIST;  

  d->next = (int *) safe_malloc(n * sizeof(int));
  d->index = (int *) safe_malloc(n * sizeof(int));
  d->counter = (int*) safe_malloc(n * sizeof(int));
  d->vector = (mat_elem_t **) safe_malloc(n * sizeof(mat_elem_t *));

  for (i=0; i<n; i++) {
    d->next[i] = NOT_IN_LIST;
  }
}


/*
 * Allocation and initialization of a dfs_t structure
 * for an n by n matrix.
 */
dfs_t *new_dfs(int n) {
  dfs_t *tmp;
  
  tmp = (dfs_t *) safe_malloc(sizeof(dfs_t));
  init_dfs(tmp, n);

  return tmp;
}


/*
 * Cleanup
 */
static void cleanup_dfs(dfs_t *d) {
  safe_free(d->next);
  safe_free(d->index);
  safe_free(d->counter);
  safe_free(d->vector);  
}

/*
 * Delete dfs structure d
 */
void delete_dfs(dfs_t *d) {
  cleanup_dfs(d);
  safe_free(d);
}


/*
 * Resize d to accommodate at least n rows or columns
 * - no effect if d is already large enough
 */
void resize_dfs(dfs_t *d, int n) {
  int i;

  if (n > d->size) {
    d->next = (int *) safe_realloc(d->next, n * sizeof(int));
    d->index = (int *) safe_realloc(d->index, n * sizeof(int));
    d->counter = (int *) safe_realloc(d->counter, n * sizeof(int));
    d->vector = (mat_elem_t **) safe_realloc(d->vector, n * sizeof(mat_elem_t *));

    for (i = d->size; i <n; i++) {
      d->next[i] = NOT_IN_LIST;
    }
    d->size = n;
  }
}


/*
 * Check whether the list is empty
 */
static inline int empty_list(dfs_t *d) {
  return d->head < 0;
}

/*
 * Get car of the list
 */
static inline int car_list(dfs_t *d) {
  return d->head;
}

/*
 * Move to next element (and remove head)
 */
static inline void cdr_list(dfs_t *d) {
  int h;

  h = d->head;
  d->head = d->next[h];
  d->next[h] = NOT_IN_LIST;
}


/*
 * Add i as head of the list
 */
static inline void cons_list(dfs_t *d, int i) {
  d->next[i] = d->head;
  d->head = i;
}



/*
 * Check whether the stack is empty
 */
static inline int empty_stack(dfs_t *d) {
  return d->top < 0;
}


/*
 * Check whether index i is unexplored
 */
static inline int unexplored(dfs_t *d, int i) {
  return d->next[i] == NOT_IN_LIST;
}


/*
 * Push mat_vector *v and index i onto the stack
 */
static inline void push_vector(dfs_t *d, int i, mat_vector_t *v) {
  int t;

  // mark that i is under exploration
  d->next[i] = ON_STACK;

  // push <i, r->data, r->size - 1> on top of the stack
  t = d->top + 1;
  d->index[t] = i; 
  d->counter[t] = v->size - 1;
  d->vector[t] = v->data;
  d->top = t;
}


/*
 * Pop top element
 */
static inline void pop_vector(dfs_t *d) {
  d->top --;
}


/*
 * Get components of the top triple
 * - require d not empty
 */
static inline int top_index(dfs_t *d) {
  return d->index[d->top];
}

static inline int top_counter(dfs_t *d) {
  return d->counter[d->top];
}

static inline mat_elem_t *top_vector(dfs_t *d) {
  return d->vector[d->top];
}


/*
 * Update the top counter
 */
static inline void set_top_counter(dfs_t *d, int c) {
  d->counter[d->top] = c;
}








/*************************
 *  TRIANGULAR MATRICES  *
 ************************/

/*
 * Initialize triangular matrix m for n rows/n columns
 */
static void init_triangular_matrix(triangular_matrix_t *m, int n) {
  init_matrix(&m->m, n, n);

  m->diag_row = NULL;
  m->diag_column = NULL;
  m->row_dptr = NULL;
  m->col_dptr = NULL;  
}


/*
 * Allocate an n by n triangular_matrix
 * - the matrix is empty.
 * - diag_row, diag_column, row_dptr, and col_dptr are not allocated.
 */
triangular_matrix_t *new_triangular_matrix(int n) {
  triangular_matrix_t *tmp;

  tmp = (triangular_matrix_t *) safe_malloc(sizeof(triangular_matrix_t));
  init_triangular_matrix(tmp, n);

  return tmp;
}

/*
 * Clean up: free internal structures
 */
static void cleanup_triangular_matrix(triangular_matrix_t *m) {
  int i, n;

  n = m->m.nrows;
  for (i=0; i<n; i++) {
    delete_mat_vector(m->m.row + i);
    delete_mat_vector(m->m.column + i);
  }
  safe_free(m->m.row);
  safe_free(m->m.column);

  safe_free(m->diag_row);
  safe_free(m->diag_column);
  safe_free(m->row_dptr);
  safe_free(m->col_dptr);  
}


/*
 * Delete triangular matrix m
 */
void delete_triangular_matrix(triangular_matrix_t *m) {
  cleanup_triangular_matrix(m);
  safe_free(m);
}





/****************************************************
 *  EQUATIONS A x = a AND y A = b FOR A TRIANGULAR  *
 ***************************************************/

/*
 * Get diagonal column for row r_idx.
 */
static inline int diag_column_idx(triangular_matrix_t *m, int r_idx) {
  return m->diag_column[r_idx];
}

static inline mat_vector_t *diag_column_vector(triangular_matrix_t *m, int r_idx) {
  return m->m.column + diag_column_idx(m, r_idx);
}


/*
 * Get diagonal row for column c_idx
 */
static inline int diag_row_idx(triangular_matrix_t *m, int c_idx) {
  return m->diag_row[c_idx];
}

static inline mat_vector_t *diag_row_vector(triangular_matrix_t *m, int c_idx) {
  return m->m.row + diag_row_idx(m, c_idx);
}



/*
 * Given a row index r_idx, computes all other row indices 
 * that depend on r_idx in the column-dependency graph.
 * - assumptions: stack is empty and is large enough.
 */
static void dfs_row_explore(triangular_matrix_t *m, int r_idx, dfs_t *stack) {
  int c, idx;
  mat_elem_t *v;

  if (unexplored(stack, r_idx)) {
    push_vector(stack, r_idx, diag_column_vector(m, r_idx));

    // Depth-first search
    do {
      c = top_counter(stack);
      v = top_vector(stack);

      // next unexplored element on column vector v
      while (c >= 0) {
	idx = v[c].idx; // row_index
	if (idx >= 0 && unexplored(stack, idx)) break;
	c --;
      }

      if (c >= 0) {
	set_top_counter(stack, c - 1); // save counter
	push_vector(stack, idx, diag_column_vector(m, idx));
      } else {
	// topological sort: add top-idx at the head of the list
	cons_list(stack, top_index(stack));
	pop_vector(stack);
      }
    } while (! empty_stack(stack));
  }
}




/*
 * Given a column index c_idx, computes all other column indices 
 * that depend on c_idx in the row-dependency graph.
 * - assumptions: stack is empty and is large enough.
 */
static void dfs_column_explore(triangular_matrix_t *m, int c_idx, dfs_t *stack) {
  int c, idx;
  mat_elem_t *v;

  if (unexplored(stack, c_idx)) {
    push_vector(stack, c_idx, diag_row_vector(m, c_idx));

    // Depth-first search
    do {
      c = top_counter(stack);
      v = top_vector(stack);

      // next unexplored element on row vector v
      while (c >= 0) {
	idx = v[c].idx; // column_index
	if (idx >= 0 && unexplored(stack, idx)) break;
	c --;
      }

      if (c >= 0) {
	// idx is the next column index to explore
	set_top_counter(stack, c - 1); // save counter
	push_vector(stack, idx, diag_row_vector(m, idx));
      } else {
	// topological sort: add top column index as the head of the list
	cons_list(stack, top_index(stack));
	pop_vector(stack);
      }
    } while (! empty_stack(stack));
  }
}




/*
 * Solve equation A x = a for a column vector a
 * and a triangular matrix A (square of dimension n)
 * - input: a is stored in buffer,
 *   stack must be an empty dfs structure of 
 *   size >= dimension of A (i.e. at least n)
 * - output: x is stored in buffer modulo a permutation.
 *   x[i] is stored in buffer[diag_row_idx(m, i)]
 */
void triangular_solve_column(triangular_matrix_t *m, dfs_t *stack, buffer_t *buffer) {
  int i, n, c, r_idx;

  // first pass: track dependencies from non-zero elements of a
  n = buffer->nelems;
  for (i=0; i<n; i++) {
    r_idx = buffer->active[i];
    // buffer->q[r_idx] is a non-zero element of a
    dfs_row_explore(m, r_idx, stack);
  }

  // row indices should now be in the list constructed via stack
  // in topological order.
  //    printf("\t%d\n", r_idx);
  while (! empty_list(stack)) {
    r_idx = car_list(stack);
    c = diag_column_idx(m, r_idx);
    equa_solve_step(buffer, m->m.column + c, m->col_dptr[c]);
    //    printf("\t%d\n", r_idx);
    cdr_list(stack);
  }
  //  printf("\n");
}




/*
 * Solve equation y A = b for a row vector b
 * and a triangular matrix A.
 * - input: b is stored in buffer,
 *   stack must be an empty dfs structure of size >= 
 *   dimension of A (i.e. at least n)
 * - output: y is stored in buffer modulo a permutation:
 *   y[i] is stored in buffer[diag_column_idx(m, i)]
 */
void triangular_solve_row(triangular_matrix_t *m, dfs_t *stack, buffer_t *buffer) {
  int i, n, r, c_idx;

  // first pass: track dependencies from non-zero elements of b
  n = buffer->nelems;
  for (i=0; i<n; i++) {
    c_idx = buffer->active[i];
    // buffer->q[r_idx] is a non-zero element of b
    dfs_column_explore(m, c_idx, stack);
  }

  // column indices should now be in the list constructed via stack
  // in topological order.
  //  printf("*** Row solve: column order ***\n");
  while (! empty_list(stack)) {
    c_idx = car_list(stack);
    r = diag_row_idx(m, c_idx);   
    equa_solve_step(buffer, m->m.row + r, m->row_dptr[r]);
    //    printf("\t%d\n", c_idx);
    cdr_list(stack);
  }
  //  printf("\n");
}





/****************
 *  ETA FILES   *
 ***************/

/*
 * Initialize and eta file with nvectors = size of row_index
 * ncoeffs = size of vblock.
 */
static void init_eta_file(eta_file_t *f, int nvectors, int ncoeffs) {
  f->vector_capacity = nvectors;
  f->vblock_capacity = ncoeffs;
  f->nvectors = 0;
  f->ncoeffs = 0;
  f->row_index = (int *) safe_malloc(nvectors * sizeof(int));
  f->vindex = (int *) safe_malloc((nvectors + 1) * sizeof(int));
  f->vindex[0] = 0;
  f->vblock = (vector_elem_t *) safe_malloc(ncoeffs * sizeof(vector_elem_t));
}


/*
 * Creation of an eta file with the given initial capacities
 * - nvectors: initial size of the row_index array
 *             initial size of vindex = nvectors + 1
 * - ncoeffs: initial size of the vblock
 * (Both must be positive)
 */
eta_file_t *new_eta_file(int nvectors, int ncoeffs) {  
  eta_file_t *tmp;

  tmp = (eta_file_t *) safe_malloc(sizeof(eta_file_t));
  init_eta_file(tmp, nvectors, ncoeffs);

  return tmp;
}


/*
 * Increase the number of vectors that can be stored in f
 * - n = increment = additional number of vectors
 */
static void increase_eta_file_vector_capacity(eta_file_t *f, int n) {
  n += f->vector_capacity;
  f->row_index = (int *) safe_realloc(f->row_index, n * sizeof(int));
  f->vindex = (int *) safe_realloc(f->vindex, (n + 1) * sizeof(int));
  f->vector_capacity = n;
}


/*
 * Increase the number of non-zeros that can be stored in f
 * - n = increment = additional number of pairs <index,coeff>
 */
static void increase_eta_file_coeff_capacity(eta_file_t *f, int n) {
  n += f->vblock_capacity;
  f->vblock = 
    (vector_elem_t *) safe_realloc(f->vblock, n * sizeof(vector_elem_t));
  f->vblock_capacity = n;  
}


/*
 * Cleanup
 */
static void cleanup_eta_file(eta_file_t *f) {
  safe_free(f->row_index);
  safe_free(f->vindex);
  safe_free(f->vblock);  
}

/*
 * Delete eta_file f
 */
void delete_eta_file(eta_file_t *f) {
  cleanup_eta_file(f);
  safe_free(f);
}


/*
 * Reset eta_file f: empty it
 * Release all the allocated rational numbers
 */
void reset_eta_file(eta_file_t *f) {
  int i, n, k;
  vector_elem_t *v;

  // free the rational coefficients stored in vblock
  v = f->vblock;
  n = f->ncoeffs;
  for (i=0; i<n; i++) {
    k = v[i].idx;
    rat_clear(&v[i].coeff);
  }

  // reset everything
  f->nvectors = 0;
  f->ncoeffs = 0;
  f->vindex[0] = 0;
}



/*
 * Operations for incremental construction of a new eta-matrix
 * - start_new_eta_matrix
 * - add_elem_to_eta_matrix or add_neg_elem_to_eta_matrix
 * - close_eta_matrix
 */

/*
 * Start a new eta matrix with row index = r_idx
 */
void start_new_eta_matrix(eta_file_t *f, int r_idx) {
  int nv;

  nv = f->nvectors;
  if (nv == f->vector_capacity) {
    increase_eta_file_vector_capacity(f, (nv >> 1) + 1);
  }

  f->row_index[nv] = r_idx;
}

/*
 * Add pair <i, q> to the open eta matrix.
 */
void add_elem_to_eta_matrix(eta_file_t *f, int i, rat_t *q) {
  int n;
  vector_elem_t *v;

  n = f->ncoeffs;
  if (n == f->vblock_capacity) {
    increase_eta_file_coeff_capacity(f, (n >> 1) + 1);
  }

  v = f->vblock + n;
  f->ncoeffs = n + 1;
  v->idx = i;
  rat_set(&v->coeff, q);
}

/*
 * Add pair <i, - q> to the eta-matrix.
 */
void add_neg_elem_to_eta_matrix(eta_file_t *f, int i, rat_t *q) {
  int n;
  vector_elem_t *v;

  n = f->ncoeffs;
  if (n == f->vblock_capacity) {
    increase_eta_file_coeff_capacity(f, (n >> 1) + 1);
  }

  v = f->vblock + n;
  f->ncoeffs = n + 1;
  v->idx = i;
  rat_set_neg(&v->coeff, q);
}



/*
 * Finish the current eta-matrix
 */
void close_eta_matrix(eta_file_t *f) {
  int nv;

  nv = f->nvectors;
  nv ++;
  f->vindex[nv] = f->ncoeffs;
  f->nvectors = nv;
}



/*
 * Addition of a new eta-matrix, copied from a vector
 * - r_idx = row index
 * - vector = non-zero elements on the column except diagonal
 */
void store_vector_in_eta_file(eta_file_t *f, int r_idx, vector_t *v) {
  int n, nv, i, p;
  vector_elem_t *w, *ve;

  nv = f->nvectors;
  if (nv == f->vector_capacity) {
    increase_eta_file_vector_capacity(f, (nv >> 1) + 1);
  }

  f->row_index[nv] = r_idx;

  // make room for at least p coefficients in f->vblock
  p = v->size;
  n = f->ncoeffs + p;
  if (n >= f->vblock_capacity) {
    increase_eta_file_coeff_capacity(f, (n >> 1) + 1);
  }

  // copy the elements.
  ve = v->data;
  w = f->vblock + f->ncoeffs;
  for (i=0; i<p; i++) {
    w[i].idx = ve[i].idx;
    rat_set(&w[i].coeff, &ve[i].coeff);
  }

  // update indices
  nv ++;
  f->nvectors = nv;
  f->ncoeffs = n;
  f->vindex[nv] = n;
}


/*
 * Add a new eta-matrix copied from a buffer
 * - r_idx = row index
 * - buffer = buffer that stores the non-zero column elements except the 
 *   diagonal coefficient
 * Assumes buffer is normalized.
 */
void store_buffer_in_eta_file(eta_file_t *f, int r_idx, buffer_t *buffer) {
  int n, nv, i, p, idx;
  vector_elem_t *w;

  nv = f->nvectors;
  if (nv == f->vector_capacity) {
    increase_eta_file_vector_capacity(f, (nv >> 1) + 1);
  }

  f->row_index[nv] = r_idx;  

  // make room for at least p coefficients in f->vblock
  p = buffer->nelems;
  n = f->ncoeffs + p;
  if (n >= f->vblock_capacity) {
    increase_eta_file_coeff_capacity(f, (n >> 1) + 1);
  }

  // copy the elements.
  w = f->vblock + f->ncoeffs;
  for (i=0; i<p; i++) {
    idx = buffer->active[i];
    w[i].idx = idx;
    rat_set(&w[i].coeff, buffer->q + idx);
  }

  // update indices
  nv ++;

  f->nvectors = nv;
  f->ncoeffs = n;
  f->vindex[nv] = n;  
}




/*
 * Solve equation A x = b for a matrix A stored as a row eta file
 * and a column vector b.
 *
 * Input:
 * - eta file represents the product of p elementary row matrices
 *   E_0 \times ... \times E_{p-1} = A
 * - buffer stores the column vector b.
 * Output:
 * - the (column) vector x such that A x = b is stored in buffer.
 *
 * Algorithm: x is obtained via
 *   x = A^{-1} \times b = E_{p-1}^{-1} \times ... \times E_0^{-1} \times b
 *
 * For an elementary row matrix E_i = <k, a_1,...,a_n>
 * (i.e, row k of E_i = (a_1,...,a_n), 
 *       diagonal elements are all 1, including a_k, 
 *       other elements are all 0) 
 *
 * the inverse is E_i^{-1} = <k, -a_1, ...., -a_n>
 * (i.e., negate elements of E_i that are off diagonal)
 * 
 * then x':= E_i^{-1} \times x is obtained by:
 *   x'_j := x_j if j != k
 *   x'_k := x_k - a_j x_j for j=1 to n, j !=k
 */
void eta_solve_column(eta_file_t *f, buffer_t *buffer) {
  int i, p, k, n;
  int *row_index, *vindex;
  vector_elem_t *v;

  row_index = f->row_index;
  vindex = f->vindex;
  p = f->nvectors;  

  for (i=0; i<p; i++) {
    k = row_index[i];
    v = f->vblock + vindex[i];
    n = vindex[i+1] - vindex[i];
    product_inv_eta(buffer, k, v, n);
  }
}


/*
 * Solve equation y A = b for a matrix A represented by a row eta file
 * and a row vector b.
 *
 * Input:
 * - eta file f represents the product of p elementary row matrices
 *   E_0 \times ... \times E_{p-1} = A
 * - buffer stores the row vector b.
 * Ouput:
 * - the row vector y such that y A = b is stored in buffer.
 *
 * Algorithm: y is computed via
 *   y = b \times A^{-1} = b \times E_{p-1}^{-1} ... \times E_0^{-1}
 *
 * For an elementary row matrix E_i = <k, a_1,...,a_n>, 
 *   y' = y \time E_i^{-1} is computed by
 *   y'_j = y_j - a_j y_k for j=1 to n, j!= k
 *   y'_k = y_k
 */
void eta_solve_row(eta_file_t *f, buffer_t *buffer) {
  int i, p, k, n;
  int *row_index, *vindex;
  vector_elem_t *v;

  row_index = f->row_index;
  vindex = f->vindex;
  p = f->nvectors;  

  for (i=p-1; i>=0; i--) {
    k = row_index[i];
    if (buffer->tag[k] == ACTIVE_COEFF) {
      v = f->vblock + vindex[i];   // v --> row k of E_i, except a_k 
      n = vindex[i+1] - vindex[i]; // n = number of elements in that column
      submul_vectelem_from_buffer(buffer, v, n, buffer->q + k);
    }
  }
}




/**********************
 *   BUMP STRUCTURE   *
 *********************/

/*
 * Find row index of v with the largest row_order
 */
static int max_pos_row_index(int *row_order, vector_t *v) {
  int i, n, r, max_p, max_r;
  
  n = v->size;
  max_p = -1;
  max_r = -1;
  for (i=0; i<n; i++) {
    r = v->data[i].idx;
    if (row_order[r] > max_p) {
      max_p = row_order[r];
      max_r = r;
    }
  }

  return max_r;
}


/*
 * Number of elements in given row or column vector,
 * whose position is between start and end.
 * pos = array that maps row or column indices to positions
 */
static int bump_count(mat_vector_t *v, int start, int end, int *pos) {
  int i, n, cnt, r;

  cnt = 0;
  n = v->size;
  for (i=0; i<n; i++) {
    r = v->data[i].idx;
    if (r >= 0 && start <= pos[r] && pos[r] <= end) {
      cnt ++;
    }
  }

  return cnt;
}


/*
 * Initialize bump structure: set start/end indices and positions
 * - m = triangular matrix
 * - perm = associated permutation structure. It stores a 
 *   permutation of the columns and rows of m, for which m is triangular.
 * - v = vector that replaces column c_idx in matrix m
 */
static void set_bump(bump_t *bmp, triangular_matrix_t *m, permutation_t *perm,
		     vector_t *v, int c_idx) {
  int r, c;

  // top-left corner
  r = diag_row_idx(m, c_idx);

  bmp->c_idx_start = c_idx;
  bmp->r_idx_start = r;
  bmp->pos_start = perm->col_order[c_idx];

  // bottom-right corner
  r = max_pos_row_index(perm->row_order, v);
  c = diag_column_idx(m, r);

  bmp->c_idx_end = c;
  bmp->r_idx_end = r;
  bmp->pos_end = perm->row_order[r];
}


/*
 * Check whether the bump is empty
 */
static inline int empty_bump(bump_t *bmp) {
  return bmp->pos_end < bmp->pos_start;
}



/*
 * Initialize the counts: assumes bmp is not empty.
 * - the counts are stored in piv->row_count and piv->col_count.
 * - the singleton rows and columns of the bump are stored in piv->row_partition
 *   and piv->col_partition.
 *
 * - we have to make sure the spike column (c_idx = bmp->c_idx_start)
 *   does not get removed.
 *   This can happen by accident if the element c_idx, r_idx
 *   where r_idx = diag_row[c_idx] = bmp->r_idx_start is 0.
 * - to prevent this, we set col_count[c_idx] to n and row_count[r_idx] to n
 */
static void init_bump_counts(bump_t *bmp, triangular_matrix_t *m, permutation_t *perm, pivoter_t *piv) {
  int r, c, i, n;

  clear_partition(&piv->col_partition);
  clear_partition(&piv->row_partition);

  c = bmp->c_idx_start;
  r = bmp->r_idx_start;

  // fake column/row counts for the spike
  piv->col_count[c] = m->m.nrows;
  piv->row_count[r] = m->m.ncolumns;

  // column and row counts for the other columns and rows in the bump
  // any column or row with count == 1 is stored in the singleton set
  // of piv->col_partition or piv->row_partition.
  i = bmp->pos_end - bmp->pos_start;
  while (i >= 1) {
    c = next_in_list(&perm->col_list, c);
    n = bump_count(m->m.column + c, bmp->pos_start, bmp->pos_end, perm->row_order);
    piv->col_count[c] = n;
    if (n == 1) {
      partition_add(&piv->col_partition, c, 2);
    }

    r = next_in_list(&perm->row_list, r);
    n = bump_count(m->m.row + r, bmp->pos_start, bmp->pos_end, perm->col_order);
    piv->row_count[r] = n;
    if (n == 1) {
      partition_add(&piv->row_partition, r, 2);
    }

    i --;
  }

}



/*
 * Decrement the count of every row index in column c_idx
 * - put every row whose count is set to 1 into the singleton set
 *   of piv->row_partition.
 */
static void decrement_row_count(bump_t *bmp, triangular_matrix_t *m, pivoter_t *piv, int c_idx) {
  mat_vector_t *col;
  int i, n, r, k;

  col = m->m.column + c_idx;
  n = col->size;
  for (i=0; i<n; i++) {
    r = col->data[i].idx;
    if (r >= 0) {
      k = piv->row_count[r];
      if (k > 0) { // k>0 means that r is a bump row
	k --;
	piv->row_count[r] = k;
	if (k == 1) {
	  partition_add(&piv->row_partition, r, 2);
	}
      }
    }
  }
}


/*
 * Decrement the count of every column index in row r_idx
 * - put every column whose count is one into the col_partition singleton set
 */
static void decrement_col_count(bump_t *bmp, triangular_matrix_t *m, pivoter_t *piv, int r_idx) {
  mat_vector_t *row;
  int i, n, c, k;

  row = m->m.row + r_idx;
  n = row->size;
  for (i=0; i<n; i++) {
    c = row->data[i].idx;
    if (c >= 0) {
      k = piv->col_count[c];
      if (k > 0) { // c is a column in the bump
	k --;
	piv->col_count[c] = k;
	if (k == 1) {
	  partition_add(&piv->col_partition, c, 2);
	}
      }
    }
  }
}


/*
 * Move column of bump-count = 1 out of the bump
 * - c_idx = index of the column to move
 */
static void remove_bump_column(bump_t *bmp, triangular_matrix_t *m, permutation_t *perm, 
			       pivoter_t *piv, int c_idx) {
  int r_idx;
  int row_start, col_start, pos;

  // diagonal row 
  r_idx = diag_row_idx(m, c_idx);

  // remove r_idx from the bump
  decrement_col_count(bmp, m, piv, r_idx);
  if (piv->row_count[r_idx] == 1) {
    partition_remove(&piv->row_partition, r_idx);
  }
  piv->row_count[r_idx] = 0;


  // new position of top-left corner
  pos = bmp->pos_start;
  bmp->pos_start = pos + 1;

  // shift c_idx before the first column of the bump
  // and r_idx before the first row
  col_start = bmp->c_idx_start;
  row_start = bmp->r_idx_start;

  // set position of the column/row to be removed
  perm->col_order[c_idx] = pos;
  perm->row_order[r_idx] = pos;

  if (col_start != c_idx) {
    assert(r_idx != row_start);

    // update c_idx_end/r_idx_end if necessary
    if (c_idx == bmp->c_idx_end) {
      assert(r_idx == bmp->r_idx_end);
      bmp->c_idx_end = previous_in_list(&perm->col_list, c_idx);
      bmp->r_idx_end = previous_in_list(&perm->row_list, r_idx);
    }

    circular_shift(&perm->col_list, col_start, c_idx);
    circular_shift(&perm->row_list, row_start, r_idx);

  } else {
    assert(r_idx == row_start);

    bmp->c_idx_start = next_in_list(&perm->col_list, col_start);
    bmp->r_idx_start = next_in_list(&perm->row_list, row_start);
  }

}


/*
 * Move row of bump count = 1 out of the bump
 * - r_idx = index of the row to move
 */
static void remove_bump_row(bump_t *bmp, triangular_matrix_t *m, permutation_t *perm,
			    pivoter_t *piv, int r_idx) {
  int c_idx;
  int col_end, row_end, pos;

  // diagonal column
  c_idx = diag_column_idx(m, r_idx);

  // remove column c_idx from the bump
  decrement_row_count(bmp, m, piv, c_idx);
  if (piv->col_count[c_idx] == 1) {
    partition_remove(&piv->col_partition, c_idx);
  }
  piv->col_count[c_idx] = 0;

  // new position of bottom-right corner
  pos = bmp->pos_end;
  bmp->pos_end = pos - 1;

  // shift c_idx after the last column of the bump.
  col_end = bmp->c_idx_end;
  row_end = bmp->r_idx_end;

  // removed row/columns have the following position
  perm->col_order[c_idx] = pos;
  perm->row_order[r_idx] = pos;

  if (col_end != c_idx) {
    assert(r_idx != row_end);

    // update c_idx_start/r_idx_start if necessary
    if (c_idx == bmp->c_idx_start) {
      assert(r_idx == bmp->r_idx_start);
      bmp->c_idx_start = next_in_list(&perm->col_list, c_idx);
      bmp->r_idx_start = next_in_list(&perm->row_list, r_idx);
    }

    // permutation: c_idx/r_idx moved after col_end/row_end
    reverse_circular_shift(&perm->col_list, c_idx, col_end);
    reverse_circular_shift(&perm->row_list, r_idx, row_end);

  } else {
    assert(r_idx == row_end);

    bmp->c_idx_end = previous_in_list(&perm->col_list, col_end);
    bmp->r_idx_end = previous_in_list(&perm->row_list, row_end);
  }

}



/*
 * Permutation to transform spike column into a spike row
 * - first column of bmp is moved after the last column
 * - first row of bmp is moved after the last row
 */
static void bump_permutation(bump_t *bmp, permutation_t *perm) {
  int i;

  assert(bmp->pos_start < bmp->pos_end); // circular shifts will fail otherwise

  // column permutation 
  // update bmp->c_idx_start and c_idx_end
  i = bmp->c_idx_start;
  bmp->c_idx_start = next_in_list(&perm->col_list, i);
  reverse_circular_shift(&perm->col_list, i, bmp->c_idx_end);
  bmp->c_idx_end = i;

  // same thing for rows
  i = bmp->r_idx_start;
  bmp->r_idx_start = next_in_list(&perm->row_list, i);
  reverse_circular_shift(&perm->row_list, i, bmp->r_idx_end);
  bmp->r_idx_end = i;
}



/*
 * Reset positions for rows/columns in the bump
 * Clear column and row counts in pivoter structure.
 */
static void reset_bump_positions(bump_t *bmp, permutation_t *perm, pivoter_t *piv) {
  int i, p;

  i = bmp->c_idx_start;
  p = bmp->pos_start;
  while (p <= bmp->pos_end) {
    piv->col_count[i] = 0;
    perm->col_order[i] = p;
    p ++;
    i = next_in_list(&perm->col_list, i);
  }

  i = bmp->r_idx_start;
  p = bmp->pos_start;
  while (p <= bmp->pos_end) {
    piv->row_count[i] = 0;
    perm->row_order[i] = p;
    p ++;
    i = next_in_list(&perm->row_list, i);
  }
}





/**********************
 *  LU FACTORIZATION  *
 *********************/

/*
 * Initialize fact for a simplex matrix with nrows and ncolumns
 * - nrows must be less than or equal to ncolumns
 * - nrows must also be the rank of the matrix
 * This function allocates and initializes the various fields
 * - lmatrix, umatrix, eta_file are all initially empty.
 * 
 * The diag_row/diag_col/col_dptr/row_dptr arrays for L and U are
 * initialized as follows:
 * - for L: diag_row[i] = i, diag_col[i] = i
 *   diag_row and diag_col are never modified for L so they're the same array.
 *   col_dptr and row_dptr[i] are allocated but not initialized
 * - for U: diag_row/diag_col and col_dptr/row_dptr are allocated but 
 *   not initialized.
 */
static void init_factorization(factorization_t *fact, int nrows, int ncolumns) {
  int i;
  int *tmp;

  fact->nvars = ncolumns;
  fact->dim = nrows;
  fact->var_col = (int *) safe_malloc(ncolumns * sizeof(int));

  init_triangular_matrix(&fact->lmatrix, nrows);
  init_triangular_matrix(&fact->umatrix, nrows);
  init_eta_file(&fact->f, DEFAULT_ETA_NVECTORS, DEFAULT_ETA_NCOEFFS);

  init_permutation(&fact->perm, nrows, nrows);
  init_pivoter(&fact->pv, nrows, nrows);
  init_dfs(&fact->stack, nrows);
  fact->saved_column = new_vector(nrows);

  fact->buffer = new_buffer(nrows);
  rat_init(&fact->r0);

  // diag_col/diag_row for L
  tmp = (int *) safe_malloc(nrows * sizeof(int));
  for (i=0; i<nrows; i++) {
    tmp[i] = i;
  }

  fact->lmatrix.diag_row = tmp;
  fact->lmatrix.diag_column = tmp;

  // row_dptr/col_dptr for L
  fact->lmatrix.row_dptr = (int *) safe_malloc(nrows * sizeof(int));
  fact->lmatrix.col_dptr = (int *) safe_malloc(nrows * sizeof(int));

  // diag_col/diag_row for U
  fact->umatrix.diag_row = (int *) safe_malloc(nrows * sizeof(int));
  fact->umatrix.diag_column = (int *) safe_malloc(nrows * sizeof(int));

  // row_dptr/col_dptr for U
  fact->umatrix.row_dptr = (int *) safe_malloc(nrows * sizeof(int));
  fact->umatrix.col_dptr = (int *) safe_malloc(nrows * sizeof(int));
}


/*
 * Cleanup
 */
static void cleanup_factorization(factorization_t *fact) {
  safe_free(fact->var_col);

  // need to be careful to avoid double free here!
  fact->lmatrix.diag_column = NULL;

  cleanup_triangular_matrix(&fact->lmatrix);
  cleanup_triangular_matrix(&fact->umatrix);
  cleanup_eta_file(&fact->f);

  cleanup_permutation(&fact->perm);
  cleanup_pivoter(&fact->pv);
  cleanup_dfs(&fact->stack);
  cleanup_and_delete_vector(fact->saved_column);

  delete_buffer(fact->buffer);
  rat_clear(&fact->r0);  
}


/*
 * Delete fact
 */
void delete_factorization(factorization_t *fact) {
  cleanup_factorization(fact);
  safe_free(fact);
}




/*
 * Create a factorization for the initial basis of m
 * - the basis is made of the columns of m that occur in m->col_list.
 * - the basis is already upper triangular.
 */
factorization_t *create_factorization(compact_matrix_t *m) {
  factorization_t *tmp;
  int i, n, d, c;
  int *vindex;
  vector_elem_t *v;
  mat_vector_t *aux;

  tmp = (factorization_t *) safe_malloc(sizeof(factorization_t));
  init_factorization(tmp, m->nrows, m->ncolumns);

  // set initial var_col (identical to m->col_order)
  n = m->ncolumns;
  for (i=0; i<n; i++) {
    tmp->var_col[i] = m->col_order[i];
  }

  // copy the basis columns of m into tmp->umatrix.m
  vindex = m->columns.vindex;
  n = m->nrows;
  for (i=0; i<n; i++) {
    c = m->col_list[i];
    v = m->columns.vblock + vindex[c];
    fast_store_vectelem_in_column(&tmp->umatrix.m, i, v, vindex[c + 1] - vindex[c]);
  }

  // set the diag_col/diag_row, row_dptr, col_dptr of U
  // store rows/columns in perm->col_list/perm->row_list.
  for (i=0; i<n; i++) {
    tmp->umatrix.diag_row[i] = i;
    tmp->umatrix.diag_column[i] = i;
    permutation_add(&tmp->perm, i, i);

    // sets row_dptr and col_dptr in U
    aux = tmp->umatrix.m.row + i;
    d = get_mat_vector_ptr(aux, i);
    assert(d >= 0);
    tmp->umatrix.row_dptr[i] = d;
    tmp->umatrix.col_dptr[i] = aux->data[d].ptr;
  }


  // initialize L to the identity matrix
  for (i=0; i<n; i++) {
    aux = tmp->lmatrix.m.column + i;
    assert (aux->size == 0 && aux->nelems == 0 && aux->capacity > 0);
    add_int_elem_in_column(&tmp->lmatrix.m, i, i, 1, aux);
    assert (aux->data[0].ptr == 0);
    tmp->lmatrix.row_dptr[i] = 0;
    tmp->lmatrix.col_dptr[i] = 0;
  }

  return tmp;
}



/*
 * Solve equation B x = a for a column vector a and the matrix B
 * factored as B = L \times E \times U.
 * - L and U are triangular
 * - E is an eta file.
 *
 * The computation is done in three steps:
 * - solve L y = a
 * - solve E z = y
 * - solve U x = z 
 *
 * If save_flag is non-zero, the intermediate result z is stored in
 * saved_column to be used in the next LU update.
 *
 * On input, buffer stores vector a, on output, it contains x.
 */
void factorization_solve_column(factorization_t *fact, buffer_t *buffer, int save_flag) {
  assert(empty_list(&fact->stack) && empty_stack(&fact->stack));

  // L y = a
  triangular_solve_column(&fact->lmatrix, &fact->stack, buffer);
  normalize_buffer(buffer);  

  // E z = y
  eta_solve_column(&fact->f, buffer);
  normalize_buffer(buffer);

  // make a copy of z
  if (save_flag) {
    copy_buffer_in_vector(&fact->saved_column, buffer);
  }

  // U x = z
  assert(empty_list(&fact->stack) && empty_stack(&fact->stack));
  triangular_solve_column(&fact->umatrix, &fact->stack, buffer);
  normalize_buffer(buffer);
  // Hack: use fact->buffer->q as auxiliary array
  permute_buffer(buffer, fact->umatrix.diag_column, fact->buffer->q);
}


/*
 * Solve equation x B = a for a row vector a and the matrix B
 * factored as B = L \times E \times U.
 * - L and U are triangular
 * - E is an eta file.
 *
 * The computation is done in three steps:
 * - solve y U = a
 * - solve z E = y
 * - solve x L = z 
 *
 * On input, buffer stores vector a, on output, it contains x.
 */
void factorization_solve_row(factorization_t *fact, buffer_t *buffer) {
  assert(empty_list(&fact->stack) && empty_stack(&fact->stack));

  // y U = a
  triangular_solve_row(&fact->umatrix, &fact->stack, buffer);
  normalize_buffer(buffer);
  // Same hack as above: this is OK since fact->buffer is not in use
  permute_buffer(buffer, fact->umatrix.diag_row, fact->buffer->q);

  // z E = y
  eta_solve_row(&fact->f, buffer);
  normalize_buffer(buffer);
  assert(empty_list(&fact->stack) && empty_stack(&fact->stack));

  // x L = z
  triangular_solve_row(&fact->lmatrix, &fact->stack, buffer);
  normalize_buffer(buffer);
}





/*****************************
 *  LU FACTORIZATION PROPER  *
 ****************************/

/*
 * One step of LU factorization: singleton column
 * - c_idx = column index of fact->umatrix
 */
static void lu_fact_singleton_column(factorization_t *fact, int c_idx) {
  int i, r_idx;
  triangular_matrix_t *m;
  mat_vector_t *column;

  m = &fact->umatrix;

  // find the row index
  column = m->m.column + c_idx;
  i = 0;
  for (;;) {
    r_idx = column->data[i].idx;
    if (r_idx >= 0) break;
    i ++;
  }

#ifdef DEBUG
  printf("LU fact: column %d, row %d (singleton column)\n", c_idx, r_idx);
#endif

  // set diagonal pointers for row r_idx of U and detach row r_idx
  m->row_dptr[r_idx] = column->data[i].ptr;
  detach_row(&m->m, &fact->pv, r_idx);

  // column r_idx of L: L[r_idx, r_idx] = 1, rest is 0
  m = &fact->lmatrix;
  column = m->m.column + r_idx;
  assert (column->size == 0 && column->nelems == 0 && column->capacity > 0);
  add_int_elem_in_column(&m->m, r_idx, r_idx, 1, column);
  m->col_dptr[r_idx] = 0;
  m->row_dptr[r_idx] = column->data[0].ptr;

  // add r_idx/c_idx at the end of current permutation
  // update pivoter
  permutation_add(&fact->perm, r_idx, c_idx);
  end_elim_step(&fact->pv, r_idx, c_idx);
  fact->umatrix.diag_row[c_idx] = r_idx;
  fact->umatrix.diag_column[r_idx] = c_idx;
}


/*
 * One step of LU factorization: singleton row
 * - r_idx = index of the singleton row in U
 * - r_ptr = pointer to the unique non-zero element in that row
 */
static void lu_fact_singleton_row(factorization_t *fact, int r_idx, int r_ptr) {
  triangular_matrix_t *u, *l;
  mat_vector_t *ucolumn, *urow, *lcolumn;
  mat_elem_t *ce;
  int c_idx, i, n, r;
  rat_t *pv_coeff;

  
  u = &fact->umatrix;
  l = &fact->lmatrix;

  urow = u->m.row + r_idx;
  c_idx = urow->data[r_ptr].idx;
  ucolumn = u->m.column + c_idx;

#ifdef DEBUG
  printf("LU fact: column %d, row %d (singleton row)\n", c_idx, r_idx);
#endif

  u->row_dptr[r_idx] = r_ptr; // diagonal pointer for row[r_idx] = r_ptr  

  // make room in column of L for n elements, where
  // n = number of non-zero elements in column c_idx of U
  lcolumn = l->m.column + r_idx;
  adjust_mat_vector_capacity(lcolumn, ucolumn->nelems);

  // set L[r_idx,r_idx] = 1 and record dptr for L
  assert (lcolumn->size == 0 && lcolumn->nelems == 0 && lcolumn->capacity > 0);
  add_int_elem_in_column(&l->m, r_idx, r_idx, 1, lcolumn);
  l->col_dptr[r_idx] = 0;
  l->row_dptr[r_idx] = lcolumn->data[0].ptr;

  // pivot coefficient = U[r_idx, c_idx]
  pv_coeff = &urow->data[r_ptr].coeff;

  // clear coefficients in column c_idx of U (except the one at row r_idx)
  // record corresponding factors in column r_idx of L
  n = ucolumn->size;
  ce = ucolumn->data;
  for (i=0; i<n; i++) {
    r = ce[i].idx;
    if (r >= 0 && r != r_idx) {
      // ce[i] stores U[r, c_idx]
      // set L[r, r_idx] to U[r, c_idx]/U[r_idx, c_idx]
      add_fraction_in_column(&l->m, r_idx, r, &ce[i].coeff, pv_coeff, lcolumn);

      // set U[r, c_idx] to zero
      rat_clear(&ce[i].coeff);
      free_mat_elem(u->m.row + r, ce[i].ptr);
      
      // update the row partition (move r)
      partition_move(&fact->pv.row_partition, r, partition_index(u->m.row[r].nelems));
    }
  }

  // empty column c_idx of U
  // row r_idx is detached so U[r_idx, c_idx] is not lost.
  ucolumn->size = 0;
  ucolumn->nelems = 0;
  ucolumn->free = -1;  

  // add r_idx/c_idx at the end of the permutation
  permutation_add(&fact->perm, r_idx, c_idx);
  end_elim_step(&fact->pv, r_idx, c_idx);
  fact->umatrix.diag_row[c_idx] = r_idx;
  fact->umatrix.diag_column[r_idx] = c_idx;
}


/*
 * One step of LU factorization: general case
 * - r_idx/c_idx = the pivot
 * - c_ptr = index of element of index r_idx in column c_idx of U
 * - r_ptr = index of element of index c_idx in row r_idx of U
 */
static void lu_fact(factorization_t *fact, int c_idx, int r_idx, int c_ptr, int r_ptr) {
  triangular_matrix_t *u, *l;
  mat_vector_t *ucolumn, *lcolumn;
  mat_vector_t *row, *pivot_row;
  mat_elem_t *ce;
  int i, n, r;
  rat_t *pv_coeff, *factor;

  factor = &fact->r0;
  u = &fact->umatrix;
  l = &fact->lmatrix;

  // get pivot coefficient
  ucolumn = u->m.column + c_idx;
  pv_coeff = &ucolumn->data[c_ptr].coeff;
  pivot_row = u->m.row + r_idx;

#ifdef DEBUG
  printf("LU fact: column %d, row %d (row size = %d, col size = %d)\n", c_idx, r_idx,
	 u->m.row[r_idx].nelems, u->m.column[c_idx].nelems);

  if (rat_is_zero(pv_coeff)) {
    printf("**** BUG: zero pivot ****\n");
    fflush(stdout);
  }
#endif

  u->row_dptr[r_idx] = r_ptr; // diagonal pointer for row[r_idx] = r_ptr  

  // reserve room in column r_idx of L
  lcolumn = l->m.column + r_idx;
  adjust_mat_vector_capacity(lcolumn, ucolumn->nelems);

  // set L[r_idx,r_idx] = 1 and record dptr
  assert (lcolumn->size == 0 && lcolumn->nelems == 0 && lcolumn->capacity > 0);
  add_int_elem_in_column(&l->m, r_idx, r_idx, 1, lcolumn);
  l->col_dptr[r_idx] = 0;
  l->row_dptr[r_idx] = lcolumn->data[0].ptr;


  // elimination loop
  n = ucolumn->size;
  ce = ucolumn->data;

  for (i=0; i<n; i++) {
    r = ce[i].idx;
    if (r >= 0 && r != r_idx) {
      row = u->m.row + r; // row r of U

      // factor = U[r, c_idx]/U[r_idx, c_idx]
      rat_set(factor, &ce[i].coeff);
      rat_div(factor, pv_coeff);
      // L[r, r_idx] := factor
      add_rat_elem_in_column(&l->m, r_idx, r, factor, lcolumn);

      // eliminate c_idx coefficient from row r
      copy_mat_vector_in_buffer(fact->buffer, row);
      submul_mat_vector_from_buffer(fact->buffer, pivot_row, factor);
      replace_row(&u->m, &fact->pv, r, fact->buffer);

      // gmp number may have been assigned to factor
      rat_clear(factor);
    }
  }

  // detach pivot row/update pivoter and permutation
  detach_row(&u->m, &fact->pv, r_idx);
  permutation_add(&fact->perm, r_idx, c_idx);
  end_elim_step(&fact->pv, r_idx, c_idx);
  fact->umatrix.diag_row[c_idx] = r_idx;
  fact->umatrix.diag_column[r_idx] = c_idx;
}


/*
 * Reconstruct the columns of U after LU factorization.
 * The row data is valid for U (except the ptr fields)
 * All the columns of U are empty.
 */
static void rebuild_umatrix_columns(triangular_matrix_t *u) {
  int i, n, j, k, c, p;
  mat_vector_t *row;
  mat_vector_t *column;

  n = u->m.ncolumns;
  column = u->m.column;
  for (i=0; i<n; i++) {
    assert(column->nelems == 0);
    column->size = 0;
    column->free = -1;
    column ++;
  }

  n = u->m.nrows;
  row = u->m.row;
  for (i=0; i<n; i++) {
    k = row->size;
    for (j=0; j<k; j++) {
      c = row->data[j].idx;
      if (c >= 0) {
	column = u->m.column + c;
	p = alloc_mat_elem(column);
	column->data[p].idx = i;
	column->data[p].ptr = j;
	column->data[p].coeff = row->data[j].coeff;
	row->data[j].ptr = p;
      }
    }
    row ++;
  }

  for (i=0; i<n; i++) {
    p = u->row_dptr[i];
    c = u->m.row[i].data[p].idx;
    k = u->m.row[i].data[p].ptr;
    u->col_dptr[c] = k;
  }
  
}


/*
 * Internal LU factorization procedure:
 * - construct the basis matrix B based on fact->var_col:
 *   if var_col[c] = i and i >=0 then column i of B is column c of m
 * - then compute the LU factorization of B
 * The eta file is emptied.
 * Return code:
 * - -1 if matrix B is singular
 * - 0 otherwise.
 */
static int lufact(factorization_t *fact, compact_matrix_t *m) {
  int i, n, c, cp, r, rp;
  int *vindex;
  vector_elem_t *v;

  // reset current factorization
  clear_matrix(&fact->lmatrix.m);
  clear_matrix(&fact->umatrix.m);
  reset_eta_file(&fact->f);

  // store columns in umatrix
  n = fact->nvars;
  vindex = m->columns.vindex;
  for (c=0; c<n; c++) {
    i = fact->var_col[c];
    if (i >= 0) {
      v = m->columns.vblock + vindex[c];
      fast_store_vectelem_in_column(&fact->umatrix.m, i, v, vindex[c+1] - vindex[c]);
    }
  }

  // prepare for LU factorization
  n = m->nrows;
  reset_permutation(&fact->perm, n, n);
  prepare_elimination(&fact->pv, &fact->umatrix.m);

#if DEBUG
  printf("\nLU fact: BASE MATRIX\n");
  print_matrix_poly(stdout, &fact->umatrix.m);
  printf("\n\n");
  fflush(stdout);
#endif

 loop:
  //  printf("\n---- UMATRIX ----\n");
  //  print_matrix_poly(stdout, &fact->umatrix.m);
  //  print_pivoter(&fact->pv, fact->dim, fact->dim);
  //  fflush(stdout);


  // try singleton columns
  c = partition_get_first(&fact->pv.col_partition, 2);
  if (c >= 0) {
    lu_fact_singleton_column(fact, c);
    goto loop;
  }

  // singleton rows
  r = partition_get_first(&fact->pv.row_partition, 2);
  if (r >= 0) {
    rp = best_column_in_row(&fact->pv, fact->umatrix.m.row + r);
    assert (rp >= 0);
    lu_fact_singleton_row(fact, r, rp);
    goto loop;
  }

  // general case
  if (pivot_selection(&fact->umatrix.m, &fact->pv, &r, &rp, &c, &cp)) {
    lu_fact(fact, c, r, cp, rp);
    goto loop;
  }

  //  printf("\n---- UMATRIX ----\n");
  //  print_matrix_poly(stdout, &fact->umatrix.m);
  //  print_matrix_details(stdout, &fact->umatrix.m);

  // re-attach all the rows of U
  rebuild_umatrix_columns(&fact->umatrix);


  // check non-singularity
  if (fact->perm.size != fact->dim) {
    printf("\n*** ERROR IN LU-FACT: SINGULAR MATRIX ***");
    printf("\n*** Rank = %d, dimension = %d ***\n\n", fact->perm.size, fact->dim);
    return -1;
  }

  return 0;
}



/*
 * Compute an LU factorization of a matrix B formed by a subset of columns of m.
 * - col = array containing the column indices (must have the same
 *   size as the dimension of L or U = fact->dim)
 * - m = matrix whose columns form B.
 * - L and U are stored in fact.
 * - the eta file is emptied.
 * Return code:
 * - -1 if matrix B is singular
 * - 0 otherwise.
 */
int compute_factorization(factorization_t *fact, compact_matrix_t *m, int *col) {
  int i, n, c;

  assert (m->ncolumns == fact->nvars && m->nrows == fact->dim);

  // set var_col
  n = m->ncolumns;
  for (i=0; i<n; i++) {
    fact->var_col[i] = -1;
  }
  n = m->nrows;
  for (i=0; i<n; i++) {
    c = col[i];
    fact->var_col[c] = i;
  }

  return lufact(fact, m);
}



/*
 * Update current basis and compute LU factorization:
 * - old_var: variable that leaves the basis
 * - new_var: variable that enters the basis
 *
 * Returns -1 if the factorization fails (new basis is a singular matrix)
 * Returns 0 otherwise.
 */
int update_and_refactor(factorization_t *fact, compact_matrix_t *m, int old_var, int new_var) {
  int c;

  assert (m->ncolumns == fact->nvars && m->nrows == fact->dim && fact->var_col[old_var] >= 0);

  // update var_col 
  c = fact->var_col[old_var];
  fact->var_col[new_var] = c;
  fact->var_col[old_var] = -1;

  return lufact(fact, m);
}



/**************************
 *  FACTORIZATION UPDATE  * 
 *************************/

#if DEBUG

static void print_permutation(permutation_t *perm) {
  list_t *list;
  int i;

  printf("\nColumn order:");
  list = &perm->col_list;
  i = first_of_list(list);
  while (i >= 0) {
    printf(" %d", i);
    i = next_in_list(list, i);
  }

  printf("\nRow order:   ");
  list = &perm->row_list;
  i = first_of_list(list);
  while (i >= 0) {
    printf(" %d", i);
    i = next_in_list(list, i);
  }

  printf("\n\n");
}


static void print_bump(bump_t *bmp, permutation_t *perm, pivoter_t *piv) {
  list_t *list;
  int i, n;

  printf("Start position: %d\n", bmp->pos_start);
  printf("End position: %d\n", bmp->pos_end);

  if (bmp->pos_start <= bmp->pos_end) {
    printf("Columns:");
    list = &perm->col_list;
    i = bmp->c_idx_start;
    for (;;) {
      printf(" %d", i);
      if (i == bmp->c_idx_end) break;
      i = next_in_list(list, i);
    }
    
    printf("\nRows:");
    list = &perm->row_list;
    i = bmp->r_idx_start;
    for (;;) {
      printf(" %d", i);
      if (i == bmp->r_idx_end) break;
      i = next_in_list(list, i);
    }

  } else {
    printf("Empty");
  }

  n = perm->size;

  printf("\nColumn counts: ");
  for (i=0; i<n; i++) {
    printf("%d ", piv->col_count[i]);
  }

  printf("\nRow counts:    ");
  for (i=0; i<n; i++) {
    printf("%d ", piv->row_count[i]);
  }

  printf("\nColumn positions: ");
  for (i=0; i<n; i++) {
    printf("(%d, %d) ", i, perm->col_order[i]);
  }

  printf("\nRow positions: ");
  for (i=0; i<n; i++) {
    printf("(%d, %d) ", i, perm->row_order[i]);
  }

  printf("\n\n");
  fflush(stdout);
}

#endif

/*
 * LU-update: shrink the bump by permutation of rows/columns of U
 * - u = triangular matrix U
 * - bmp = bump structure
 * - perm = current permutation of rows/columns of U
 * - piv = auxiliary pivoter used for detecting singleton rows
 *        and singleton columns in the bump
 */
static void shrink_bump(bump_t *bmp, triangular_matrix_t *u, permutation_t *perm, pivoter_t *piv) {
  int c, r;

  // compute the bump counts  
  init_bump_counts(bmp, u, perm, piv);

#if DEBUG  
  printf("--- Bump ---\n");
  print_bump(bmp, perm, piv);
#endif
  
  c = partition_get_first(&piv->col_partition, 2);
  while (c >= 0) {
    remove_bump_column(bmp, u, perm, piv, c);

#if DEBUG
    printf("--- After removing column %d ---\n", c);
    print_bump(bmp, perm, piv);
#endif

    partition_remove(&piv->col_partition, c);
    c = partition_get_first(&piv->col_partition, 2);
  }

  r = partition_get_first(&piv->row_partition, 2);
  while (r >= 0) {
    remove_bump_row(bmp, u, perm, piv, r);

#if DEBUG
    printf("--- After removing row %d ---\n", r);
    print_bump(bmp, perm, piv);
#endif

    partition_remove(&piv->row_partition, r);
    r = partition_get_first(&piv->row_partition, 2);
  }

#if DEBUG
  printf("--- End of shrink bump ---\n");
  print_bump(bmp, perm, piv);
#endif
}



/*
 * Eliminate the spike row (i.e., last row of bump).
 * - fact->bmp stores the bump submatrix
 * - must be called only if the bump is non-empty.
 * Returns -1 if the matrix is singular, 0 otherwise.
 */
static int eliminate_spike_row(factorization_t *fact) {
  buffer_t *buffer;
  triangular_matrix_t *u;
  mat_vector_t *row;
  int r, r_idx, c_idx, p;
  rat_t *factor;
  list_t *list;

  u = &fact->umatrix;
  buffer = fact->buffer;
  factor = &fact->r0;

  // copy spike row in buffer
  r_idx = fact->bmp.r_idx_end; // index of spike row 
  row = u->m.row + r_idx;

  assert(buffer->nelems == 0);
  copy_mat_vector_in_buffer(buffer, row); 

  // start eta-matrix
  start_new_eta_matrix(&fact->f, r_idx);

  // scan bump rows and eliminate
  list = &fact->perm.row_list;
  r = fact->bmp.r_idx_start;
  do {
    row = u->m.row + r;
    c_idx = diag_column_idx(u, r);
    if (buffer->tag[c_idx] == ACTIVE_COEFF && rat_is_nonzero(buffer->q + c_idx)) {
      // subtract q[c_idx]/u[r, c_idx] * row[r] from buffer
      rat_set(factor, buffer->q + c_idx);
      p = u->row_dptr[r];
      rat_div(factor, &row->data[p].coeff);
      submul_mat_vector_from_buffer(buffer, row, factor);

      // record factor in eta matrix
      add_elem_to_eta_matrix(&fact->f, r, factor);

      // free gmp number if one is assigned to factor
      rat_clear(factor);
    }
    
    r = next_in_list(list, r);
  } while (r != r_idx);

  close_eta_matrix(&fact->f);

  // copy buffer into spike row.
  normalize_buffer(buffer);
  row = u->m.row + r_idx;
  clear_row(&u->m, r_idx, row);
  adjust_mat_vector_capacity(row, buffer->nelems);
  copy_buffer_in_row(&u->m, buffer, r_idx, row);

  // cleanup buffer
  clear_buffer(buffer);
  
  // set col_dptr and row_dptr for matrix U
  c_idx = diag_column_idx(u, r_idx);
  p = get_mat_vector_ptr(row, c_idx);
  if (p < 0) {
    printf("\n*** ERROR IN LU-UPDATE: SINGULAR MATRIX ***");
    printf("\n*** Detected in eliminate_spike_row ***\n");
    return -1;
  }
  u->row_dptr[r_idx] = p;
  u->col_dptr[c_idx] = row->data[p].ptr;

  return 0;
}


/*
 * For special case where bump reduces to a 1 by 1 matrix:
 * - set the row_dptr and col_dptr for the new column
 * - u = matrix U, c_idx = column of U where new column was added.
 */
static void restore_diag_pointers(triangular_matrix_t *u, int c_idx) {
  int r_idx, p;
  mat_vector_t *column;

  column = u->m.column + c_idx;
  r_idx = diag_row_idx(u, c_idx);
  p = get_mat_vector_ptr(column, r_idx);
  assert (p >= 0);
  u->col_dptr[c_idx] = p;
  u->row_dptr[r_idx] = column->data[p].ptr;
}


/*
 * Update the current factorization:
 * - replace a column of U by the vector in fact->saved_column:
 *   old_var: variable that leaves the basis
 *   new_var: variable that enters the basis
 *   (i.e. column i of U is replaced by saved_column 
 *    where i = fact->var_col[old_var])
 * - let V be the result, then the function computes an elementary
 *   row matrix E_p and an upper-triangular matrix U' such that 
 *   V = E_p \times U'.
 * - U' is stored as the new fact->umatrix
 * - E_p is added as last matrix in the eta file.
 * Returns -1 if the factorization fails (singular matrix).
 * Returns 0 otherwise.
 */
int update_factorization(factorization_t *fact, int old_var, int new_var) {
  int c_idx;
  vector_t *new_column;
  bump_t *bmp;

  c_idx = fact->var_col[old_var];
  fact->var_col[new_var] = c_idx;
  fact->var_col[old_var] = -1;

  new_column = fact->saved_column;
  bmp = &fact->bmp;

#if DEBUG
  printf("\n--- Saved column ---\n");
  print_vector(stdout, new_column, "u");
  printf("\n");
  print_permutation(&fact->perm);
#endif
  
  // initialize the "bump" submatrix
  set_bump(bmp, &fact->umatrix, &fact->perm, new_column, c_idx);

#if DEBUG
  printf("\n--- INITIAL BUMP ---\n");
  print_bump(bmp, &fact->perm, &fact->pv);
#endif

  if (empty_bump(bmp)) {
    printf("\n*** ERROR IN LU-UPDATE: SINGULAR MATRIX ***");
    printf("\n*** old var: %d, new var: %d ***\n\n", old_var, new_var);
    return -1;
  }


  // copy saved_column into column c_idx of U
  fast_store_vectelem_in_column(&fact->umatrix.m, c_idx,
				new_column->data, new_column->size);

  // shrink the bump
  shrink_bump(bmp, &fact->umatrix, &fact->perm, &fact->pv);

  // elimination loop if the bump is not reduced to a 1 x 1 submatrix
  if (bmp->pos_start < bmp->pos_end) {
    // apply permutation to turn spike column into spike row
    bump_permutation(bmp, &fact->perm);

#if DEBUG
    printf("--- After permutation ---\n");
    print_bump(bmp, &fact->perm, &fact->pv);
    print_permutation(&fact->perm);
#endif

    if (eliminate_spike_row(fact) < 0) {
      return -1;
    }

  } else {
    assert(bmp->pos_start == bmp->pos_end);

    printf("--- Reduced bump ---\n");
#if DEBUG
    print_permutation(&fact->perm);
#endif

    restore_diag_pointers(&fact->umatrix, c_idx);
  }
   
  reset_bump_positions(bmp, &fact->perm, &fact->pv);

#if DEBUG
  printf("--- After resetting positions ---\n");
  print_bump(bmp, &fact->perm, &fact->pv);
#endif

  return 0;
}
