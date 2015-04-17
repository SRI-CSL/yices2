/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * MATRIX REPRESENTATION FOR LINEAR ARITHMETIC SOLVER
 */

/*
 * A matrix is represented as an array of rows
 * - row i is a sparse representation of (a_i1, ..., a_in)
 *   (where only the non-zero elements are stored)
 * - for each column j, we keep track of all the rows where
 *   a_ij is non-zero in a column vector
 *
 * Equivalently, each row can be seen as a linear equation
 *   a_i1 x_1 + ... + a_in x_n == 0
 * where x_1, ... , x_n are n variables corresponding to the columns.
 *
 * Each row is an array of triples (col_idx, c_ptr, a)
 * - if col_idx < 0, the triple is not used. A list of free elements
 *   is maintained, links are stored in the c_ptr field.
 * - if col_idx >= 0, then it's the index k of a variable x_k
 *   the triple represents a * x_k and and c_ptr is an index in the array
 *   column[k]
 *
 * Each column is an array of pairs (row_idx, r_ptr)
 * - if row_idx < 0, the pair is not used. It's stored in a free list
 *   with links stored in r_ptr
 * - if row_idx >= 0, then it's the index of a row i and r_ptr is
 *   an index in the array row[i]
 *
 * For a non-zero element a_ij in row i, column j, there are two
 * indices i_ptr and j_ptr such that
 * - row[i][i_ptr] = (j, j_ptr, a_ij)
 * - col[j][j_ptr] = (i, i_ptr)
 */

#include <assert.h>
#include <stdbool.h>

#include "solvers/simplex/matrices.h"
#include "utils/memalloc.h"




/**************************
 *  MATRIX CONSTRUCTION   *
 *************************/

/*
 * COLUMN VECTORS
 */

/*
 * Allocate and initialize a column vector of capacity n
 */
static column_t *new_column(uint32_t n) {
  column_t *v;

  if (n >= MAX_MATRIX_COL_SIZE) {
    out_of_memory();
  }
  v = (column_t *) safe_malloc(sizeof(column_t) + n * sizeof(col_elem_t));
  v->capacity = n;
  v->size = 0;
  v->nelems = 0;
  v->free = -1;

  return v;
}


/*
 * Return a column equal to v but 50% larger
 */
static column_t *extend_column(column_t *v) {
  uint32_t n;

  n = v->capacity + 1;
  n += n>>1;
  if (n >= MAX_MATRIX_COL_SIZE) {
    out_of_memory();
  }
  v = (column_t *) safe_realloc(v, sizeof(column_t) + n * sizeof(col_elem_t));
  v->capacity = n;

  return v;
}


/*
 * Allocate an element in vector *v
 * - if *v is null, allocate a fresh vector of default size
 * - if *v is full, reallocate a larger vector
 * If any allocation or reallocation happens, *v is updated.
 * - return the index of the element in v->data
 */
static uint32_t alloc_column_elem(column_t **v) {
  column_t *c;
  int32_t i;

  c = *v;
  if (c == NULL) {
    c = new_column(DEF_MATRIX_COL_SIZE);
    c->size = 1;
    *v = c;
    i = 0;
  } else {
    // try the free list
    i = c->free;
    if (i >= 0) {
      c->free = c->data[i].r_ptr;
    } else {
      i = c->size;
      if (i == c->capacity) {
        c = extend_column(c);
        *v = c;
      }
      assert(i < c->capacity);
      c->size ++;
    }
  }
  c->nelems ++;
  return i;
}


/*
 * Check whether column element i is valid (not in the free list)
 */
#ifndef NDEBUG
static inline bool good_column_elem(column_t *v, int32_t i) {
  assert(0 <= i && i < v->size);
  return v->data[i].r_idx >= 0;
}
#endif

/*
 * Free element of index i in column v
 */
static void free_column_elem(column_t *v, int32_t i) {
  assert(good_column_elem(v, i));
  v->data[i].r_idx = -1; // mark it as dead
  v->data[i].r_ptr = v->free;
  v->free = i;
  v->nelems --;
}


/*
 * Delete column v
 */
static inline void delete_column(column_t *v) {
  safe_free(v);
}





/*
 * ROW VECTORS
 */

/*
 * Allocate and initialize a row of capacity n
 */
static row_t *new_row(uint32_t n) {
  row_t *v;

  if (n >= MAX_MATRIX_ROW_SIZE) {
    out_of_memory();
  }
  v = (row_t *) safe_malloc(sizeof(row_t) + n * sizeof(row_elem_t));
  v->capacity = n;
  v->size = 0;
  v->nelems = 0;
  v->free = -1;

  return v;
}



/*
 * Return a colum equal to v but 50% larger
 */
static row_t *extend_row(row_t *v) {
  uint32_t n;

  n = v->capacity + 1;
  n += n>>1;
  if (n >= MAX_MATRIX_ROW_SIZE) {
    out_of_memory();
  }
  v = (row_t *) safe_realloc(v, sizeof(row_t) + n * sizeof(row_elem_t));
  v->capacity = n;

  return v;
}


/*
 * Allocate a row element in vector *v
 * - if *v is null, allocate a fresh vector of default size
 * - if *v is full, reallocate a larger vector
 * If any allocation or reallocation happens, *v is updated.
 * - return the index of the element in v->data
 * - initialize v->data[i].coeff if required
 */
static uint32_t alloc_row_elem(row_t **v) {
  row_t *r;
  int32_t i;

  r = *v;
  if (r == NULL) {
    r = new_row(DEF_MATRIX_ROW_SIZE);
    *v = r;
    i = 0;
  } else {
    // try the free list
    i = r->free;
    if (i >= 0) {
      r->free = r->data[i].c_ptr;
    } else {
      i = r->size;
      if (i == r->capacity) {
        r = extend_row(r);
        *v = r;
      }
      assert(i < r->capacity);
      // initialize the rational coefficient
      q_init(&r->data[i].coeff);
      r->size ++;
    }
  }
  r->nelems ++;
  return i;
}


/*
 * Check whether row element i is valid (not in the free list)
 */
#ifndef NDEBUG
static inline bool good_row_elem(row_t *v, int32_t i) {
  assert(0 <= i && i < v->size);
  return v->data[i].c_idx >= 0;
}
#endif

/*
 * Free element of index i in row v
 */
static void free_row_elem(row_t *v, int32_t i) {
  assert(good_row_elem(v, i));
  v->data[i].c_idx = -1; // mark it as dead
  v->data[i].c_ptr = v->free;
  v->free = i;
  v->nelems --;
}


/*
 * Delete row v
 */
static void delete_row(row_t *v) {
  uint32_t i, n;
  n = v->size;
  for (i=0; i<n; i++) {
    q_clear(&v->data[i].coeff);
  }
  safe_free(v);
}







/*
 * MATRIX
 */

/*
 * Initialize matrix:
 * - n = initial row capacity, m = initial column capacity
 * - if n == 0 then the default row capacity is used
 * - if m == 0 then the default column capacity is used
 */
void init_matrix(matrix_t *matrix, uint32_t n, uint32_t m) {
  if (n == 0) n = DEF_MATRIX_NUM_ROWS;
  if (m == 0) m = DEF_MATRIX_NUM_COLUMNS;

  if (n >= MAX_MATRIX_NUM_ROWS || m >= MAX_MATRIX_NUM_COLUMNS) {
    out_of_memory();
  }

  matrix->nrows = 0;
  matrix->ncolumns = 0;
  matrix->row_cap = n;
  matrix->column_cap = m;
  matrix->row = (row_t **) safe_malloc(n * sizeof(row_t *));
  matrix->base_var = (int32_t *) safe_malloc(n * sizeof(int32_t));

  matrix->column = (column_t **) safe_malloc(m * sizeof(column_t *));
  matrix->base_row = (int32_t *) safe_malloc(m * sizeof(int32_t));
  matrix->index = (int32_t *) safe_malloc(m * sizeof(int32_t));

  q_init(&matrix->factor);

  // marks: one bit per row
  matrix->marks = allocate_bitvector(n);

  // constant is not allocated here
  matrix->constant = NULL;
}


/*
 * Delete matrix: free all memory it uses
 */
void delete_matrix(matrix_t *matrix) {
  uint32_t i, n;

  n = matrix->nrows;
  for (i=0; i<n; i++) {
    delete_row(matrix->row[i]);
  }

  n = matrix->ncolumns;
  for (i=0; i<n; i++) {
    delete_column(matrix->column[i]);
  }

  safe_free(matrix->row);
  safe_free(matrix->column);
  safe_free(matrix->index);
  safe_free(matrix->constant);
  safe_free(matrix->base_var);
  safe_free(matrix->base_row);
  delete_bitvector(matrix->marks);

  q_clear(&matrix->factor);

  matrix->row = NULL;
  matrix->column = NULL;
  matrix->index = NULL;
  matrix->constant = NULL;
  matrix->base_var = NULL;
  matrix->base_row = NULL;
  matrix->marks = NULL;
}


/*
 * Reset matrix to the empty matrix
 * - delete all rows and columns
 */
void reset_matrix(matrix_t *matrix) {
  uint32_t i, n;

  n = matrix->nrows;
  for (i=0; i<n; i++) {
    delete_row(matrix->row[i]);
    matrix->row[i] = NULL;  // this is redundant but it helps debugging
  }

  n = matrix->ncolumns;
  for (i=0; i<n; i++) {
    delete_column(matrix->column[i]);
    matrix->column[i] = NULL;
  }

  q_clear(&matrix->factor);

  matrix->nrows = 0;
  matrix->ncolumns = 0;
}






/*
 * UTILITIES
 */

/*
 * Get the index of a new column element for column j
 */
static inline uint32_t get_column_elem(matrix_t *matrix, uint32_t j) {
  assert(j < matrix->ncolumns);
  return alloc_column_elem(matrix->column + j);
}

/*
 * Pointer to column element k in column j
 */
static inline col_elem_t *column_elem(matrix_t *matrix, uint32_t j, uint32_t k) {
  assert(j < matrix->ncolumns && matrix->column[j] != NULL && k < matrix->column[j]->size);
  return matrix->column[j]->data + k;
}


/*
#if 0
// NOT USED
#endif

 * Pointer to column element k in row i
 */
static inline row_elem_t *row_elem(matrix_t *matrix, uint32_t i, uint32_t k) {
  assert(i < matrix->nrows &&  matrix->row[i] != NULL && k < matrix->row[i]->size);
  return matrix->row[i]->data + k;
}



/*
 * Add a column element in column j, and set it to <r_idx, r_ptr>
 * - return the index of the element in column j
 */
static uint32_t add_column_elem(matrix_t *matrix, uint32_t j, uint32_t r_idx, uint32_t r_ptr) {
  uint32_t k;
  col_elem_t *e;

  k = get_column_elem(matrix, j);
  e = column_elem(matrix, j, k);
  e->r_idx = r_idx;
  e->r_ptr = r_ptr;

  return k;
}


#if 0
// Not used
/*
 * Add a row element in row i, and set it to <c_idx, c_ptr, coeff>
 * - return the element index in row i
 */
static uint32_t add_row_elem(matrix_t *matrix, uint32_t i, uint32_t c_idx, uint32_t c_ptr,
                             rational_t *coeff) {
  uint32_t k;
  row_elem_t *e;

  k = get_row_elem(matrix, i);
  e = row_elem(matrix, i, k);
  e->c_idx = c_idx;
  e->c_ptr = c_ptr;
  q_set(&e->coeff, coeff);

  return k;
}

#endif

/*
 * Remove element k in row i (when its coefficient is zero)
 * and update the corresponding column vector
 */
static void remove_row_elem(matrix_t *matrix, uint32_t i, uint32_t k) {
  row_elem_t *e;

  e = row_elem(matrix, i, k);
  free_column_elem(matrix->column[e->c_idx], e->c_ptr);
  free_row_elem(matrix->row[i], k);
}


#if 0
// Not used
/*
 * Create a new a[i, j] for row i and column j with value = a
 * - this adds a new element in row i and in column j, so there
 *   mustn't be one already
 * - return the row index of the new element
 */
static uint32_t add_matrix_elem(matrix_t *matrix, uint32_t i, uint32_t j, rational_t *a) {
  uint32_t c_ptr, r_ptr;
  col_elem_t *ce;
  row_elem_t *re;

  c_ptr = get_column_elem(matrix, j);
  r_ptr = get_row_elem(matrix, i);
  ce = column_elem(matrix, j, c_ptr);
  ce->r_idx = i;
  ce->r_ptr = r_ptr;
  re = row_elem(matrix, i, r_ptr);
  re->c_idx = j;
  re->c_ptr = c_ptr;
  q_set(&re->coeff, a);

  return r_ptr;
}

#endif


/*
 * Convert row to a polynomial
 * - WARNING: the result is not normalized (variables are not in increasing order)
 */
static polynomial_t *convert_row_to_poly(row_t *row) {
  uint32_t i, j, n;
  int32_t x;
  polynomial_t *p;

  n = row->nelems;
  p = (polynomial_t *) safe_malloc(sizeof(polynomial_t) + (n+1) * sizeof(monomial_t));
  p->nterms = n;

  n = row->size;
  j = 0;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      p->mono[j].var = x;
      q_init(&p->mono[j].coeff);
      q_set(&p->mono[j].coeff, &row->data[i].coeff);
      j ++;
    }
  }
  // add the end marker to p
  assert(j == row->nelems);
  p->mono[j].var = max_idx;
  q_init(&p->mono[j].coeff);

  return p;
}



/*
 * COLUMN ADDITION
 */

/*
 * Increase the column capacity by 50% or to m,
 * depending on which is larger
 * - so after this, there's room for at least m columns
 */
static void matrix_increase_column_capacity(matrix_t *matrix, uint32_t m) {
  uint32_t n;

  n = matrix->column_cap + 1;
  n += n>>1;
  if (n < m) {
    n = m;
  }
  if (n >= MAX_MATRIX_NUM_COLUMNS) {
    out_of_memory();
  }
  matrix->column_cap = n;
  matrix->column = (column_t **) safe_realloc(matrix->column, n * sizeof(column_t *));
  matrix->base_row = (int32_t *) safe_realloc(matrix->base_row, n * sizeof(int32_t));
  matrix->index = (int32_t *) safe_realloc(matrix->index, n * sizeof(int32_t));
}



/*
 * Add a single column to the matrix
 * - the new column is empty (NULL)
 * - we also want to maintain the invariant that index[i] == -1 for
 *   every column i
 */
void matrix_add_column(matrix_t *matrix) {
  uint32_t i;

  i = matrix->ncolumns;
  if (i == matrix->column_cap) {
    // increase capacity by 50%
    matrix_increase_column_capacity(matrix, 0);
  }
  assert(i < matrix->column_cap);

  matrix->column[i] = NULL;
  matrix->base_row[i] = -1;
  matrix->index[i] = -1;
  matrix->ncolumns = i + 1;
}



/*
 * Add m new columns to the matrix
 * - all are initialized to NULL and their index[i] is set to -1
 */
void matrix_add_columns(matrix_t *matrix, uint32_t m) {
  uint32_t i, n;

  n = matrix->ncolumns + m;
  if (n >= matrix->column_cap) {
    matrix_increase_column_capacity(matrix, n);
  }
  assert(n <= matrix->column_cap);

  for (i=matrix->ncolumns; i<n; i++) {
    matrix->column[i] = NULL;
    matrix->base_row[i] = -1;
    matrix->index[i] = -1;
  }
  matrix->ncolumns = n;
}



#if 0
// not used

/*
 * Remove the empty elements from column c
 * - update the corresponding row elements
 */
static void matrix_compact_column(matrix_t *matrix, uint32_t c) {
  column_t *column;
  uint32_t i, j, n;
  int32_t r, r_ptr;

  assert(c < matrix->ncolumns);
  column = matrix->column[c];
  if (column == NULL || column->free < 0) return;

  n = column->size;
  j = 0;
  for (i=0; i<n; i++) {
    r = column->data[i].r_idx;
    if (r >= 0) {
      assert(j <= i);
      if (j < i) {
        r_ptr = column->data[i].r_ptr;
        column->data[j] = column->data[i];
        matrix->row[r]->data[r_ptr].c_ptr = j;
      }
      j ++;
    }
  }
  column->size = j;
  column->free = -1;
}

#endif



/*
 * ROW ADDITION
 */

/*
 * Increase the row capacity by 50%
 */
static void matrix_increase_row_capacity(matrix_t *matrix) {
  uint32_t n;

  n = matrix->row_cap + 1;
  n += n>>1;
  if (n >= MAX_MATRIX_NUM_ROWS) {
    out_of_memory();
  }
  matrix->row_cap = n;
  matrix->row = (row_t **) safe_realloc(matrix->row, n * sizeof(row_t *));
  matrix->base_var = (int32_t *) safe_realloc(matrix->base_var, n * sizeof(int32_t));
  matrix->marks = extend_bitvector(matrix->marks, n);
}


/*
 * Add a new row of the form p == 0
 * - p is defined by the array of monomials a
 * - n = size of that array
 * - there must be an existing column in the matrix for
 *   all the variables in p (i.e., a[0].var, ...., a[n-1].var)
 *   (i.e., a[i].var < matrix->ncolumns for i=0, ..., n-1)
 * - p must be normalized (all monomials must have different variables,
 *   and all coefficients must be non zero).
 */
void matrix_add_row(matrix_t *matrix, monomial_t *a, uint32_t n) {
  row_t *r;
  col_elem_t *c;
  uint32_t i, j, row_size;
  uint32_t c_ptr, r_idx;

#ifndef NDEBUG
  for (i=0; i<n; i++) {
    assert(q_is_nonzero(&a[i].coeff));
  }
#endif

  // allocate a row index
  r_idx = matrix->nrows;
  if (r_idx == matrix->row_cap) {
    matrix_increase_row_capacity(matrix);
  }
  assert(r_idx < matrix->row_cap);
  matrix->nrows = r_idx + 1;

  // allocate a row vector
  row_size = DEF_MATRIX_ROW_SIZE;
  if (row_size < n) {
    row_size = n;
  }
  r = new_row(row_size);
  assert(r->capacity >= n);

  // copy a[i] into r->data[i]
  // add the corresponding data to the column vectors
  for (i=0; i<n; i++) {
    j = a[i].var;
    c_ptr = get_column_elem(matrix, j);
    r->data[i].c_idx = j;
    r->data[i].c_ptr = c_ptr;
    q_init(&r->data[i].coeff);
    q_set(&r->data[i].coeff, &a[i].coeff);

    c = column_elem(matrix, j, c_ptr);
    c->r_idx = r_idx;
    c->r_ptr = i;
  }
  r->size = n;
  r->nelems = n;

  matrix->row[r_idx] = r;
  matrix->base_var[r_idx] = -1;
  clr_bit(matrix->marks, r_idx);
}



/*
 * Add a new row of the form x - p == 0
 * - p is defined by a[0] ... a[n-1]
 * - p must be normalized
 * - x must not occur in p
 */
void matrix_add_eq(matrix_t *matrix, int32_t x, monomial_t *a, uint32_t n) {
  row_t *r;
  col_elem_t *c;
  uint32_t i, j, row_size;
  uint32_t c_ptr, r_idx;

#ifndef NDEBUG
  for (i=0; i<n; i++) {
    assert(a[i].var != x && q_is_nonzero(&a[i].coeff));
  }
#endif

  // allocate a row index
  r_idx = matrix->nrows;
  if (r_idx == matrix->row_cap) {
    matrix_increase_row_capacity(matrix);
  }
  assert(r_idx < matrix->row_cap);
  matrix->nrows = r_idx + 1;

  // allocate a row vector
  row_size = DEF_MATRIX_ROW_SIZE;
  if (row_size < n+1) {
    row_size = n+1;
  }
  r = new_row(row_size);
  assert(r->capacity >= n+1);

  // copy -a[i] into r->data[i]
  // add the corresponding data to the column vectors
  for (i=0; i<n; i++) {
    j = a[i].var;
    c_ptr = get_column_elem(matrix, j);
    r->data[i].c_idx = j;
    r->data[i].c_ptr = c_ptr;
    q_init(&r->data[i].coeff);
    q_set_neg(&r->data[i].coeff, &a[i].coeff);

    c = column_elem(matrix, j, c_ptr);
    c->r_idx = r_idx;
    c->r_ptr = i;
  }
  // add x as last element of the row
  c_ptr = get_column_elem(matrix, x);
  r->data[i].c_idx = x;
  r->data[i].c_ptr = c_ptr;
  q_init(&r->data[i].coeff);
  q_set_one(&r->data[i].coeff);

  c = column_elem(matrix, x, c_ptr);
  c->r_idx = r_idx;
  c->r_ptr = i;

  i++;
  r->size = i;
  r->nelems = i;

  matrix->row[r_idx] = r;
  matrix->base_var[r_idx] = -1;
  clr_bit(matrix->marks, r_idx);
}


#ifndef NDEBUG

/*
 * Check a new tableau row (x - p)
 */
static void check_tableau_eq(matrix_t *matrix, int32_t x, monomial_t *a, uint32_t n) {
  uint32_t i;
  int32_t y;

  // x must not occur in the tableau
  assert(0 <= x && x < matrix->ncolumns && matrix->base_row[x] < 0);
  assert(matrix->column[x] == NULL || matrix->column[x]->nelems == 0);

  // all variables in a[0] ... a[n-1] must be non-basic
  for (i=0; i<n; i++) {
    y = a[i].var;
    assert(0 <= y && y < matrix->ncolumns && y != x && matrix->base_row[y] < 0);
  }
}

#endif


/*
 * Add a new row of the form x - p == 0 and make x the basic variable in the new row
 * - the matrix must be in tableau form
 * - p is stored as an array of monomials a[0] ... a[n-1]
 * - x must be a fresh variable not occurring in any row of the tableau
 * - x and the existing basic variables must not occur in p
 * - x and a[0].var, ..., a[n-1].var must be existing columns
 */
void matrix_add_tableau_eq(matrix_t *matrix, int32_t x, monomial_t *a, uint32_t n) {
  uint32_t r_idx; // index of the new row

#ifndef NDEBUG
  check_tableau_eq(matrix, x, a, n);
#endif

  r_idx = matrix->nrows;
  matrix_add_eq(matrix, x, a, n);
  assert(matrix->nrows == r_idx+1);
  matrix->base_var[r_idx] = x;
  matrix->base_row[x] = r_idx;
}


/*
 * Remove the empty elements from row r and update the columns
 */
static void matrix_compact_row(matrix_t *matrix, uint32_t r) {
  row_t *row;
  uint32_t i, j, n;
  int32_t c, c_ptr;

  assert(r < matrix->nrows);
  row = matrix->row[r];
  if (row == NULL || row->free < 0) return;

  n = row->size;
  j = 0;
  for (i=0; i<n; i++) {
    c = row->data[i].c_idx;
    if (c >= 0) {
      assert(j <= i);
      if (j < i) {
        c_ptr = row->data[i].c_ptr;
        row->data[j].c_idx = c;
        row->data[j].c_ptr = c_ptr;
        q_set(&row->data[j].coeff, &row->data[i].coeff);
        matrix->column[c]->data[c_ptr].r_ptr = j;
      }
      j ++;
    }
  }
  row->size = j;
  row->free = -1;

  // free the rationals
  while (j < n) {
    q_clear(&row->data[j].coeff);
    j ++;
  }
}


/*
 * Detach row from the column vectors
 */
static void matrix_detach_row(matrix_t *matrix, row_t *row) {
  uint32_t i, n;
  int32_t c, c_ptr;

  n = row->size;
  for (i=0; i<n; i++) {
    c = row->data[i].c_idx;
    if (c >= 0) {
      c_ptr = row->data[i].c_ptr;
      free_column_elem(matrix->column[c], c_ptr);
    }
  }
}



/*
 * Change the index of row to r
 */
static void matrix_change_row_index(matrix_t *matrix, row_t *row, uint32_t r) {
  uint32_t i, n;
  int32_t c, c_ptr;

  n = row->size;
  for (i=0; i<n; i++) {
    c = row->data[i].c_idx;
    if (c >= 0) {
      c_ptr = row->data[i].c_ptr;
      matrix->column[c]->data[c_ptr].r_idx = r;
    }
  }

}


/*
 * Remove all NULL or empty rows from the matrix
 * - renumber the rest
 */
static void compact_matrix(matrix_t *matrix) {
  row_t *row;
  uint32_t i, j, n;
  int32_t x;

  n = matrix->nrows;
  j = 0;
  for (i=0; i<n; i++) {
    row = matrix->row[i];
    if (row != NULL) {
      if (row->nelems == 0) {
        // delete the row
        delete_row(row);
      } else {
        if (j < i) {
          matrix_change_row_index(matrix, row, j);
          matrix->row[j] = row;
          assign_bit(matrix->marks, j, tst_bit(matrix->marks, i));

          x = matrix->base_var[i];
          matrix->base_var[j] = x;
          if (x >= 0) {
            matrix->base_row[x] = j;
          }
        }
        j ++;
      }
    }
  }

  matrix->nrows = j;
}




/*
 * REMOVAL OF ROWS AND COLUMNS
 */

/*
 * Remove rows[n ... nrows-1]
 */
static void matrix_remove_rows(matrix_t *matrix, uint32_t n) {
  uint32_t i, p;
  row_t *row;

  assert(n <= matrix->nrows);

  p = matrix->nrows;
  for (i=n; i<p; i++) {
    row = matrix->row[i];
    matrix_detach_row(matrix, row);
    delete_row(row);
    matrix->row[i] = NULL;
  }

  matrix->nrows = n;
}


/*
 * Remove columns[n ... ncolumns- 1]
 */
static void matrix_remove_columns(matrix_t *matrix, uint32_t n) {
  uint32_t i, p;
  column_t *col;

  assert(n <= matrix->ncolumns);

  p = matrix->ncolumns;
  for (i=n; i<p; i++) {
    col = matrix->column[i];
    if (col != NULL) {
      assert(col->nelems == 0);
      delete_column(col);
      matrix->column[i] = NULL;
    }
  }

  matrix->ncolumns = n;
}


/*
 * Reduce the matrix to dimension n x m
 * - n = number of rows to keep
 * - m = number of columns to keep
 */
void matrix_shrink(matrix_t *matrix, uint32_t n, uint32_t m) {
  assert(good_matrix(matrix));

  matrix_remove_rows(matrix, n);
  matrix_remove_columns(matrix, m);

  assert(good_matrix(matrix));
}



/*
 * REMOVAL OF FIXED VARIABLES
 */

/*
 * Find the index of the constant element in row r
 * - return -1 if r has no constant
 */
static int32_t get_constant_in_row(row_t *r) {
  uint32_t i, n;

  n = r->size;
  for (i=0; i<n; i++) {
    if (r->data[i].c_idx == const_idx) return i;
  }
  return -1;
}


/*
 * Build the constant vector (to prepare for elimination of fixed variables)
 */
void matrix_collect_constants(matrix_t *matrix) {
  uint32_t i, n;
  int32_t *tmp;

  assert(matrix->constant == NULL);
  n = matrix->nrows;
  tmp = (int32_t *) safe_malloc(n * sizeof(int32_t));
  matrix->constant = tmp;
  for (i=0; i<n; i++) {
    tmp[i] = get_constant_in_row(matrix->row[i]);
  }
}



/*
 * Eliminate fixed variable x (i.e., apply the substitution x := a)
 * - x must not be the const_idx
 */
void matrix_eliminate_fixed_variable(matrix_t *matrix, int32_t x, rational_t *a) {
  column_t *col;
  uint32_t i, n;
  int32_t j, k, r_ptr, c_ptr;
  row_elem_t *e, *cnst;

  assert(0 <= x && x < matrix->ncolumns && x != const_idx);
  col = matrix->column[x];
  if (col == NULL) return;  // nothing to do

  n = col->size;
  if (q_is_zero(a)) {
    // if a is zero, we just need to remove the column
    for (i=0; i<n; i++) {
      j = col->data[i].r_idx;
      if (j >= 0) {
        r_ptr = col->data[i].r_ptr;
        free_row_elem(matrix->row[j], r_ptr);
      }
    }
  } else {
    for (i=0; i<n; i++) {
      j = col->data[i].r_idx;
      if (j >= 0) {
        /*
         * e --> element c.x in row j = element of index r_ptr
         */
        r_ptr = col->data[i].r_ptr;
        e = row_elem(matrix, j, r_ptr);
        assert(e->c_idx == x);
        k = matrix->constant[j];
        if (k < 0) {
          // row j has no constant: attach e to column 0
          c_ptr = add_column_elem(matrix, const_idx, j, r_ptr);
          e->c_idx = const_idx;
          e->c_ptr = c_ptr;
          q_mul(&e->coeff, a); // make constant = a.c
          matrix->constant[j] = r_ptr;
        } else {
          // add a.c to element k of row j
          cnst = row_elem(matrix, j, k);
          q_addmul(&cnst->coeff, &e->coeff, a);
          // free e (from row j)
          free_row_elem(matrix->row[j], r_ptr);
        }
      }
    }
  }

  // remove column x
  delete_column(col);
  matrix->column[x] = NULL;
}


/*
 * Cleanup:
 * - remove all zero constant elements
 * - delete the constant array
 */
void matrix_cleanup_constants(matrix_t *matrix) {
  uint32_t i, n;
  int32_t r_ptr;
  row_elem_t *e;

  assert(matrix->constant != NULL);

  n = matrix->nrows;
  for (i=0; i<n; i++) {
    r_ptr = matrix->constant[i];
    if (r_ptr >= 0) {
      e = row_elem(matrix, i, r_ptr);
      assert(e->c_idx == const_idx);
      if (q_is_zero(&e->coeff)) {
        free_column_elem(matrix->column[const_idx], e->c_ptr);
        free_row_elem(matrix->row[i], r_ptr);
      }
    }
  }

  safe_free(matrix->constant);
  matrix->constant = NULL;
}











/*****************************
 *   MARKOWITZ'S HEURISTIC   *
 ****************************/

/*
 * Markowitz's heuristic is used during Gaussian elimination:
 * - select a pivot a_ij/=0 in row i, column j such that
 *      (r_count[i] - 1) * (c_count[j] - 1) is minimal
 *   where r_count[i] = number of non-zero coefficients in row i
 *         c_count[j] = number of non-zero coefficients in column j
 *
 * To implement this, we keep for a record for each row i:
 * - the best column j in that row + the index k of the corresponding element
 * - the score (r_count[i] - 1) * (c_count[j] - 1)
 * - then we store the rows in a heap
 *
 * The markowitz_t data structure also contains bitvector that flags
 * all variables that can be eliminated. This is used for simplifying the matrix.
 */

/*
 * Ordering function for the heap
 * - row_cmp(d, x, y) returns true if x has lower score than y
 */
static bool row_cmp(markowitz_t *d, int32_t x, int32_t y) {
  assert(d->row_rec[x] != NULL && d->row_rec[y] != NULL && x != y);
  return d->row_rec[x]->score < d->row_rec[y]->score;
}

/*
 * Compute (a - 1) * (b - 1).
 * - if there's an overflow return UINT32_MAX
 */
static inline uint32_t markowitz_score(uint32_t a, uint32_t b) {
  uint64_t tmp;
  tmp = ((uint64_t ) (a - 1)) * (b -1);
  return (tmp >= UINT32_MAX) ? UINT32_MAX : tmp;
}


/*
 * Initialize Markowitz's record for n rows and m columns
 * - the row_rec array is allocated but not initialized
 * - the elim_flag bitvector is initialized (all zeros)
 */
static void init_markowitz(markowitz_t *d, uint32_t n, uint32_t m) {
  assert(n < MAX_MATRIX_NUM_ROWS && m < MAX_MATRIX_NUM_COLUMNS);

  d->nrows = n;
  d->ncolumns = m;
  d->row_rec = (row_record_t **) safe_malloc(n * sizeof(row_record_t *));
  d->elim_flag = allocate_bitvector0(m);
  init_generic_heap(&d->heap, 0, n, (heap_cmp_fun_t) row_cmp, d);
  init_objstore(&d->store, sizeof(row_record_t), MARKOWITZ_RECORDS_PER_BLOCK);
}


/*
 * Delete the Markovitz's records
 */
static void delete_markowitz(markowitz_t *d) {
  safe_free(d->row_rec);
  delete_bitvector(d->elim_flag);
  delete_generic_heap(&d->heap);
  delete_objstore(&d->store);
}


/*
 * Mark all columns in array a as elimination candidates
 * - n = size of the array
 * - the constant const_idx must not be an elimination candidate.
 */
static void markowitz_init_columns(markowitz_t *d, int32_t *a, uint32_t n) {
  uint32_t i;
  int32_t x;

  for (i=0; i<n; i++) {
    x = a[i];
    assert(0 <= x && x < d->ncolumns && x != const_idx);
    set_bit(d->elim_flag, x);
  }
}


/*
 * Mark all columns except const_idx as elimination candidates
 */
static void markowitz_init_all_columns(markowitz_t *d) {
  set_bitvector(d->elim_flag, d->ncolumns);
  clr_bit(d->elim_flag, const_idx);
}


/*
 * Add record for row r to d->row_rec
 */
static void markowitz_add_record(markowitz_t *d, uint32_t r, uint32_t score, uint32_t c_idx, uint32_t r_ptr) {
  row_record_t *rec;

  rec = (row_record_t *) objstore_alloc(&d->store);
  rec->score = score;
  rec->c_idx = c_idx;
  rec->r_ptr = r_ptr;
  d->row_rec[r] = rec; // must be done before adding r to the heap
  generic_heap_add(&d->heap, r);
}


/*
 * Initialize the record for a singleton row r (of the form a.x == 0)
 * - row must be equal matrix->row[r]
 * - a new record is created
 */
static void markowitz_init_singleton_row(markowitz_t *d, matrix_t *matrix, row_t *row, uint32_t r) {
  uint32_t i;
  int32_t x;

  assert(row->nelems == 1 && row == matrix->row[r]);
  i = 0;
  x = row->data[i].c_idx;
  while (x < 0) {
    i ++;
    assert(i < row->size);
    x = row->data[i].c_idx;
  }

  markowitz_add_record(d, r, 0, x, i);
}


/*
 * Initialize the record for a row r with two monomials
 * - row must be equal matrix->row[r]
 * - a new record is created if the row is of the form
 *   a.x + b == 0 or if it's a.x + b.y == 0
 *   and x or y is marked for elimination
 */
static void markowitz_init_simple_row(markowitz_t *d, matrix_t *matrix, row_t *row, uint32_t r) {
  uint32_t i, j, score;
  int32_t x, y;

  assert(row->nelems == 2 && row == matrix->row[r]);

  if (row->size == 2) {
    i = 0; x = row->data[0].c_idx;
    j = 1; y = row->data[1].c_idx;
  } else {
    // find the two row elements
    i = 0;
    x = row->data[i].c_idx;
    while (x < 0) {
      i ++;
      assert(i < row->size);
      x = row->data[i].c_idx;
    }
    j = i;
    do {
      j ++;
      assert(j < row->size);
      y = row->data[j].c_idx;
    } while (y < 0);
  }

  assert(x >= 0 && y >= 0 && row->data[i].c_idx == x && row->data[j].c_idx == y);

  if (x == const_idx) {
    // eliminate y
    score = matrix->column[y]->nelems - 1;
    markowitz_add_record(d, r, score, y, j);

  } else if (y == const_idx) {
    // eliminate x
    score = matrix->column[x]->nelems - 1;
    markowitz_add_record(d, r, score, x, i);

  } else if (tst_bit(d->elim_flag, x)) {
    // x can be eliminated
    score = matrix->column[x]->nelems - 1;
    if (tst_bit(d->elim_flag, y) && matrix->column[y]->nelems <= score) {
      // y can be eliminated and is better than x
      score = matrix->column[y]->nelems - 1;
      markowitz_add_record(d, r, score, y, j);
    } else {
      markowitz_add_record(d, r, score, x, i);
    }

  } else if (tst_bit(d->elim_flag, y)) {
    // eliminate y
    score = matrix->column[y]->nelems - 1;
    markowitz_add_record(d, r, score, y, j);

  } else {
    // no elimination
    d->row_rec[r] = NULL;
  }

}


/*
 * Initialize the record for a row r (general case: r has at least 3 elements)
 * - row must be equal to matrix->row[r]
 * - a new record is created if the row contains a variable to eliminate
 * - otherwise d->col_rec[r] is NULL
 */
static void markowitz_init_row(markowitz_t *d, matrix_t *matrix, row_t *row, uint32_t r) {
  uint32_t i, n, c;
  uint32_t best_i, best_c;
  int32_t x, best_x;

  assert(row == matrix->row[r]);

  n = row->size;

  best_x = -1;
  best_i = 0;
  best_c = UINT32_MAX;

  // find best column for the row
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0 && tst_bit(d->elim_flag, x)) {
      c = matrix->column[x]->nelems;
      if (c < best_c) {
        best_c = c;
        best_x = x;
        best_i = i;
      }
    }
  }

  if (best_x >= 0) {
    markowitz_add_record(d, r, markowitz_score(best_c, row->nelems), best_x, best_i);
  } else {
    d->row_rec[r] = NULL;
  }
}


/*
 * Initialize the row record for all rows of matrix
 */
static void markowitz_init_rows(markowitz_t *d, matrix_t *matrix) {
  uint32_t i, n;
  row_t *row;

  assert(matrix->nrows == d->nrows);
  n = matrix->nrows;
  for (i=0; i<n; i++) {
    row = matrix->row[i];
    switch (row->nelems) {
    case 0:
      delete_row(row);
      matrix->row[i] = NULL;
      break;
    case 1:
      markowitz_init_singleton_row(d, matrix, row, i);
      break;
    case 2:
      markowitz_init_simple_row(d, matrix, row, i);
      break;
    default:
      markowitz_init_row(d, matrix, row, i);
      break;
    }
  }
}




/*
 * Update record for row r
 * - score, c_idx, r_ptr are the new record components
 */
static void markowitz_update_record(markowitz_t *d, uint32_t r, uint32_t score, uint32_t c_idx, uint32_t r_ptr) {
  row_record_t *rec;
  uint32_t old_score;

  rec = d->row_rec[r];
  if (rec != NULL) {
    old_score = rec->score;
    rec->score = score;
    rec->c_idx = c_idx;
    rec->r_ptr = r_ptr;
    if (score < old_score) {
      generic_heap_move_up(&d->heap, r);
    } else if (score > old_score) {
      generic_heap_move_down(&d->heap, r);
    }
  } else {
    markowitz_add_record(d, r, score, c_idx, r_ptr);
  }
}


/*
 * Remove record for row r
 */
static void markowitz_remove_record(markowitz_t *d, uint32_t r) {
  row_record_t *rec;

  rec = d->row_rec[r];
  if (rec != NULL) {
    generic_heap_remove(&d->heap, r);
    objstore_free(&d->store, rec);
    d->row_rec[r] = NULL;
  }
}


/*
 * Update the record for row r after it changes to a singleton row
 * - row must be equal matrix->row[r]
 */
static void markowitz_update_singleton_row(markowitz_t *d, matrix_t *matrix, row_t *row, uint32_t r) {
  uint32_t i;
  int32_t x;

  assert(row->nelems == 1 && row == matrix->row[r]);
  i = 0;
  x = row->data[i].c_idx;
  while (x < 0) {
    i ++;
    assert(i < row->size);
    x = row->data[i].c_idx;
  }
  markowitz_update_record(d, r, 0, x, i);
}


/*
 * Update the record for a row r with two monomials
 * - row must be equal matrix->row[r]
 */
static void markowitz_update_simple_row(markowitz_t *d, matrix_t *matrix, row_t *row, uint32_t r) {
  uint32_t i, j, score;
  int32_t x, y;

  assert(row->nelems == 2 && row == matrix->row[r]);

  if (row->size == 2) {
    i = 0;
    x = row->data[0].c_idx;
    j = 1;
    y = row->data[1].c_idx;
  } else {
    // find the two row elements
    i = 0;
    x = row->data[i].c_idx;
    while (x < 0) {
      i ++;
      assert(i < row->size);
      x = row->data[i].c_idx;
    }
    j = i;
    do {
      j ++;
      assert(j < row->size);
      y = row->data[j].c_idx;
    } while (y < 0);
  }

  assert(x >= 0 && y >= 0 && row->data[i].c_idx == x && row->data[j].c_idx == y);

  if (x == const_idx) {
    // eliminate y
    score = matrix->column[y]->nelems - 1;
    markowitz_update_record(d, r, score, y, j);

  } else if (y == const_idx) {
    // eliminate x
    score = matrix->column[x]->nelems - 1;
    markowitz_update_record(d, r, score, x, i);

  } else if (tst_bit(d->elim_flag, x)) {
    // x can be eliminated
    score = matrix->column[x]->nelems - 1;
    if (tst_bit(d->elim_flag, y) && matrix->column[y]->nelems <= score) {
      // y can be eliminated and is better than x
      score = matrix->column[y]->nelems - 1;
      markowitz_update_record(d, r, score, y, j);
    } else {
      markowitz_update_record(d, r, score, x, i);
    }

  } else if (tst_bit(d->elim_flag, y)) {
    // eliminate y
    score = matrix->column[y]->nelems - 1;
    markowitz_update_record(d, r, score, y, j);

  } else {
    // the row can't be eliminated
    markowitz_remove_record(d, r);
  }
}


/*
 * Update the record for a row r (general case: r has at least 3 elements)
 * - row must be equal to matrix->row[r]
 */
static void markowitz_update_row(markowitz_t *d, matrix_t *matrix, row_t *row, uint32_t r) {
  uint32_t i, n, c;
  uint32_t best_i, best_c;
  int32_t x, best_x;

  assert(row == matrix->row[r]);

  n = row->size;

  best_x = -1;
  best_i = 0;
  best_c = UINT32_MAX;

  // find best column for the row
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0 && tst_bit(d->elim_flag, x)) {
      c = matrix->column[x]->nelems;
      if (c < best_c) {
        best_c = c;
        best_x = x;
        best_i = i;
      }
    }
  }

  if (best_x >= 0) {
    markowitz_update_record(d, r, markowitz_score(best_c, row->nelems), best_x, best_i);
  } else {
    markowitz_remove_record(d, r);
  }
}


/*
 * Update record after row r has changed
 * - if r is non-empty and  does not have a record then a new one is created
 *   and added to the heap.
 * - during tableau construction, r may be a previously visited row that
 *   already has a basic variable. Since r is put back into the heap,
 *   it will be revisited again and possibly get simplified more.
 */
static void markowitz_update(markowitz_t *d, matrix_t *matrix, uint32_t r) {
  row_t *row;

  row = matrix->row[r];
  switch (row->nelems) {
  case 0:
    markowitz_remove_record(d, r);
    break;
  case 1:
    markowitz_update_singleton_row(d, matrix, row, r);
    break;
  case 2:
    markowitz_update_simple_row(d, matrix, row, r);
    break;
  default:
    markowitz_update_row(d, matrix, row, r);
    break;
  }
}









/*****************
 *    PIVOTING   *
 ****************/

/*
 * Given a row r and k = index of a row element in r (such that r[k] = <a, x, ..>
 * - divide all coefficients in row r by a so that the coefficient of x is 1
 */
void matrix_scale_row(row_t *r, uint32_t k) {
  uint32_t i, n;
  int32_t c, x;
  rational_t *a;

  x = r->data[k].c_idx;
  a = &r->data[k].coeff;
  assert(x >= 0 && x != const_idx && q_is_nonzero(a));

  if (q_is_one(a)) {
    // nothing to do
    return;
  } else if (q_is_minus_one(a)) {
    // negate all coefficients
    n = r->size;
    for (i=0; i<n; i++) {
      if (r->data[i].c_idx >= 0) {
        q_neg(&r->data[i].coeff);
      }
    }
    assert(q_is_one(a));

  } else {
    // divide all coefficients by a
    n = r->size;
    for (i=0; i<n; i++) {
      c = r->data[i].c_idx;
      if (c >= 0 && c != x) {
        q_div(&r->data[i].coeff, a);
      }
    }
    q_set_one(a);
  }
}


/*
 * Auxiliary function for variable elimination. This is the common
 * part of Gaussian elimination and pivoting.
 *
 * Input:
 * - r = index of the row where variable elimination is done
 * - k = index in that row of an element a.x where x is the variable to eliminate
 *       (i.e., matrix->row[r]->data[k] is (x, .., a) and a is non-zero
 * - row0 = a row where x has coefficient 1 (it must be distinct from row[r])
 *
 * The function subtract a * row0 from row[r] to eliminate x.
 */
void matrix_submul_row(matrix_t *matrix, uint32_t r, uint32_t k, row_t *row0) {
  row_t *row;
  row_elem_t *e;
  int32_t *index;
  uint32_t i, n;
  int32_t j, x;
  rational_t *a;

  assert(r < matrix->nrows);
  row = matrix->row[r];

  // for every variable x, index[x] = element where x occurs in row r or -1
  index = matrix->index;
  n = row->size;
  e = row->data;
  for (i=0; i<n; i++) {
    x = e[i].c_idx;
    if (x >= 0) index[x] = i;
  }

  // coefficient: a = row[k].coeff
  a = &matrix->factor;
  q_set(a, &row->data[k].coeff);

  // update the coefficients in row r
  n = row0->size;
  e = row0->data;
  if (q_is_one(a)) {
    /*
     * special case a=1: subtract row0 from row
     */
    for (i=0; i<n; i++) {
      x = e[i].c_idx;
      if (x >= 0) {
        j = index[x];
        if (j < 0) {
          // x does not occur in row r: create a new element
          j = alloc_row_elem(&row);
          row->data[j].c_idx = x;
          row->data[j].c_ptr = add_column_elem(matrix, x, r, j);
          q_set_neg(&row->data[j].coeff, &row0->data[i].coeff);
        } else {
          // x occurs in row
          q_sub(&row->data[j].coeff, &row0->data[i].coeff);
        }
      }
    }

  } else if (q_is_minus_one(a)) {
    /*
     * special case a=-1: add row0 to row
     */
    for (i=0; i<n; i++) {
      x = e[i].c_idx;
      if (x >= 0) {
        j = index[x];
        if (j < 0) {
          // x does not occur in row r
          j = alloc_row_elem(&row);
          row->data[j].c_idx = x;
          row->data[j].c_ptr = add_column_elem(matrix, x, r, j);
          q_set(&row->data[j].coeff, &row0->data[i].coeff);
        } else {
          // x occurs in row
          q_add(&row->data[j].coeff, &row0->data[i].coeff);
        }
      }
    }

  } else {
    /*
     * general case: subtract a * row0 from row
     */
    for (i=0; i<n; i++) {
      x = e[i].c_idx;
      if (x >= 0) {
        j = index[x];
        if (j < 0) {
          // x does not occur in row r: create a new element
          j = alloc_row_elem(&row);
          row->data[j].c_idx = x;
          row->data[j].c_ptr = add_column_elem(matrix, x, r, j);
          q_set_neg(&row->data[j].coeff, a);
          q_mul(&row->data[j].coeff, &row0->data[i].coeff);
        } else {
          // x occurs in element j of row r
          q_submul(&row->data[j].coeff, a, &row0->data[i].coeff);
        }
      }
    }
  }

  assert(q_is_zero(&row->data[k].coeff));

  /*
   * row must be copied back since alloc_row_elem may change it
   */
  matrix->row[r] = row;

  /*
   * Cleanup: reset the indices to -1
   * and remove the zero elements
   */
  index = matrix->index;
  n = row->size;
  e = row->data;
  for (i=0; i<n; i++) {
    x = e[i].c_idx;
    if (x >= 0) {
      index[x] = -1;
      if (q_is_zero(&e[i].coeff)) {
        remove_row_elem(matrix, r, i);
      }
    }
  }

  if (row->nelems * 2 < row->size) {
    matrix_compact_row(matrix, r);
  }

}




/*
 * Pivoting step: make x basic in r0
 * - k identifies the variable: k must be the index of the element where
 * x occurs in row r0
 */
void matrix_pivot(matrix_t *matrix, uint32_t r0, uint32_t k) {
  row_t *row0;
  column_t *col;
  int32_t x, r, j;
  uint32_t i, n;

  assert(r0 < matrix->nrows && matrix->row[r0] != NULL && k < matrix->row[r0]->size);

  row0 = matrix->row[r0];
  x = row0->data[k].c_idx; // variable x to make basic

  assert(x >= 0 && x != const_idx);

  // update row0: make coefficient of x equal to 1
  matrix_scale_row(row0, k);

  // eliminate x from the other rows
  col = matrix->column[x];
  n = col->size;
  for (i=0; i<n; i++) {
    r = col->data[i].r_idx;
    if (r >= 0 && r != r0) {
      j = col->data[i].r_ptr;
      matrix_submul_row(matrix, r, j, row0);
      assert(matrix->column[x] == col); // column[x] should not change
    }
  }

  // reset the column: it contains a single element
  if (col->capacity >= MATRIX_SHRINK_COLUMN_THRESHOLD) {
    // attempt to save memory: replace column[x] by a smaller column
    delete_column(col);
    col = new_column(DEF_MATRIX_COL_SIZE);
    matrix->column[x] = col;
  }
  col->free = -1;
  col->nelems = 1;
  col->size = 1;
  col->data[0].r_idx = r0;
  col->data[0].r_ptr = k;

  row0->data[k].c_ptr = 0;

  // update base_row and base_var
  j = matrix->base_var[r0];
  if (j >= 0) {
    matrix->base_row[j] = -1; // variable j no longer basic
  }
  matrix->base_var[r0] = x;
  matrix->base_row[x] = r0;
}






/*
 * VARIABLE ELIMINATION
 */


/*
 * Eliminate a zero variable: perform the substitution x := 0
 * - if d is non-null, the markowitz record of all modified rows is updated
 * - the column of x is deleted
 */
static void matrix_eliminate_zero_variable(matrix_t *matrix, markowitz_t *d, int32_t x) {
  column_t *col;
  row_t *row;
  uint32_t i, n;
  int32_t r, k;

  assert(0 <= x && x < matrix->ncolumns && matrix->column[x] != NULL);
  col = matrix->column[x];
  n = col->size;
  for (i=0; i<n; i++) {
    r = col->data[i].r_idx;
    if (r >= 0) {
      k = col->data[i].r_ptr;

      // remove x from row r
      row = matrix->row[r];
      assert(row->data[k].c_idx == x);
      q_clear(&row->data[k].coeff);
      free_row_elem(row, k);

      // update the heap
      if (d != NULL) {
        markowitz_update(d, matrix, r);
      }
    }
  }

  // delete column[x]
  delete_column(col);
  matrix->column[x] = NULL;
}





/*
 * Special form of submul for variable substitution: replace a variable
 * in row r by the monomial - b.y
 * - r = row index
 * - k = index in row r of an element a.x where x is the variable to eliminate
 * - e0 = monomial b.y in a row r0 (distinct from r)
 */
static void matrix_submul_simple_row(matrix_t *matrix, uint32_t r, uint32_t k, row_elem_t *e0) {
  row_t *row;
  row_elem_t *e;
  uint32_t i, n;
  int32_t x, y;

  y = e0->c_idx;

  // search for y in row r
  row = matrix->row[r];
  n = row->size;
  e = row->data;
  for (i=0; i<n; i++) {
    if (e[i].c_idx == y) break;
  }

  if (i < n) {
    // y is in row r at position i: subtract a.b from its coefficient
    q_submul(&e[i].coeff, &e0->coeff, &e[k].coeff);
    if (q_is_zero(&e[i].coeff)) {
      remove_row_elem(matrix, r, i);
    }
    // clear coefficient of x
    q_clear(&e[k].coeff);
    remove_row_elem(matrix, r, k);

  } else {
    // recycle row->data[k] (from a.x to -ab.y)
    x = e[k].c_idx;
    free_column_elem(matrix->column[x], e[k].c_ptr);
    e[k].c_idx = y;
    e[k].c_ptr = add_column_elem(matrix, y, r, k);
    q_neg(&e[k].coeff);
    q_mul(&e[k].coeff, &e0->coeff);
    assert(q_is_nonzero(&e[k].coeff));
  }

}



/*
 * Perform the substitution x := -e = - b.y
 * - if d != NULL, the markowitz record of all modified rows is updated
 * - e must not occur in the rows that are being modified
 *   and the variable in e must be distinct from x
 * _ the column of x is removed
 */
static void matrix_substitute_variable(matrix_t *matrix, markowitz_t *d, int32_t x, row_elem_t *e) {
    column_t *col;
  uint32_t i, n;
  int32_t r, k;

  assert(0 <= x && x < matrix->ncolumns && matrix->column[x] != NULL && x != e->c_idx);

  col = matrix->column[x];
  n = col->size;
  for (i=0; i<n; i++) {
    r = col->data[i].r_idx;
    if (r >= 0) {
      k = col->data[i].r_ptr;

      // subtract a.(x + b.y) from row r
      matrix_submul_simple_row(matrix, r, k, e);
      if (d != NULL) {
        markowitz_update(d, matrix, r);
      }
    }
  }

  // delete column[x]
  delete_column(col);
  matrix->column[x] = NULL;
}



/*
 * Pivot and update to markowitz records
 * - make a variable x basic in r0
 * - k points to a row element r0->data[k] where x occurs
 */
static void matrix_pivot_and_update(matrix_t *matrix, markowitz_t *d, uint32_t r0, uint32_t k) {
  row_t *row0;
  column_t *col;
  int32_t x, r, j;
  uint32_t i, n;

  assert(r0 < matrix->nrows && matrix->row[r0] != NULL && k < matrix->row[r0]->size && d != NULL);

  row0 = matrix->row[r0];
  x = row0->data[k].c_idx; // variable x to make basic

  assert(x >= 0 && x != const_idx);

  // update row0: make coefficient of x equal to 1
  matrix_scale_row(row0, k);

  // eliminate x from the other rows
  col = matrix->column[x];
  n = col->size;
  for (i=0; i<n; i++) {
    r = col->data[i].r_idx;
    if (r >= 0 && r != r0) {
      j = col->data[i].r_ptr;
      matrix_submul_row(matrix, r, j, row0);
      assert(matrix->column[x] == col); // column[x] should not change

      // update the heap for row r
      markowitz_update(d, matrix, r);
    }
  }

  // reset the column: it contains a single element
  col->free = -1;
  col->nelems = 1;
  col->size = 1;
  col->data[0].r_idx = r0;
  col->data[0].r_ptr = k;
  row0->data[k].c_ptr = 0;

  // update base_row and base_var
  j = matrix->base_var[r0];
  if (j >= 0) {
    matrix->base_row[j] = -1; // variable j no longer basic
  }
  matrix->base_var[r0] = x;
  matrix->base_row[x] = r0;

}










/****************************
 *   GAUSSIAN ELIMINATION   *
 ***************************/

/*
 * Rows that are removed from a matrix during Gaussian elimination are
 * stored into two separate data structures:
 * - a fixed variable vectors stores variable assignments: x == a.
 *   each assignment is the elimination of a singleton row (x == 0) or
 *   a simple row (x + a == 0)
 * - an elimination matrix stores an upper triangular matrix
 *   each row in the matrix is a polynomial a_1 x_1 + ... + a_n x_n ==0
 *   with one variable x_i as diagonal element (base_var), with
 *   coefficient a_i = 1
 */



/*
 * ELIMINATION MATRIX
 */

/*
 * Initialize an elimination matrix.
 * - the initial row_capacity is 0
 * - number of rows = 0 too
 */
void init_elim_matrix(elim_matrix_t *matrix) {
  matrix->capacity = 0;
  matrix->nrows = 0;
  matrix->row = NULL;
  matrix->base_var = NULL;
}


/*
 * Delete an elimination matrix
 * - also delete all the polynomials it contains
 */
void delete_elim_matrix(elim_matrix_t *matrix) {
  uint32_t i, n;

  n = matrix->nrows;
  for (i=0; i<n; i++) {
    free_polynomial(matrix->row[i]);
  }

  safe_free(matrix->row);
  safe_free(matrix->base_var);
  matrix->row = NULL;
  matrix->base_var = NULL;
}


/*
 * Empty an elimination matrix
 */
void reset_elim_matrix(elim_matrix_t *matrix) {
  uint32_t i, n;

  n = matrix->nrows;
  for (i=0; i<n; i++) {
    free_polynomial(matrix->row[i]);
  }
  matrix->nrows = 0;
}


/*
 * Allocate a new row in matrix
 * - return its index i
 * - matrix->row[i] and matrix->base_var[i] are not initialized
 */
static uint32_t elim_matrix_alloc_row(elim_matrix_t *matrix) {
  uint32_t i, n;

  i = matrix->nrows;
  n = matrix->capacity;
  if (i == n) {
    // allocate more rows
    if (n == 0) {
      n = DEF_ELIM_MATRIX_NUM_ROWS;
    } else {
      n ++;
      n += n>>1;
      if (n >= MAX_ELIM_MATRIX_NUM_ROWS) {
        out_of_memory();
      }
    }

    matrix->base_var = (int32_t *) safe_realloc(matrix->base_var, n * sizeof(int32_t));
    matrix->row = (polynomial_t **) safe_realloc(matrix->row, n * sizeof(polynomial_t *));
    matrix->capacity = n;
  }
  assert(i < matrix->capacity);
  matrix->nrows = i+1;

  return i;
}


/*
 * Copy the content of row into an elimination matrix:
 * - x = base variable for that row
 * - convert row to a polynomial
 */
static void elim_matrix_add_row(elim_matrix_t *matrix, int32_t x, row_t *row) {
  uint32_t i;

  i = elim_matrix_alloc_row(matrix);
  matrix->base_var[i] = x;
  matrix->row[i] = convert_row_to_poly(row);
}



/*
 * FIXED VARIABLE VECTOR
 */

/*
 * Initialization: nothing allocated yet
 */
void init_fvar_vector(fvar_vector_t *v) {
  v->nvars = 0;
  v->size = 0;
  v->fvar = NULL;
}


/*
 * Deletion: clear all rationals then delete the array
 */
void delete_fvar_vector(fvar_vector_t *v) {
  uint32_t i, n;

  n = v->nvars;
  for (i=0; i<n; i++) {
    q_clear(&v->fvar[i].value);
  }
  safe_free(v->fvar);
  v->fvar = NULL;
}


/*
 * Empty the vector and clear all rationals
 */
void reset_fvar_vector(fvar_vector_t *v) {
  uint32_t i, n;

  n = v->nvars;
  for (i=0; i<n; i++) {
    q_clear(&v->fvar[i].value);
  }
  v->nvars = 0;
}


/*
 * Allocate a new element in v and initialize its rational value
 * - extend the array if necessary
 * - return its index
 */
static uint32_t fvar_vector_alloc(fvar_vector_t *v) {
  uint32_t i, n;

  i = v->nvars;
  n = v->size;
  if (i == n) {
    if (n == 0) {
      n = DEF_FVAR_VECTOR_SIZE;
    } else {
      n ++;
      n += n>>1;
      if (n >= MAX_FVAR_VECTOR_SIZE) {
        out_of_memory();
      }
    }
    v->fvar = (fvar_rec_t *) safe_realloc(v->fvar, n * sizeof(fvar_rec_t));
    v->size = n;
  }
  assert(i < v->size);
  q_init(&v->fvar[i].value);
  v->nvars = i + 1;

  return i;
}


/*
 * Store the pair (x, -a) in v
 */
static void fvar_vector_add_neg(fvar_vector_t *v, int32_t x, rational_t *a) {
  uint32_t i;

  i = fvar_vector_alloc(v);
  v->fvar[i].var = x;
  q_set_neg(&v->fvar[i].value, a);
 }


/*
 * Store the pair (x, 0) into v
 */
static void fvar_vector_add0(fvar_vector_t *v, int32_t x) {
  uint32_t i;

  i = fvar_vector_alloc(v);
  v->fvar[i].var = x;
  assert(q_is_zero(&v->fvar[i].value));
 }






/*
 * SIMPLIFICATION
 */


/*
 * Eliminate a simple row (i.e., a row with two monomials)
 * - d = markowitz data structure
 * - i_flag = bitvector for integer variables
 * - row0 = row to eliminate
 * - r0 = its index in the matrix
 * - k = index of the monomial to eliminate:
 *   row0->data[k] = a. x where x is the variable to eliminate
 * - elim = elimination matrix (or NULL)
 * - fvar = fixed var vector
 */
static void gauss_elim_simple_row(matrix_t *matrix, markowitz_t *d, byte_t *i_flag,
                                  row_t *row0, uint32_t r0, uint32_t k,
                                  elim_matrix_t *elim, fvar_vector_t *fvars) {
  uint32_t i;
  int32_t x, y;
  bool y_is_int;

  assert(row0 == matrix->row[r0] && row0 != NULL && row0->nelems == 2 && k < row0->size);

  x = row0->data[k].c_idx;   // variable to eliminate
  matrix_scale_row(row0, k); // rewrite row0 as x + b.y == 0

  assert(x != const_idx);

  // find the other monomial in row0
  i = 0;
  for (;;) {
    assert(i < row0->size);
    y = row0->data[i].c_idx;
    if (x != y && y >= 0) break;
    i ++;
  }

  // row0->data[i] == monomial b.y
  if (y == const_idx) {
    /*
     * Apply the substitution x := -b
     * This may be inconsistent if x is integer and b is not, but the simplex
     * solver will detect this when scanning the fvar vector.
     */
    fvar_vector_add_neg(fvars, x, &row0->data[i].coeff);
    goto substitute;
  }


  if (tst_bit(i_flag, x)) {
    // Check whether the substitution x := -b.y is ok
    y_is_int = tst_bit(i_flag, y);
    if (y_is_int && q_is_integer(&row0->data[i].coeff)) {
      // b.y is an integer
      goto save_and_substitute;
    }

    /*
     * Try the substitution y := -1/b.x if it's allowed
     * Old test was:
     *  if (tst_bit(d->elim_flag, y) && matrix->column[y]->nelems <= matrix->column[x]->nelems) {
     * but replacing y by -1/b x is fine even if y occurs more often than x in the matrix.
     */
    if (tst_bit(d->elim_flag, y)) {
      matrix_scale_row(row0, i); // rewrite row0 as a.x + y == 0
      if (!y_is_int || q_is_integer(&row0->data[k].coeff)) {
        // we can apply y := -a.x
        x = y;
        i = k;
        goto save_and_substitute;
      }
    }

    // failed substitution: keep row0
    return;
  }

 save_and_substitute:
  if (elim != NULL) {
    elim_matrix_add_row(elim, x, row0);
  }

 substitute:
  /*
   * Perform the substitution x := - b.y where b.y is row0->data[i]
   */
  matrix_detach_row(matrix, row0);
  matrix_substitute_variable(matrix, d, x, row0->data + i);
  delete_row(row0);
  matrix->row[r0] = NULL;
}



/*
 * Check whether all coefficients and variables of row are integer
 * - i_flag = integer bit vector
 * - return true if for all monomial a.x both a and x are integer
 */
static bool all_integer_row(row_t *row, byte_t *i_flag) {
  uint32_t i, n;
  int32_t x;

  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      if (! (tst_bit(i_flag, x) && q_is_integer(&row->data[i].coeff))) {
        return false;
      }
    }
  }
  return true;
}


/*
 * Eliminate a generic row
 * - d = markowitz data structure
 * - i_flag = bitvector for integer variables
 * - row0 = row to eliminate
 * - r0 = its index in the matrix
 * - k = index of the monomial to eliminate:
 *   row0->data[k] = a. x where x is the variable to eliminate
 * - elim = elimination matrix (or NULL)
 */
static void gauss_elim_row(matrix_t *matrix, markowitz_t *d, byte_t *i_flag,
                           row_t *row0, uint32_t r0, uint32_t k,
                           elim_matrix_t *elim) {

  column_t *col;
  uint32_t i, n;
  int32_t x, r, j;

  assert(row0 == matrix->row[r0] && row0 != NULL && k < row0->size);

  x = row0->data[k].c_idx;    // variable to eliminate
  matrix_scale_row(row0, k);  // make coefficient of x equal to 1

  assert(x != const_idx);

  if (tst_bit(i_flag, x) && ! all_integer_row(row0, i_flag)) {
    /*
     * Can't use the row to eliminate x: just keep the row for now.
     * We could also try another variable in the same row?
     */
    return;
  }

  if (elim != NULL) {
    elim_matrix_add_row(elim, x, row0);
  }
  matrix_detach_row(matrix, row0);

  // eliminate x from the other rows
  col = matrix->column[x];
  n = col->size;
  for (i=0; i<n; i++) {
    r = col->data[i].r_idx;
    if (r >= 0) {
      assert(r != r0);
      j = col->data[i].r_ptr;
      matrix_submul_row(matrix, r, j, row0);
      markowitz_update(d, matrix, r);
    }
  }

  // delete column x and row r0
  delete_column(col);
  matrix->column[x] = NULL;

  delete_row(row0);
  matrix->row[r0] = NULL;
}




/*
 * Eliminate rows in the matrix
 * - d = markowitz data structure: must contain the rows to eliminate
 * - i_flag = bitvector that indicates which variables are integer
 * - fvars = vector to store eliminated fixed variables
 * - elim = elimination matrix to store other eliminated rows
 *   if elim is NULL, the eliminated rows are not stored anywhere.
 */
static void gaussian_elimination(matrix_t *matrix, markowitz_t *d, byte_t *i_flag,
                                 elim_matrix_t *elim, fvar_vector_t *fvars) {
  row_t *row0;
  int32_t r0;
  uint32_t x, k;

  for (;;) {
    r0 = generic_heap_get_min(&d->heap);
    if (r0 < 0) break;

    row0 = matrix->row[r0];
    x = d->row_rec[r0]->c_idx;
    k = d->row_rec[r0]->r_ptr;


#if 0
    if (tst_bit(i_flag, x)) {
      printf("---> eliminating i!%"PRIu32" and row %"PRId32" (score = %"PRIu32")\n", x, r0, d->row_rec[r0]->score);
    } else {
      printf("---> eliminating z!%"PRIu32" and row %"PRId32" (score = %"PRIu32")\n", x, r0, d->row_rec[r0]->score);
    }
#endif

    /*
     * row0 = row[r0] = row to eliminate
     * x = variable to eliminate
     * k = index of monomial a.x in row0
     */
    markowitz_remove_record(d, r0);

    switch (row0->nelems) {
    case 0: // should never happen
      abort();
    case 1:
      matrix_detach_row(matrix, row0); // must be done before elim_zero_var
      delete_row(row0);
      matrix->row[r0] = NULL;
      fvar_vector_add0(fvars, x); // record the assignment x := 0
      matrix_eliminate_zero_variable(matrix, d, x); // remove x
      break;
    case 2:
      gauss_elim_simple_row(matrix, d, i_flag, row0, r0, k, elim, fvars);
      break;
    default:
      gauss_elim_row(matrix, d, i_flag, row0, r0, k, elim);
      break;
    }

  }
}


/*
 * Matrix simplification:
 * - mark the rows and variables to eliminate then apply Gaussian elimination
 * - pivoting steps are applied in the order defined by the Markowitz heuristic
 *
 * Parameters:
 * - matrix = input matrix
 * - elim_candidates = array of variables that may be eliminated
 *   n = size of that array. There must not be duplicates in the array.
 * - i_flag = bitvector that indicates which variables are integer:
 *   i_flag[x] = 1 means x is an integer variable,
 *   i_flag[x] = 0 means x is not an integer variable
 * - elim = elimination matrix where the eliminated rows will be stored
 *   (if elim is NULL nothing is stored)
 * - fvars = vectors to record the eliminated fixed variables
 *
 * The result is stored in matrix, elim, and fvars:
 * - matrix = simplified matrix
 * - fvars = variable assignments of the form x == b where x is a variable id and
 *   b is a rational constant (the assignments result from the elimination of
 *   singleton or simple rows)
 * - elim (if non-NULL) = other eliminated rows/triangular matrix
 *
 * NOTE: the variable assignments in fvars may be inconsistent
 * - there can be two types of inconsistencies:
 *   (x == 0) where x = const_idx = 1 if a row a == 0 is generated with a!=0
 *   (x == b) where x is an integer variable and b is not an integer
 * - the caller must check for this
 */
void simplify_matrix(matrix_t *matrix, int32_t *elim_candidates, uint32_t n, byte_t *i_flag,
                     elim_matrix_t *elim, fvar_vector_t *fvars) {
  markowitz_t d;

  init_markowitz(&d, matrix->nrows, matrix->ncolumns);
  markowitz_init_columns(&d, elim_candidates, n);
  markowitz_init_rows(&d, matrix);

  gaussian_elimination(matrix, &d, i_flag, elim, fvars);
  compact_matrix(matrix);

  delete_markowitz(&d);
}







/***********************************
 *  INITIAL TABLEAU CONSTRUCTION   *
 **********************************/

/*
 * Two heuristics can be used to compute basic variables
 * - simple heuristic: scan rows from 0 to n-1, pick the best variable in that row
 * - Markowitz heuristic: scan the rows in the order defined by their score
 *   in the Markowitz data structure
 */


/*
 * Remove a singleton row row0 during tableau construction
 * - if d is non-null, update the Markowitz records
 * - the row0 must be matrix->row[r0]
 * - the eliminated variable is stored in fvars
 *
 * If row0 is a constant row then the assignment const_idx = 0 is added to fvars.
 * This is an invalid assignment and there's no solution to the equations. We add
 * the equation anyway so that the caller can check for feasibility by scanning
 * the assignments in fvars.
 */
static void tableau_remove_singleton_row(matrix_t *matrix, markowitz_t *d,
                                         row_t *row0, uint32_t r0, fvar_vector_t *fvars) {
  uint32_t i;
  int32_t x;

  assert(matrix->row[r0] == row0 && row0->nelems == 1 && row0->size > 0);

  // find the variable in row r0
  i = 0;
  x = row0->data[i].c_idx;
  while (x < 0) {
    i ++;
    assert(i < row0->size);
    x = row0->data[i].c_idx;
  }

  assert(0 <= x && x < matrix->ncolumns && matrix->column[x] != NULL);

  // store x := 0 in fvars
  fvar_vector_add0(fvars, x);

  // remove row0 from the column vectors and replace x by 0 in other rows
  matrix_detach_row(matrix, row0);
  matrix_eliminate_zero_variable(matrix, d, x);

  // delete the row
  delete_row(row0);
  matrix->row[r0] = NULL;
}




/*
 * Eliminate row r0 by replacing x by the constant in element e
 * - if d != NULL, update the Markowitz records of all rows modified
 * - row0 must be equal to matrix->row[r0]
 * - x must have coefficient 1 in the row
 * - e->c_idx must be const_idx
 * NOTE: e is an element inside row0
 *
 * The assignment x := - e is saved in fvars even if it's inconsistent.
 * This may happen if x is an integer variable and e is not an integer
 * constant. The assignments must be checked for feasibility by the callers.
 */
static void tableau_remove_simple_row(matrix_t *matrix, markowitz_t *d,
                                      row_t *row0, uint32_t r0, int32_t x, row_elem_t *e, fvar_vector_t *fvars) {
  assert(0 <= x && x < matrix->ncolumns && matrix->column[x] != NULL && matrix->row[r0] == row0 && e->c_idx == const_idx);

  // save the assignment x := - e->coeff
  fvar_vector_add_neg(fvars, x, &e->coeff);

  // apply the substitution x := - e  to all rows where x occurs (except row0)
  matrix_detach_row(matrix, row0);
  matrix_substitute_variable(matrix, d, x, e);

  // remove row0
  delete_row(row0);
  matrix->row[r0] = NULL;

}


/*
 * Check whether a simple row row0 can be eliminated
 * - if so, add an assignment x := constant to fvars
 * - otherwise, select a basic variable for that row
 */
static void tableau_process_simple_row(matrix_t *matrix, row_t *row0, uint32_t r0, fvar_vector_t *fvars) {
  uint32_t i, j;
  int32_t x, y;

  assert(row0->nelems == 2 && row0 == matrix->row[r0] && row0->size >= 2);

  if (row0->size == 2) {
    i = 0; x = row0->data[0].c_idx;
    j = 1; y = row0->data[1].c_idx;
  } else {
    // find the two row elements
    i = 0;
    x = row0->data[i].c_idx;
    while (x < 0) {
      i ++;
      assert(i < row0->size);
      x = row0->data[i].c_idx;
    }
    j = i;
    do {
      j ++;
      assert(j < row0->size);
      y = row0->data[j].c_idx;
    } while (y < 0);
  }

  assert(x >= 0 && y >= 0 && row0->data[i].c_idx == x && row0->data[j].c_idx == y);

  if (x == const_idx) {
    // substitute y by the constant in row->data[i]
    matrix_scale_row(row0, j);  // make coefficient of y == 1
    tableau_remove_simple_row(matrix, NULL, row0, r0, y, row0->data + i, fvars);

  } else if (y == const_idx) {
    // substitute x by the constant in row->data[j]
    matrix_scale_row(row0, i);  // make coefficient of x == 1
    tableau_remove_simple_row(matrix, NULL, row0, r0, x, row0->data + j, fvars);

  } else if (matrix->column[y]->nelems < matrix->column[x]->nelems) {
    // make y basic in row r0
    matrix_pivot(matrix, r0, j);
    assert(matrix->base_var[r0] == y);

  } else {
    // make x basic in row r0
    matrix_pivot(matrix, r0, i);
    assert(matrix->base_var[r0] == x);
  }
}



/*
 * Find a basic variable in row r0
 * - matrix->row[r0] must be equal to row0
 * - row0 has at least 3 elements
 */
static void tableau_process_row(matrix_t *matrix, row_t *row0, uint32_t r0) {
  uint32_t i, n, c;
  int32_t x;
  uint32_t best_i, best_c;
#ifndef NDEBUG
  int32_t best_x;
#endif

  assert(matrix->row[r0] == row0);

#ifndef NDEBUG
  best_x = -1;
#endif
  best_i = 0;
  best_c = UINT32_MAX;

  // find the lower-cost variable to pivot
  n = row0->size;
  for (i=0; i<n; i++) {
    x = row0->data[i].c_idx;;
    if (x >= 0 && x != const_idx) {
      c = matrix->column[x]->nelems;
      if (c < best_c) {
        best_c = c;
        best_i = i;
#ifndef NDEBUG
        best_x = x;
#endif
      }
    }
  }

  // make best_x the basic variable for r0
  assert(best_x >= 0);
  matrix_pivot(matrix, r0, best_i);
  assert(matrix->base_var[r0] == best_x);
}



/*
 * Simple tableau construction:
 * - scan all rows in index order
 * - if a row is of the form a.x == 0 or a.x + b == 0,
 *   record the corresponding assignment (x == 0 or x == -b/a) in fvars
 *   and remove the row
 * - otherwise, pick the variable with smallest column count and make it basic variable
 */
void simple_tableau_construction(matrix_t *matrix, fvar_vector_t *fvars) {
  uint32_t i, n;
  row_t *row;
  bool need_compact;

  need_compact = false;
  n = matrix->nrows;
  for (i=0; i<n; i++) {
    row = matrix->row[i];
    switch (row->nelems) {
    case 0:
      delete_row(row);
      matrix->row[i] = NULL;
      need_compact = true;
      break;
    case 1:
      tableau_remove_singleton_row(matrix, NULL, row, i, fvars);
      need_compact = true;
      break;
    case 2:
      tableau_process_simple_row(matrix, row, i, fvars);
      need_compact |= (matrix->row[i] == NULL);
      break;
    default:
      tableau_process_row(matrix, row, i);
      break;
    }
  }

  if (need_compact) {
    compact_matrix(matrix);
  }
}





/*
 * Check whether simple row row0 can be eliminated
 * - if so add the assignment x := constant to fvars
 * - otherwise, make variable x basic in that row
 * - k = index of monomial where x occurs in row0
 */
static void markowitz_tableau_process_simple_row(matrix_t *matrix, markowitz_t *d,
                                                 row_t *row0, uint32_t r0, uint32_t k, fvar_vector_t *fvars) {
  uint32_t i;
  int32_t x, y;

  assert(row0 == matrix->row[r0] && row0 != NULL && row0->nelems == 2 && k < row0->size);

  x = row0->data[k].c_idx;   // variable to eliminate

  assert(x != const_idx);

  // find the other monomial in row0
  i = 0;
  for (;;) {
    assert(i < row0->size);
    y = row0->data[i].c_idx;
    if (x != y && y >= 0) break;
    i ++;
  }

  if (y == const_idx) {
    // eliminate x
    matrix_scale_row(row0, k); // rewrite row0 as x + b.y == 0
    tableau_remove_simple_row(matrix, d, row0, r0, x, row0->data + i, fvars);
  } else {
    // make x basic in row r0
    matrix_pivot_and_update(matrix, d, r0, k);
    assert(matrix->base_var[r0] == x);
  }
}




/*
 * Reprocess row row0 when it gets reduced to a 2-monomial row
 * - x = a variable in that row
 * - if row0 is of the form x + constant == 0 then eliminate row0
 */
static void markowitz_tableau_revisit_simple_row(matrix_t *matrix, row_t *row0, uint32_t r0, int32_t x, fvar_vector_t *fvars) {
  uint32_t i;
  int32_t y;

  assert(row0 == matrix->row[r0] && row0 != NULL && row0->nelems == 2 && matrix->base_var[r0] >= 0 && x != const_idx);

  // find the other monomial in row0
  i = 0;
  for (;;) {
    assert(i < row0->size);
    y = row0->data[i].c_idx;
    if (x != y && y >= 0) break;
    i ++;
  }

  if (y == const_idx) {
    /*
     * x must be the basic var so the row is of the form x + a == 0
     * where a = rational coeff in data[i].
     * Since x is basic, it occurs only in r0 so there's no substitution to propagate
     */
    assert(matrix->base_var[r0] == x && matrix->column[x] != NULL &&
           matrix->column[x]->nelems == 1);

    fvar_vector_add_neg(fvars, x, &row0->data[i].coeff);

    free_column_elem(matrix->column[const_idx], row0->data[i].c_ptr);
    delete_row(row0);
    matrix->row[r0] = NULL;
    delete_column(matrix->column[x]);
    matrix->column[x] = NULL;
    matrix->base_row[x] = -1;
  }

}




/*
 * Tableau construction using the Markowitz heuristic
 */
void markowitz_tableau_construction(matrix_t *matrix, fvar_vector_t *fvars) {
  markowitz_t d;
  int32_t r0, x;
  row_t *row0;
  uint32_t k;

  init_markowitz(&d, matrix->nrows, matrix->ncolumns);
  markowitz_init_all_columns(&d);
  markowitz_init_rows(&d, matrix);

  for (;;) {
    r0 = generic_heap_get_min(&d.heap);
    if (r0 < 0) break;

    /*
     * See notes in markowitz_update: r0 may be visited several
     * times.
     */
    row0 = matrix->row[r0];
    x = d.row_rec[r0]->c_idx;
    k = d.row_rec[r0]->r_ptr;
    markowitz_remove_record(&d, r0);

    if (matrix->base_var[r0] < 0) {
      /*
       * First visit of row r0
       * Make x basic variable in row r0
       * - k = index of the monomial a.x in row0
       */
      switch (row0->nelems) {
      case 0:
        abort();
      case 1:
        tableau_remove_singleton_row(matrix, &d, row0, r0, fvars);
        break;
      case 2:
        markowitz_tableau_process_simple_row(matrix, &d, row0, r0, k, fvars);
        break;
      default:
        matrix_pivot_and_update(matrix, &d, r0, k);
        assert(matrix->base_var[r0] == x);
        break;
      }

    } else {
      /*
       * r0 already has a basic variable,
       * check whether it can be eliminated
       */
      if (row0->nelems == 1) {
        assert(matrix->base_var[r0] == x && matrix->column[x] != NULL &&
               matrix->column[x]->nelems == 1);

        // store x := 0 to fvars then delete the row and colum
        fvar_vector_add0(fvars, x);
        delete_row(row0);
        matrix->row[r0] = NULL;
        delete_column(matrix->column[x]);
        matrix->column[x] = NULL;

        // x is no longer basic
        matrix->base_row[x] = -1;

      } else if (row0->nelems == 2) {
        markowitz_tableau_revisit_simple_row(matrix, row0, r0, x, fvars);
      }

    }
  }

  compact_matrix(matrix);
  delete_markowitz(&d);
}







#ifndef NDEBUG

#include <stdio.h>
#include <inttypes.h>


/*
 * DEBUGGING SUPPORT
 */

/*
 * Index of variable x in row r
 * - return -1 if x does not occur in r
 */
static int32_t get_var_in_row(row_t *row, int32_t x) {
  uint32_t i, n;

  n = row->size;
  for (i=0; i<n; i++) {
    if (row->data[i].c_idx == x) return i;
  }
  return -1;
}


/*
 * Consistency properties for base_var:
 * - base_row[base_var[r]] == r for all rows
 * - base_var[r] != const_idx
 * - base_var[r] < ncolumns
 * - base_var[r] occurs in row r with coefficient 1
 */
static bool good_base_var(matrix_t *matrix) {
  uint32_t i, n;
  int32_t x, k;
  row_t *row;

  n = matrix->nrows;
  for (i=0; i<n; i++) {
    x = matrix->base_var[i];
    if (x >= 0) {
      if (x == const_idx || x >= matrix->ncolumns || matrix->base_row[x] != i) {
        return false;
      }
      row = matrix->row[i];
      k = get_var_in_row(row, x);
      if (k < 0 || ! q_is_one(&row->data[k].coeff)) {
        return false;
      }
    }
  }
  return true;
}


/*
 * Consistency properties for base_row
 * - base_var[base_row[x]] == x for all basic variables
 * - base_var[r] < nrows
 */
static bool good_base_row(matrix_t *matrix) {
  uint32_t i, n;
  int32_t r;

  n = matrix->ncolumns;
  for (i=0; i<n; i++) {
    r = matrix->base_row[i];
    if (r >= 0) {
      if (r >= matrix->nrows || matrix->base_var[r] != i) {
        return false;
      }
    }
  }

  return true;
}



/*
 * Consistency property for a row r
 * - if row->data[i] = (x, k, a) then
 *    a /= 0 and 0 <= x < ncolumns and column[x]->data[k] = (x, i)
 * - nelems == number of non-zero coefficients
 */
static bool good_row(matrix_t *matrix, uint32_t r) {
  row_t *row;
  col_elem_t *e;
  uint32_t j, i, n;
  int32_t x, k;

  row = matrix->row[r];
  if (row == NULL) return false;

  n = row->size;
  j = 0;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      if (x >= matrix->ncolumns || q_is_zero(&row->data[i].coeff)) {
        return false;
      }
      k = row->data[i].c_ptr;
      if (k < 0 || k >= matrix->column[x]->size) {
        return false;
      }
      e = column_elem(matrix, x, k);
      if (e->r_idx != r || e->r_ptr != i) return false;
      j ++;
    }
  }

  if (j != row->nelems) return false;

  return true;
}


/*
 * Consistency properties for a column c
 * - if column->data[i] = (r, k) the row[r]->data[k] = (c, i, ...)
 * - nelems = number of elements in column c
 */
static bool good_column(matrix_t *matrix, uint32_t c) {
  column_t *column;
  row_elem_t *e;
  uint32_t j, i, n;
  int32_t r, k;

  column = matrix->column[c];
  if (column != NULL) {
    n = column->size;
    j = 0;
    for (i=0; i<n; i++) {
      r = column->data[i].r_idx;
      if (r >= 0) {
        if (r >= matrix->nrows) return false;
        k = column->data[i].r_ptr;
        if (k < 0 || k >= matrix->row[r]->size) {
          return false;
        }
        e = row_elem(matrix, r, k);
        if (e->c_idx != c || e->c_ptr != i) return false;
        j ++;
      }
    }

    if (j != column->nelems) return false;
  }

  return true;
}


/*
 * Run all consistency checks on matrix
 */
bool good_matrix(matrix_t *matrix) {
  uint32_t i, n;

  if (good_base_var(matrix) && good_base_row(matrix)) {
    n = matrix->nrows;
    for (i=0; i<n; i++) {
      if (! good_row(matrix, i)) {
        printf("---> Bad row[%"PRIu32"]\n", i);
        fflush(stdout);
        return false;
      }
    }

    n = matrix->ncolumns;
    for (i=0; i<n; i++) {
      if (! good_column(matrix, i)) {
        printf("---> Bad column[%"PRIu32"]\n", i);
        fflush(stdout);
        return false;
      }
    }

    return true;

  } else {
    return false;
  }
}


#endif
