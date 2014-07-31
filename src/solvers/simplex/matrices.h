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
 *   is maintained. Links are stored in the c_ptr field.
 * - if col_idx >= 0, then it's the index k of a variable x_k
 *   the triple represents a * x_k and c_ptr is an index in the array
 *   column[k].
 *
 * Each column is an array of pairs (row_idx, r_ptr)
 * - if row_idx < 0, the pair is not used. It's stored in a free list
 *   with links stored in r_ptr.
 * - if row_idx >= 0, then it's the index of a row i and r_ptr is
 *   an index in the array row[i].
 *
 * For a non-zero element a_ij in row i, column j, there are two
 * indices i_ptr and j_ptr such that
 * - row[i][i_ptr] = (j, j_ptr, a_ij)
 * - col[j][j_ptr] = (i, i_ptr)
 *
 * Column index 0 = const_idx is used to represent constants in the equations:
 * a_1 x_1 + ... + a_n x_n + b = 0, where b is a rational constant, is represented as
 * b.x_0 + a_1.x_1 + ... + a_n x_n = 0. The value of x_0 should always be one (i.e., it
 * should be a fixed variable with lower bound and upper bound both equal to 1).
 *
 * Initially, the matrix is not a tableau. Rows can be added arbitrarily, and there are
 * no basic variables. The matrix can be converted to a tableau using the
 * tableau_construction functions. This assigns a basic variable to every row.
 * Then the matrix is in the form
 *
 *    y_1 + a_11 x_1 + ... + a_1n x_n = 0
 *                  ...
 *    y_p + a_p1 x_1 + ... + a_pn x_n = 0
 *
 * where y_1, ..., y_p are basic variables. It is possible to add a new row to the
 * tableau provided the row is of the form y_t + a_t1 x_1 + ... + a_tn x_n = 0
 * - the basic variable y_t must be a fresh variable, not occurring in any other row.
 * - the existing basic variables y_1, ..., y_p must not occur in the new row.
 */

#ifndef __MATRICES_H
#define __MATRICES_H

#include <stdint.h>
#include <stdbool.h>

#include "terms/rationals.h"
#include "terms/polynomials.h"
#include "utils/object_stores.h"
#include "utils/generic_heap.h"
#include "utils/bitvectors.h"


/*
 * Row and column element
 */
typedef struct row_elem_s {
  int32_t c_idx;    // column index
  int32_t c_ptr;    // pointer into column[c_idx]
  rational_t coeff;
} row_elem_t;

typedef struct col_elem_s {
  int32_t r_idx;   // row index
  int32_t r_ptr;   // index into row[r_idx]
} col_elem_t;


/*
 * Row descriptor:
 * - the initialized elements are in row->data[0 ... size-1]
 * - capacity = size of the array data
 * - nelems = number of elements (non-zero coefficients)
 * - free = start of the free list
 */
typedef struct row_s {
  uint32_t nelems;
  uint32_t size;
  uint32_t capacity;
  int32_t  free;
  row_elem_t data[0]; // real size is equal to capacity
} row_t;


/*
 * Column descriptor: same thing
 */
typedef struct column_s {
  uint32_t nelems;
  uint32_t size;
  uint32_t capacity;
  int32_t free;
  col_elem_t data[0]; // the real size is equal to capacity
} column_t;



/*
 * Matrix
 * - two arrays: one for rows, one for columns
 * - base_var[i] = the basic variable of row i or -1 if basic variables
 *   have not been computed
 * - base_row[v] = row where v is basic variable or -1 if v is non-basic
 *
 * Index array:
 * - index is an auxiliary array used for building a row r
 * - for a column j, index[j] is the index of a row_element in r
 *   whose c_idx is j (or -1 if r does not contain j)
 *   (if k = index[j] then r->data[k].c_idx == j)
 * - outside row operations, index[j] must be -1 for all j
 *
 * Mark bitvector:
 * - one bit per row: 1 means the row is marked, 0 means it's not marked.
 * - this is used by external code to construct sets of rows (e.g., for propagation)
 *
 * Constant array: built on demand
 * - constant: for each row i, constant[i] = index of the
 *   constant in row i. If constant[i] = k >= 0, then row[i][k] is
 *   <b, x_0, ..>.  If constant[i] = -1, then there's no constant in row i.
 *
 */
typedef struct matrix_s {
  uint32_t nrows;        // number of rows
  uint32_t ncolumns;     // number of columns
  uint32_t row_cap;      // size of the arrays row and basic_var
  uint32_t column_cap;   // size of the column array
  row_t **row;
  column_t **column;
  int32_t *base_var;
  int32_t *base_row;

  // auxiliary data structures
  int32_t *index;
  rational_t factor;    // pivot coefficient

  // marks
  byte_t *marks;

  // optional components
  int32_t *constant;    // maps rows to constant
} matrix_t;


/*
 * Default and maximal size (i.e., max capacity) of a row or column
 */
#define DEF_MATRIX_ROW_SIZE 10
#define MAX_MATRIX_ROW_SIZE ((uint32_t)((UINT32_MAX-sizeof(row_t))/sizeof(row_elem_t)))

#define DEF_MATRIX_COL_SIZE 10
#define MAX_MATRIX_COL_SIZE ((uint32_t)((UINT32_MAX-sizeof(column_t))/sizeof(col_elem_t)))


/*
 * Threshold that triggers a reduction of basic columns
 * - if variable x is made basic and column[x] has capacity >= MATRIX_SHRINK_THRESHOLD
 *   then column[x] is reduced to a column of default capacity (i.e., DEF_MATRIX_COL_SIZE)
 *   (because  column[x] needs to contain only one element).
 */
#define MATRIX_SHRINK_COLUMN_THRESHOLD 100


/*
 * Default and maximal number of rows/columns in a matrix
 * - we set the max to UINT32_MAX/8 == UINT32_MAX/sizeof(pointer on 64bit machines)
 * - this should help make the behavior consistent on 32/64 bit architectures
 */
#define DEF_MATRIX_NUM_ROWS 100
#define MAX_MATRIX_NUM_ROWS (UINT32_MAX/8)

#define DEF_MATRIX_NUM_COLUMNS 100
#define MAX_MATRIX_NUM_COLUMNS (UINT32_MAX/8)




/*
 * GAUSSIAN ELIMINATION
 */

/*
 * Gaussian elimination constructs a triangular matrix
 * a_11 x_1 + a_12 x_2 + .....        + a_1n x_n == 0
 *            a_22 x_2 + .....        + a_2n x_n == 0
 *                             ....
 *                      a_kk xk + ... +  a_kn x_n == 0
 * with a_11=1, ..., a_kk = 1
 *
 * We may need this to construct models. We store the
 * triangular matrix in two arrays: each row is represented
 * as a polynomial + we keep a base_var array that gives
 * the diagonal variable for each row
 */
typedef struct elim_matrix_s {
  uint32_t nrows;
  uint32_t capacity;
  polynomial_t **row;
  int32_t *base_var;
} elim_matrix_t;


#define DEF_ELIM_MATRIX_NUM_ROWS 10
#define MAX_ELIM_MATRIX_NUM_ROWS (UINT32_MAX/8)


/*
 * Fixed variables: during Gaussian elimination,
 * all variables that occur in a row x == 0 or x + a == 0
 * (where a is a constant) are eliminated.
 * The corresponding variables and their values are stored in
 * a resizable array. Each element of the array is a pair <var, rational>
 */
typedef struct fvar_rec_s {
  int32_t var;
  rational_t value;
} fvar_rec_t;

typedef struct fvar_vector_s {
  uint32_t nvars; // number of fixed variables
  uint32_t size;  // size of the array
  fvar_rec_t *fvar;
} fvar_vector_t;

#define DEF_FVAR_VECTOR_SIZE 10
#define MAX_FVAR_VECTOR_SIZE (UINT32_MAX/sizeof(fvar_rec_t))


/*
 * Markowitz's heuristic:
 * - Gaussian elimination selects a pivot a_ij/=0 in row i, column j
 * - to keep the matrix sparse after pivoting, the heuristic picks
 *   a_ij for which (r_count[i] - 1) * (c_count[j] - 1) is minimal
 *   where r_count[i] = number of non-zero coefficients in row i
 *         c_count[j] = number of non-zero coefficients in column j
 *
 * To implement this, we keep for a record for each row i:
 * - the best column j in that row + the index k of the corresponding element
 * - the score (r_count[i] - 1) * (c_count[j] - 1)
 */

/*
 * Record for each row r
 * - row[r]->data[r_ptr].c_idx = best column
 */
typedef struct row_record_s row_record_t;

struct row_record_s {
  uint32_t score; // (r_count[r_idx] - 1) * (c_count[c_idx] - 1)
  uint32_t c_idx; // best column
  uint32_t r_ptr; // element index
};


/*
 * Pivot selection data:
 * - row_rec[r] = record for row r or NULL is r is not considered for elimination
 * - elim_flag = bitvector: elim_flag[x] = 1 if x is to be eliminated, 0 otherwise
 * - heap = all rows with non-NULL record in increasing score order
 * - store = object store to allocate row_records
 */
typedef struct markowitz_s {
  uint32_t nrows;
  uint32_t ncolumns;
  row_record_t **row_rec;
  byte_t *elim_flag;
  generic_heap_t heap;
  object_store_t store;
} markowitz_t;


// parameter for object-store: number of records per block
#define MARKOWITZ_RECORDS_PER_BLOCK 330



/*
 * GENERIC MATRICES
 */

/*
 * Initialize a matrix of initial capacity = n rows, m columns
 * - if n == 0, then DEF_MATRIX_NUM_ROWS is used,
 * - if m == 0, then DEF_MATRIX_NUM_COLUMNS is used
 * - nrows and ncolumns are both 0
 */
extern void init_matrix(matrix_t *matrix, uint32_t n, uint32_t m);

/*
 * Delete matrix: free all memory it uses
 */
extern void delete_matrix(matrix_t *matrix);

/*
 * Reset the matrix: to the empty matrix (nrows = ncolumns = 0)
 */
extern void reset_matrix(matrix_t *matrix);

/*
 * Make a copy of matrix1 into matrix
 * - this copies the rows and columns
 * - row_idx, base_var, base_row are set to NULL
 */
extern void copy_matrix(matrix_t *matrix, matrix_t *matrix1);



/*
 * ROW AND COLUMN ADDITION
 */

/*
 * Add one column to matrix
 * - the new column vector is initialized to NULL (empty column)
 * - its index is the current number of columns
 */
extern void matrix_add_column(matrix_t *matrix);

/*
 * Add m columns to matrix
 * - if p = number of columns before the call, then the new columns
 * are given ids p to p + m - 1
 */
extern void matrix_add_columns(matrix_t *matrix, uint32_t m);


/*
 * The two following functions can add arbitrary rows to the matrix,
 * without assigning basic variables to the new row. They cannot be
 * used if the matrix is in tableau form.
 */

/*
 * Add a new row of the form p == 0
 * - p is stored as an array of monomials a[0] ... a[n-1]
 * - the variables a[0].var ... a[n-1].var must all be existing columns
 * It should be OK for p to be zero, but that should be avoided since it
 * adds an empty row to the matrix.
 */
extern void matrix_add_row(matrix_t *matrix, monomial_t *a, uint32_t n);

/*
 * Add a new row of the form x - p == 0
 * - p is stored as an array of monomials a[0] ... a[n-1]
 * - x must not occur in p
 * - x and a[0].var, ..., a[n-1].var must be existing columns
 */
extern void matrix_add_eq(matrix_t *matrix, int32_t x, monomial_t *a, uint32_t n);


/*
 * Add a new row of the form x - p == 0 and make x the basic variable in the new row
 * - the matrix must be in tableau form
 * - p is stored as an array of monomials a[0] ... a[n-1]
 * - x must be a fresh variable not occurring in any row of the tableau
 * - x and the existing basic variables must not occur in p
 * - x and a[0].var, ..., a[n-1].var must be existing columns
 */
extern void matrix_add_tableau_eq(matrix_t *matrix, int32_t x, monomial_t *a, uint32_t n);



/*
 * REMOVE ROWS AND COLUMNS
 */

/*
 * Reduce the matrix to dimension n x m
 * - n = number of rows to keep
 * - m = number of columns to keep
 */
extern void matrix_shrink(matrix_t *matrix, uint32_t n, uint32_t m);


/*
 * ACCESS TO MATRIX COMPONENTS
 */

/*
 * Get row i of the matrix
 */
static inline row_t *matrix_row(matrix_t *matrix, uint32_t i) {
  assert(i < matrix->nrows);
  return matrix->row[i];
}

/*
 * Get column x of the matrix (this may be NULL)
 */
static inline column_t *matrix_column(matrix_t *matrix, int32_t x) {
  assert(0 <= x && x < matrix->ncolumns);
  return matrix->column[x];
}

/*
 * Get the basic variable in row i
 * - return -1 = null_thvar if there's no basic variable
 */
static inline int32_t matrix_basic_var(matrix_t *matrix, uint32_t i) {
  assert(i < matrix->nrows);
  return matrix->base_var[i];
}

/*
 * Get the row where variable x is basic
 * - return -1 if x is not basic
 */
static inline int32_t matrix_basic_row(matrix_t *matrix, int32_t x) {
  assert(0 <= x && x < matrix->ncolumns);
  return matrix->base_row[x];
}

/*
 * Check whether x is basic
 */
static inline bool matrix_is_basic_var(matrix_t *matrix, int32_t x) {
  return matrix_basic_row(matrix, x) >= 0;
}

static inline bool matrix_is_nonbasic_var(matrix_t *matrix, int32_t x) {
  return matrix_basic_row(matrix, x) < 0;
}


/*
 * Number of non-zero coefficients in row i
 */
static inline uint32_t matrix_row_count(matrix_t *matrix, uint32_t i) {
  assert(i < matrix->nrows);
  return matrix->row[i]->nelems;
}


/*
 * Number of non-zero coefficients in column x
 */
static inline uint32_t matrix_column_count(matrix_t *matrix, int32_t x) {
  assert(0 <= x && x < matrix->ncolumns);
  return matrix->column[x] == NULL ? 0 : matrix->column[x]->nelems;
}



/*
 * Coefficient of element k in row r
 */
static inline rational_t *matrix_coeff(matrix_t *matrix, uint32_t r, uint32_t k) {
  assert(r < matrix->nrows && k < matrix->row[r]->size && matrix->row[r]->data[k].c_idx >= 0);
  return &matrix->row[r]->data[k].coeff;
}



/*
 * MARKS
 */

/*
 * Set or clear mark on row r
 */
static inline void matrix_mark_row(matrix_t *matrix, uint32_t r) {
  assert(r < matrix->nrows);
  set_bit(matrix->marks, r);
}

static inline void matrix_unmark_row(matrix_t *matrix, uint32_t r) {
  assert(r < matrix->nrows);
  clr_bit(matrix->marks, r);
}


/*
 * Check whether row r is marked
 */
static inline bool matrix_row_is_marked(matrix_t *matrix, uint32_t r) {
  assert(r < matrix->nrows);
  return tst_bit(matrix->marks, r);
}

static inline bool matrix_row_is_unmarked(matrix_t *matrix, uint32_t r) {
  return ! matrix_row_is_marked(matrix, r);
}



/*
 * ELIMINATION OF FIXED VARIABLES
 */

/*
 * The process is
 * 1) build the const_idx vector
 * 2) call eliminate_fixed variable for every fixed variable x
 * 3) call cleanup_constants
 * - no rows or columns should be added during this process
 */

/*
 * Allocate and initialize the constant array
 */
extern void matrix_collect_constants(matrix_t *matrix);

/*
 * Remove a fixed variable x (i.e., apply the substitution x := a)
 * - a must be a rational (not an extended rational)
 * - if row i contains variable x with coefficient b, then we add
 *   b * a to the constant of that row
 */
extern void matrix_eliminate_fixed_variable(matrix_t *matrix, int32_t x, rational_t *a);

/*
 * Cleanup the constants: remove all constant elements with coeff == 0
 * - then delete the constant vector
 */
extern void matrix_cleanup_constants(matrix_t *matrix);




/*
 * PIVOTING
 */

/*
 * Given a row r and k = index of a row element in r (such that r[k] = <a, x, ..>
 * - divide all coefficients in row r by a so that the coefficient of x is 1
 */
extern void matrix_scale_row(row_t *r, uint32_t k);

/*
 * Eliminate a variable from row r:
 * - r = index of the row where variable elimination is done
 * - k = index in that row of an element a.x where x is the variable to eliminate
 *       (i.e., matrix->row[r]->data[k] is (x, .., a) and a is non-zero
 * - row0 = a row where x has coefficient 1 (it must be distinct from row[r])
 *
 * The function subtract a * row0 from row[r] to eliminate x.
 */
extern void matrix_submul_row(matrix_t *matrix, uint32_t r, uint32_t k, row_t *row0);

/*
 * Pivoting: make a variable x basic in row r0
 * - r0 = row index
 * - k = element index in row r0 that identifies x:
 * k must be the index of a valid element, such that
 * matrix->row[r0]->data[k] is a triple (x, j, a) where
 *    x is a variable index (x >= 0)
 *    a is a non-zero rational
 * Important: x must not be equal to const_idx (i.e., 0)
 */
extern void matrix_pivot(matrix_t *matrix, uint32_t r0, uint32_t k);




/*
 * ELIMINATION MATRICES
 */

/*
 * Initialize an elimination matrix.
 * - the initial row_capacity is 0
 * - number of rows = 0 too
 */
extern void init_elim_matrix(elim_matrix_t *matrix);

/*
 * Delete an elimination matrix
 * - also delete all the polynomials it contains
 */
extern void delete_elim_matrix(elim_matrix_t *matrix);

/*
 * Reset to an empty elimination matrix
 * - also delete all polynomials
 */
extern void reset_elim_matrix(elim_matrix_t *matrix);


/*
 * Get row number i
 */
static inline polynomial_t *elim_matrix_row(elim_matrix_t *matrix, uint32_t i) {
  assert(i < matrix->nrows);
  return matrix->row[i];
}

/*
 * Get diagonal variable for row i
 */
static inline int32_t elim_matrix_base_var(elim_matrix_t *matrix, uint32_t i) {
  assert(i < matrix->nrows);
  return matrix->base_var[i];
}



/*
 * FIXED VARIABLE VECTOR
 */

/*
 * Initialize a vector to store fixed variables
 * - initial size is 0
 */
extern void init_fvar_vector(fvar_vector_t *v);

/*
 * Clear all rationals then delete the vector
 */
extern void delete_fvar_vector(fvar_vector_t *v);

/*
 * Reset to the empty vector
 */
extern void reset_fvar_vector(fvar_vector_t *v);



/*
 * MATRIX SIMPLIFICATION AND TABLEAU CONSTRUCTION
 */

/*
 * The simplifications rely on Gaussian elimination to attempt to
 * remove variables. Empty rows that occur during Gaussian elimination
 * are removed. Also, if a simple row a.x + b == 0 or a.x == 0 is
 * created, then x is eliminated and stored in the fixed-variable
 * vector.
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
 * - matrix = the simplified matrix
 * - fvars = rows of the form x == b where x is eliminated and b is a rational constant
 * - elim (if non-NULL) = other eliminated rows/triangular matrix
 *
 * NOTE: the variable assignments in fvars may be inconsistent
 * - there can be two types of inconsistencies:
 *   (x == 0) where x = const_idx = 1 if a row a == 0 is generated with a!=0
 *   (x == b) where x is an integer variable and b is not an integer
 * - the caller must check for this
 */
extern void simplify_matrix(matrix_t *matrix, int32_t *elim_candidates, uint32_t n,
                            byte_t *i_flag, elim_matrix_t *elim, fvar_vector_t *fvars);




/*
 * Simple tableau construction
 * - scan all rows
 * - if a row is of the form a.x == 0 or a.x + b == 0,
 *   record the corresponding assignment (x == 0 or x == -b/a) in fvars
 *   and remove the row
 * - otherwise, pick the variable with smallest column count and make it basic variable
 *
 * There can be inconsistent assignments in fvars (cf. simplify_matrix)
 */
extern void simple_tableau_construction(matrix_t *matrix, fvar_vector_t *fvars);


/*
 * Tableau construction using the Markowitz heuristic
 * - process the rows in the order defined by the Markowitz heuristic
 * - eliminate rows of the from a.x == 0 or a.x + b == 0
 *   and record the corresponding variable assignment in fvars
 *
 * There can be inconsistent assignments in fvars (cf. note in simplify_matrix)
 */
extern void markowitz_tableau_construction(matrix_t *matrix, fvar_vector_t *fvars);




#ifndef NDEBUG

/*
 * SUPPORT FOR DEBUGGING
 */

/*
 * Check internal consistency of matrix m:
 * - check whether the base_var and base_row are consistent
 * - check whether row and columns are consistent
 */
extern bool good_matrix(matrix_t *matrix);

#endif




#endif /* __MATRICES_H */
