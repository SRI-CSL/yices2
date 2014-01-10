/*********************************************
 *  Construction and operations on matrices  *
 ********************************************/

#ifndef __MATRICES_H

#include <stdio.h>

#include "matrix_types.h"
#include "rationals.h"



/**********************************
 *  ALLOCATION/RESIZE FUNCTIONS   *
 *********************************/

/*
 * Create a new matrix with nrows and ncolumns.
 * The row and column capacities are also set to nrows/ncolumns.
 * All the columns and rows are empty.
 */
extern matrix_t *new_matrix(int nrows, int ncolumns);


/*
 * Make room in the row array for at least n rows.
 * - if n is no more than m->nrows, nothing is done.
 * - otherwise, sufficient space is allocated for n rows and 
 *   the new rows are initialized. They are all empty.
 */
extern void adjust_nrows(matrix_t *m, int n);

/*
 * Make room in the column array for at least n columns.
 * - if n is no more than m->ncolumns, nothing is done.
 * - otherwise, sufficient space is allocated for n columns and 
 *   the descriptors of all the new columns are initialized.
 * - all new columns are empty.
 */
extern void adjust_ncolumns(matrix_t *m, int n);

/*
 * Increase the capacity of the row array.
 * \param n = minimal capacity requested.
 * The new capacity is max(n, old-cap * 1.5 + 1).
 * - nrows is not changed.
 */
extern void expand_row_capacity(matrix_t *m, int n);

/*
 * Increase the capacity of the column-descriptor array.
 * \param n = minimal capacity requested.
 * The new capacity is max(n, old-cap * 1.5 + 1).
 * - ncolumns is not changed.
 */
extern void expand_column_capacity(matrix_t *m, int n);


/*
 * Remove the empty elements from row r_idx and update the column
 * dependencies.
 * - requires 0 <= r_idx <= m->nrows - 1 (row of that index exists).
 */
extern void compact_row(matrix_t *m, int r_idx);


/*
 * Remove the empty elements from column c_idx and update the row ptrs.
 * - requires 0 <= c_idx <= m->ncolumns - 1.
 */
extern void compact_column(matrix_t *m, int c_idx);



/*
 * Delete matrix m.
 */
extern void delete_matrix(matrix_t *m);






/**********************************
 *  ADDITION OF ROWS AND COLUMNS  *
 *********************************/

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
extern void add_vectelem_as_new_row(matrix_t *m, vector_elem_t *v, int n);

/*
 * New row is given as a vector
 */
extern void add_vector_as_new_row(matrix_t *m, vector_t *v);

/*
 * New row is given as a buffer
 */
extern void add_buffer_as_new_row(matrix_t *m, buffer_t *buffer);



/*
 * COLUMN ADDITION
 *
 * Create a new column and add it as the last column of m.
 * row and column arrays are adjusted to have enough room if 
 * necessary.
 */

/*
 * New column is given as an array of n vector_elem_t elements
 */
extern void add_vectelem_as_new_column(matrix_t *m, vector_elem_t *v, int n);

/*
 * New column is given as a vector
 */
extern void add_vector_as_new_column(matrix_t *m, vector_t *v);

/*
 * New column is given as a buffer
 */
extern void add_buffer_as_new_column(matrix_t *m, buffer_t *buffer);



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
extern int store_vectelem_in_row(matrix_t *m, int r_idx, vector_elem_t *v, int n);

/*
 * Same thing, with v given as a vector_t
 */
extern int store_vector_in_row(matrix_t *m, int r_idx, vector_t *v);

/*
 * Same thing with v given as a buffer
 */
extern int store_buffer_in_row(matrix_t *m, int r_idx, buffer_t *buffer);



/*
 * Set column of index c_idx equal to v
 * - requires 0 <= c_idx <= m->ncolumns - 1
 *   and all indices in v must be between 0 and m->nrows - 1.
 * - returns -1 and does nothing if that's not true. (not really,
 *   does not check for c_idx < 0).
 * - returns 0 and sets the column otherwise.
 */
extern int store_vectelem_in_column(matrix_t *m, int c_idx, vector_elem_t *v, int n);

/*
 * Same thing, with v given as a vector_t
 */
extern int store_vector_in_column(matrix_t *m, int c_idx, vector_t *v);


/*
 * Same thing, with v given as a buffer
 */
extern int store_buffer_in_column(matrix_t *m, int c_idx, buffer_t *buffer);





/*
 * Clear matrix m: set all columns and rows to 0.
 * Keep the matrix dimensions unchanged.
 */
extern void clear_matrix(matrix_t *m);





/**************************
 *  GAUSSIAN ELIMINATION  *
 *************************/

/*
 * Allocation of a new gauss matrix
 * nrows = initial number of rows
 * ncolumns = initial number of columns
 * The elim structure is not initalized yet.
 * The buffer is not allocated
 */
extern gauss_matrix_t *new_gauss_matrix(int nrows, int ncolumns);

/*
 * Delete matrix m
 */
extern void delete_gauss_matrix(gauss_matrix_t *m);

/*
 * Initialize the elim structure and allocate buffer.
 * This must be called before eliminate_columns or eliminate,
 * after m has been constructed.
 */
extern void gauss_elim_prepare(gauss_matrix_t *m);

/*
 * Construct a triangular submatrix by Gaussian elimination of a set
 * of columns from a matrix m 
 * - array col contains the indices of the columns to eliminate
 * - n = number of elements in col
 */
extern void eliminate_columns(gauss_matrix_t *m, int col[], int n);


/*
 * Clear all rows of m that are in the eliminated row list
 * These rows are detached from the rest of m: they do
 * not occur in the columns.
 */
extern void clear_eliminated_rows(gauss_matrix_t *m);


/*
 * Full Gaussian elimination: construct a maximal triangular
 * submatrix of m.
 */
extern void eliminate_all_columns(gauss_matrix_t *m);





/**************************************************************
 *  COMPACT MATRICES: STORE RESULTS OF GAUSSIAN ELIMINATION   *
 *************************************************************/

/*
 * Create a compact matrix to store the triangular sub-matrix of m
 * (i.e., the matrix formed by m->perm.row_list)
 * Only the rows are stored by this function.
 *
 * Rows are renumbered from 0 to n-1 where n is the length
 * of m->perm.row_list. The diagonal element in each row is stored in
 * first position. Columns are not renumbered. They have the same
 * index in the compact matrix as in m.
 */
extern compact_matrix_t *construct_triangular_row_matrix(gauss_matrix_t *m);


/*
 * Construct the column data for a compact matrix m
 * - assumes that the row data has been set
 */
extern void build_columns(compact_matrix_t *m);


/*
 * Create a compact matrix to store the triangular sub-matrix of m
 * (i.e., the matrix formed by the list of triangle rows)
 * Bot rows and columns are constructed by this function.
 *
 * Rows are renumbered from 0 to n-1 where n is the number of 
 * triangle rows. Columns are not renumbered.
 */
extern compact_matrix_t *construct_triangular_matrix(gauss_matrix_t *m);


/*
 *  Delete a compact matrix
 */
extern void delete_compact_matrix(compact_matrix_t *m);




/*************************
 *  TRIANGULAR MATRICES  *
 ************************/

/*
 * For a square matrix m, one can construct
 * a row-dependency and a column-dependency graph.
 * In column-dependency graph: 
 *   edge i --> j means that j occurs as an index in column i
 *   (i.e., a_ji is non-zero)
 * In row-dependency graph:
 *   edge i --> j means that j occurs as an index in row i
 *   (i.e., a_ij is non-zero).
 *
 * A triangular matrix is a square matrix whose column
 * dependency graph has no circuit (equivalently the 
 * row-dependency graph has no circuit). This means that
 * the matrix can be written in upper or lower triangular 
 * form after a column and row permutation.
 *
 * For solving a linear equations A x = a or y A = b where
 * A is a triangular matrix and a and b are sparse,
 * we use depth-first search in the column-dependency or
 * row-dependency graphs. (Gilbert & Peierls technique).
 * This uses an auxiliary data structure (dfs_t).
 */

/*
 * Allocate an n by n triangular_matrix
 * - the matrix is empty.
 * - diag_row, diag_column, row_dptr, and col_dptr are not allocated.
 */
extern triangular_matrix_t *new_triangular_matrix(int n);


/*
 * Delete triangular matrix m
 */
extern void delete_triangular_matrix(triangular_matrix_t *m);


/*
 * Allocation and initialization of a dfs_t structure
 * for an n by n matrix.
 */
extern dfs_t *new_dfs(int n);


/*
 * Delete dfs structure d
 */
extern void delete_dfs(dfs_t *d);


/*
 * Resize d to accommodate at least n rows or columns
 * - no effect if d is already large enough
 */
extern void resize_dfs(dfs_t *d, int n);


/*
 * Solve equation A x = a for a column vector a
 * and a triangular matrix A (square of dimension n)
 * - input: a is stored in buffer,
 *   stack must be an empty dfs structure of 
 *   size >= dimension of A (i.e. at least n)
 * - output: x is stored in buffer modulo a permutation.
 *   x[i] is stored in buffer->q[diag_row_idx(m, i)]
 *
 * To invert this permutation (i.e., store x[i] in buffer->q[i]), 
 * call permute_buffer(buffer, m->diag_column, ..)
 */
extern void triangular_solve_column(triangular_matrix_t *m, dfs_t *stack, buffer_t *buffer);


/*
 * Solve equation y A = b for a row vector b
 * and a triangular matrix A.
 * - input: b is stored in buffer,
 *   stack must be an empty dfs structure of size >= 
 *   dimension of A (i.e. at least n)
 * - output: y is stored in bufferm modulo a permutation.
 *   y[i] is stored in buffer->q[diag_column_idx(m, i)]
 *
 * To invert the permutation and store y[i] into buffer->q[i],
 * call permute_buffer(buffer, m->diag_row, ...)
 */
extern void triangular_solve_row(triangular_matrix_t *m, dfs_t *stack, buffer_t *buffer);





/****************
 *  ETA FILES   *
 ***************/

/*
 * Creation of an eta file with the given initial capacities
 * - nvectors: initial size of the row_index array
 *             initial size of vindex = nvectors + 1
 * - ncoeffs: initial size of the vblock
 * (Both must be positive)
 */
extern eta_file_t *new_eta_file(int nvectors, int ncoeffs);


/*
 * Delete eta_file f
 */
extern void delete_eta_file(eta_file_t *f);


/*
 * Reset eta_file f: empty it
 * Release all the allocated rationals
 */
extern void reset_eta_file(eta_file_t *f);


/*
 * Operations for incremental construction of a new eta-matrix
 * - start_new_eta_matrix
 * - add_elem_to_eta_matrix or add_neg_elem_to_eta_matrix
 * - close_eta_matrix
 */

/*
 * Start a new eta matrix with row index = r_idx
 */
extern void start_new_eta_matrix(eta_file_t *f, int r_idx);


/*
 * Add pair <i, q> to the open eta matrix.
 */
extern void add_elem_to_eta_matrix(eta_file_t *f, int i, rat_t *q);


/*
 * Add pair <i, - q> to the eta-matrix.
 */
extern void add_neg_elem_to_eta_matrix(eta_file_t *f, int i, rat_t *q);


/*
 * Finish the current eta-matrix
 */
extern void close_eta_matrix(eta_file_t *f);


/*
 * Addition of a new eta-matrix, copied from a vector
 * - r_idx = row index
 * - vector = non-zero elements on the column except diagonal
 */
extern void store_vector_in_eta_file(eta_file_t *f, int r_idx, vector_t *v);


/*
 * Add a new eta-matrix copied from a buffer
 * - r_idx = row index
 * - buffer = buffer that stores the non-zero column elements except the 
 *   diagonal coefficient
 * Assumes buffer is normalized.
 */
extern void store_buffer_in_eta_file(eta_file_t *f, int r_idx, buffer_t *buffer);


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
 */
extern void eta_solve_column(eta_file_t *f, buffer_t *buffer);


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
 */
extern void eta_solve_row(eta_file_t *f, buffer_t *buffer);






/**********************
 *  LU FACTORIZATION  *
 *********************/

/*
 * Delete fact
 */
extern void delete_factorization(factorization_t *fact);



/*
 * Create an initial LU factorization for a compact matrix m.  The
 * function requires m to be already triangularized. This is true if
 * m is constructed via function construct_triangular_matrix and
 * construct_triangular_row_matrix.
 *
 * - the basis is formed by the columns of m that occur in m->col_list:
 *   L is set to the identity matrix and U is a copy of these columns.
 *
 * - the var_col array in the result is the same as m->col_order.
 */
extern factorization_t *create_factorization(compact_matrix_t *m);


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
 * If save_flag is non-zero, the intermediate result z is stored
 * internally (in saved_column vector of fact) to be used in the next
 * LU update.
 *
 * On input, buffer stores vector a, on output, it contains x.
 */
extern void factorization_solve_column(factorization_t *fact, buffer_t *buffer, int save_flag);


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
extern void factorization_solve_row(factorization_t *fact, buffer_t *buffer);



/*
 * Compute an LU factorization of a matrix B formed by a subset of columns of m.
 * - col = array containing the column indices (must have the same
 *   size as the dimension of L or U = fact->dim, and contain disctinct
 *    column indices)
 * - m = matrix whose columns form B.
 * Result:
 * - L and U are stored in fact.
 * - the eta file is emptied.
 *
 * Return code:
 *   0 means matrix B is non-singular. The factorization has succeeded 
 *   and the result is stored in fact.
 *  -1 means that matrix B is singular. Fact contains garbage.
 */
extern int compute_factorization(factorization_t *fact, compact_matrix_t *m, int *col);



/*
 * Update basis B (i.e., replace old_var by new_var) and compute LU
 * factorization.
 * - old_var: variable that leaves the basis
 * - new_var: variable that enters the basis 
 * - m = matrix whose columns form B
 * Result:
 * - L and U such that L U = (B with column of old_var replaced by new_var)
 *   are stored in fact.
 * - the eta file is emptied
 * 
 * Return code:
 * -1 if the factorization fails (new basis is a singular matrix) 
 *  0 otherwise
 * If -1 is returned then fact contains garbage.
 */
extern int update_and_refactor(factorization_t *fact, compact_matrix_t *m, int old_var, int new_var);


/*
 * Update the current factorization:
 * - replace a column of U by the vector in fact->saved_column.
 *   old_var: variable that leaves the basis
 *   new_var: variable that enters the basis
 *   (i.e. column i of U is replaced by saved_column 
 *    where i = fact->var_col[old_var])
 * - let V be the result, then the function computes an elementary
 *   row matrix E_p and an upper-triangular matrix U' such that 
 *   V = E_p \times U'.
 * - U' is stored as the new fact->umatrix
 * - E_p is added as last matrix in the eta file.
 *
 * Return code:
 *   0 means success: V is non-singular
 *  -1 means failure: V is singular
 */
extern int update_factorization(factorization_t *fact, int old_var, int new_var);


#endif /* __MATRICES_H */
