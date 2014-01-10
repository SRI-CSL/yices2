/*
 * Data structures used in vector and matrix constructions
 * Gaussian elimination/LU factorization.
 *
 * Created 2006/03/06. 
 */

#ifndef __MATRIX_TYPES_H
#define __MATRIX_TYPES_H

#include "rationals.h"



/***********
 * BUFFERS *
 **********/

/*
 * A buffer is an array of rationals (i.e., a dense vector) used for
 * internal computations. 
 *
 * A buffer of dimension n consists of 
 * - an array of n tags
 * - a list of active indices = elements whose tag is different from NO_COEFF
 *
 * The tags indicate which coefficients are non-zero: if buffer->tag[i]
 * is zero than j is not in the active list.
 *
 * If buffer->nelems = k then the active indices are stored
 * in buffer->active[0] ... buffer->active[k-1].
 * If j = buffer->active[i] for j in 0,..., k-1 then buffer->tag[j]
 * is ACTIVE_COEFF. Otherwise, buffer->tag[j] is ZERO_COEFF.
 */

#define ACTIVE_COEFF 1
#define ZERO_COEFF 0

typedef unsigned char mark_t;

typedef struct buffer_s {
  int dim;        // dimension
  int nelems;     // number of active indices
  int *active;    // list of active indices
  rat_t *q;  // coefficients
  mark_t *tag;    // tags
} buffer_t;






/******************
 * SPARSE VECTORS *
 *****************/

/*
 * Element of a vector = a pair <index, coefficient>
 * The coefficient is a rat_t object.
 */
typedef struct vector_elem_s {
  int idx;
  rat_t coeff;
} vector_elem_t;

/*
 * Vector = a header of two integers and an array of elements
 * - size = number of elements currently stored
 * - capacity = size of the array
 */
typedef struct vector_s {
  int capacity;
  int size;
  vector_elem_t data[0];
} vector_t;



/*
 * Default initial size of vectors for automatic allocation
 */
#define DEFAULT_VECTOR_SIZE 10





/**********************
 *   BASIC MATRICES   *
 *********************/

/*
 * A matrix is stored as an array of row vectors.
 * Another array keeps dependency information for each column.
 *
 * Matrix representation
 * ---------------------
 *
 * mat_vector: to represent both rows and columns
 * each element in a mat_vector is a triple <idx, ptr, coeff>
 *
 * If the mat_vector is a row:
 * - if idx >= 0 then the triple is valid:
 *    idx is a column index
 *    ptr is an index in the m_vector corresponding to column idx
 *    coeff is the rational coefficient 
 * - if c_idx < 0, then the element is unused (free). A list of the
 *   free elements is maintained; links are stored in ptr.
 *
 * - for each row r, elements are stored in an array r.data
 *     r.capacity = size of r.data
 *     r.size = index of the last element in the row array
 *     r.nelems = number of elements actually stored.
 *     r.free = start of the free list
 *
 *   We have r.nelems <= r.size <= r.capacity.
 *   All elements are stored at indices between 0 and r.size - 1.
 *   r.free is -1 if the free list is empty; in this case, r.size = r.nelems,
 *   otherwise, r.size = r.nelems + length(free list).
 *
 * Column vector: similar.
 *
 * A (non-zero) element a in row i and column j is stored as follows:
 * - there are two indices i_ptr and j_ptr such that
 *      row[i][i_ptr] = <j, j_ptr, a>
 *   column[j][j_ptr] = <i, i_ptr, a>
 */

/*
 * Default sizes of row vectors and column vectors
 */
#define DEFAULT_ROW_VECTOR_SIZE 10
#define DEFAULT_COLUMN_VECTOR_SIZE 10

/*
 * Default capacity of row and column arrays om a matrix
 */
#define DEFAULT_ROW_CAPACITY 10
#define DEFAULT_COL_CAPACITY 10

/*
 * Row/column vectors of a matrix
 */
typedef struct {
  int idx;
  int ptr;
  rat_t coeff;
} mat_elem_t;

typedef struct {
  int capacity;
  int size;
  int nelems;
  int free;
  mat_elem_t *data;
} mat_vector_t;

/*
 * Simple matrix: arrays of rows and columns
 */
typedef struct {
  int row_cap, column_cap;     // capacity of the vectors of rows/colums
  int nrows, ncolumns;         // actual number of rows and columns
  mat_vector_t *row;           // array of rows
  mat_vector_t *column;        // array of columns
} matrix_t;





/***********************
 *  TRIANGULAR MATRIX  * 
 **********************/

/*
 * Upper or lower-triangular matrices:
 * - a square matrix (stored as a matrix_t)
 * - arrays to store information about the diagonal:
 * - for each row r: diag_column[r] = diagonal column
 *   row_dptr[r] = index of diagonal coefficient in row r
 *   (i.e., k such that m->row[r].data[k] is diagonal coeff)
 * - for each column c: diag_row[c] = diagonal row
 *   col_dptr[c] = index of diagonal coefficient in column c
 */
typedef struct {
  matrix_t m;         // matrix
  int *diag_row;      // maps column idx to row index
  int *diag_column;   // maps row idx to column index
  int *row_dptr;      // diag pointers for rows
  int *col_dptr;      // diag pointers for columns
} triangular_matrix_t;







/****************************************
 *  DOUBLY-LINKED LISTS AND PARTITIONS  *
 ***************************************/

/*
 * Doubly-linked lists for partition and permutations of rows or columns.
 * - for each row or column, we store the indices of its predecessor 
 *   and successor in the list.
 * - a list is built from an array data of list_elem_t
 * - a list is identified by a negative index in the same array.
 *   For example, 
 *     data[-1] = header for list -1
 *     data[-1].next = index of first element in the list
 *     data[-1].pre = index of the last element in the list
 *   (if list -1 is empty, then data[-1].pre = data[-1].next = -1).
 *
 * A partition is an array of lists indexed from 1 to p.
 * Stored internally in data[-p] to data[-1].
 */
typedef struct {
  int pre, next;
} list_elem_t;

typedef struct {
  int list_id;          // negative index
  list_elem_t *data;    // shared array
} list_t;


typedef struct {
  int nelems;           // total number of elements (0 to nelems - 1)  
  int nparts;           // number of lists (indexed -1 to -nparts)
  list_elem_t *data;    // array for lists and elements
} partition_t;





/***************************
 *  PERMUTATION STRUCTURE  *
 **************************/

/*
 * A permutation structure stores a row/column permutation.
 * - col_list = list of columns
 * - row_list = list of rows
 * - size = length of both lists
 * - col_order, row_order = inverse permutation.
 *
 * If a row r is in the permutation, then row_order[r] is
 * its position in row_list. Positions are indexed from 0 to size - 1.
 * Otherwise row_order[r] is -1. Same thing for columns.
 */
typedef struct {
  list_elem_t *col_perm_base;    // for list of columns
  list_t col_list;               // list of columns
  list_elem_t *row_perm_base;    // for list of rows
  list_t row_list;               // list of rows
  int size;                      // size of both lists
  int *col_order;                // position in col_list
  int *row_order;                // position in row_list
} permutation_t;





/*******************************************
 *  DATA STRUCTURE FOR PIVOTING HEURISTIC  *
 ******************************************/

/*
 * Pivoting uses Markowitz's heuristic:
 * - during Gaussian elimination and LU factorization, pivot element
 *  m[r,c] is chosen so as to minimize (row_count[r] - 1) * (col_count[c] - 1)
 *  where row_count = number of non-zeros in row r,
 *        col_count = number of non-zeros in column c.
 *
 * For matrix simplification, Gaussian elimination is partial and applies
 * to selected columns. This is indicated by setting row_count or col_count
 * to negative values for the rows or columns to keep.
 * 
 * The rows and columns of non-negative count are stored in a row/column partition.
 * The partition is an array N+1 lists. For rows, we have:
 *     list 0 = rows r such that row_count[r] = 0 
 *     list 1 = rows such that row_count[r] = 1
 *     ..
 *     list N - 1 = .... row_count[r] = N-1
 *     list N = rows such that row_count[r] >= N (last list)
 *
 * Same thing for the column partition
 */

// Size of the row and column partitions = N = number of lists - 1
#define PARTITION_SIZE 20

// Tags for col_count/row_count
#define PTAG_EMPTY   -1
#define PTAG_TO_KEEP -2

typedef struct {
  partition_t row_partition;  
  partition_t col_partition;
  int *row_count;
  int *col_count;
} pivoter_t;




/***********************
 * ELIMINATION MATRIX  *
 **********************/

/*
 * Matrix + data structures for performing Gaussian elimination
 * - after Gaussian elimination, row_dptr and col_dptr are
 * set to record the diagonal elements.
 * (changed: col_dptr is not used)
 */
typedef struct {
  matrix_t m;          // the matrix itself

  permutation_t perm;  // row/column permutation
  pivoter_t pv;        // data for pivoting heuristic 

  int *row_dptr;      // diag pointers for rows

  buffer_t *buffer;    // buffer for row operations
  rat_t r0;            // register for row elimination
} gauss_matrix_t;



/*********************
 *  COMPACT MATRIX   *
 ********************/

/*
 * Vector array (used to store an array of rows or columns in a compact format).
 * - nvectors = number of vectors in the array
 * - vindex = array of indices between 0 and nvectors
 * - vblock = array of pairs <index, coefficient> 
 *
 * The vblock stores all the vectors contiguously: vector i: is stored
 * in vblock at indices between vindex[i] and vindex[i+1] - 1.
 */
typedef struct {
  int nvectors;
  int *vindex;
  vector_elem_t *vblock;
} vector_array_t;


/*
 * Compact matrix for storing upper triangular matrices or 
 * "upper trapezoidal" matrices (result of Gaussian elimination).
 * 
 * - two vector arrays, one for the rows and one for the colums
 *   (the column array is optional).
 * 
 * - diagonal representation
 *     diag_size = size of the diagonal (normally, the number of rows).
 *     col_list = array of diag_size column indices
 * - col_list stores a permutation of columns on the diagonal:
 *     col_list[0] = index of the first column
 *     ...
 *     col_list[i] = index of the (i+1)-th column
 * - rows are stored in the diagonal order: row of index 0 is the fist row, etc.
 * 
 * - col_order = array of ncolumns integers
 *   if column c is on the diagonal, then col_order[c] = its position 
 *   (so we have col_list[i] = c  and col_order[c] = i).
 *   otherwise col_order[c] is -1.
 *
 */
typedef struct compact_matrix_s {
  int nrows;          // number of rows (rows are indexed from 0 to nrows - 1)
  int ncolumns;       // number of columns (indexed from 0 to ncolumns - 1)
  int vsize;          // total number of non-zero elements
  int diag_size;      // diagonal 
  int *col_list;     // column permutation
  int *col_order;    // inverse permutation or free flag
  vector_array_t rows;    // compact row array
  vector_array_t columns; // compact column array (may be unused).

} compact_matrix_t;










/*********
 * STACK *
 ********/

/*
 * Stack/list for DFS search in matrix row/column
 * - used for solving linear equation with triangular matrices
 * - the stack is made of three arrays
 *       index array = row or column index
 *       vector array = mat_elem_t vector (either a row or a column)
 *       counter array = index in vector
 * - the list is represented by array next and index head
 * 
 * Special markes:
 * - end of list is -1.
 * - for an element i not in the list or stack, next[i] = -2 
 * - for an element i on the stack but not in the list, next[i] = -3
 */
#define END_OF_LIST -1
#define NOT_IN_LIST -2
#define ON_STACK    -3

typedef struct {
  int size;       // size of stack and list
  int top;        // top of the stack, -1 if the stack is empty
  int head;
  int *next;
  int *index;
  int *counter;
  mat_elem_t **vector;
} dfs_t;




/****************
 *  ETA FILES   *
 ***************/

/*
 * An eta file represents the product of p elementary row matrices
 *   E_0 \times ... \times E_{p-1}
 *
 * Each E_i is a square matrix of size n.
 * 
 * E_i is defined by a row index k and a vector (a_k1,\ldots,a_kn)
 * that defines row k of E_i, with a_kk = 1. The rest of E_i is 0,
 * except that all diagonal elements are 1.
 *
 * Data structure used:
 * - nvectors = p = number of elementary matrices
 * - for every i between 0 and p-1,
 *     row_index[i] = k = row index for E_i
 * - the non-zero elements of (a_k1,\ldots,a_kn), except a_kk,
 *   are stored as pairs <column-index, coefficients> in a global 
 *   vblock:
 * - if vindex[i] = t and vindex[i+1] = u then the 
 *   row elements for E_i are stored in vblock[t] ... vblock[u-1] 
 *   (in no particular order)
 * - each vblock[k] element stores a pair <row-index, coefficient>
 *   where coefficient a rational.
 */
typedef struct {
  int vector_capacity;    // size of the row_index array
  int vblock_capacity;    // size of the vblock array
  int nvectors;           // current number of vectors
  int ncoeffs;            // current number of pairs <index/coeff>
  int *row_index;         // row indices
  int *vindex;            // start of each eta-vector in vblock
  vector_elem_t *vblock;  // array of pairs <index/coefficients>
} eta_file_t;


// Default initial size of an eta file
#define DEFAULT_ETA_NVECTORS 100
#define DEFAULT_ETA_NCOEFFS  200
 


/**********
 *  BUMP  *
 *********/

/*
 * Bump structure used for updating LU factorizations.
 * It's used to support Reid's technique for reducing 
 * the work before applying Forrst-Tomlin update (called
 * "Shrinking the Bump" in Vanderbei's book).
 *
 * The bump is a submatrix of a square matrix U formed by 
 * the elements (r, c) such that
 *     pos_start <= col_order[c] <= pos_end
 *     pos_start <= row_order[r] <= pos_end,
 * where col_order and row_order define permutations of rows and columns of U.
 * (from a permutation_t structure).
 *
 * - c_idx_start is the column index of position pos_start
 * - c_idx_end is the column index of position pos_end
 * - r_idx_start is the row index of position pos_start = diagonal of c_idx_start 
 * - r_idx_start is the row index of position pos_end = diagonal of r_idx_start
 */
typedef struct {
  int pos_start, pos_end;
  int c_idx_start, c_idx_end;
  int r_idx_start, r_idx_end;
} bump_t;



/********************
 *  FACTORIZATION   *
 *******************/
/*
 * A factorization represents a non-singular matrix B as a product
 * B = L \times (E_0 \times .. \times E_{p-1}) \times U, where
 * - L and U are triangular matrices.
 * - E_0 \times ... \time E_{p-1} is stored as an eta file
 *
 */
typedef struct {
  int nvars;          // number of variables (columns in simplex tableau)
  int dim;            // dimension = number of rows in tableau
  int *var_col;       // maps basic variables to their column index in U

  triangular_matrix_t lmatrix; // L 
  triangular_matrix_t umatrix; // U
  eta_file_t f;                // E_0 \times ... E_{p-1}

  permutation_t perm;  // row/column permutation
  pivoter_t pv;        // data for pivoting heuristic 
  dfs_t stack;         // dfs structure for solving equations
  bump_t bmp;          // bump structure for updates

  vector_t *saved_column;  // new column of U

  // general buffer and register for LU computations
  buffer_t *buffer;
  rat_t r0;
} factorization_t;



#endif /* __MATRIX_TYPES_H */
