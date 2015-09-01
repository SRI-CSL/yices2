/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Solver for systems of linear diophantine equations
 *
 * References: Chou & Collins, 1982
 *             Rosser, 1941
 *             Rosser, 1952
 *
 * Input:
 * - an integer matrix A (m rows, n columns)
 * - an integer vector b (of dimension m)
 *
 * Goals:
 * 1) check whether the system of equations  A x + b = 0
 *    has integer solutions and if so find one
 * 2) if there are no solutions, find an explanation
 * 3) find the general solution x = b_0 + c_1 z_1 + ... + c_k z_k
 *    where
 *     { c_1, ..., c_k } are k vectors that form a basis
 *        of the lattice L = { x | A x = 0 }
 *    and z_1, ..., z_k are k integer parameters
 *
 * Algorithm
 * ---------
 * Search for a matrix C and a unimodular matrix U such that
 *     C = A U and C is in echelon form.
 *
 * Unimodular means that the coefficients of U are integer
 * and det(U) is +1 or -1.
 *
 * Echelon form means that C looks like this
 *   c_11 0    .............. 0
 *   c_21 c_22 0 ............ 0
 *     ...
 *   c_m1 c_m2 ... c_m,m 0 .. 0
 *
 * (provided C has rank m).
 *
 * Solving C y = b is equivalent to solving A x = b:
 * 1) if y is a solution to (C y = b) then x = U y is a
 *    solution to (A x = b)
 * 2) if x is a solution to (A x = b) then y = U^{-1} x is an
 *    integer solution to (C y = b)
 *
 * Since C is in echelon form, solving C y = b is easy.
 *
 * Trick to compute C and U
 * ------------------------
 * - build a larger matrix D (m+n rows, n columns) by joining C and U
 * - extend b into an (m+n) vector B
 * - initially:
 *
 *      D = [ A ]      B = [b]
 *          [ I ]          [0]
 *
 *   where I is the n x n identity matrix.
 *
 * - turn the upper part of D into an echelon matrix by applying
 *   elementary column transformations.
 * - these transformations are one of the following operations:
 *    1) negate a column of D
 *    2) swap two columns of D
 *    3) add an integer multiple of a column of D to another column of D
 * - other operation:
 *    4) add an integer multiple of a column of D to B
 *
 * The algorithm operates then on D and B of the following form
 *
 *      D = [ C ]      B = [f]
 *          [ U ]          [g]
 *
 * and all transformations preserve the following invariants:
 *
 *    1) U is unimodular
 *    2) C = A U
 *    3) f = A g + b
 *
 * The problem is solved when we reach a state where f = 0
 * (then g is a solution to A x + b = 0) and C is in echelon form.
 * The problem is unsat if there's an unsat row in C (which can be easily
 * checked).
 *
 * If C is in echelon form, then the last k columns of C are zero.
 * The corresponding k columns of U = u_1, ..., u_k form a basis of
 * the set of vectors x such that A x = 0. So the general solution is
 *  x =  g + u_1 z_1 + ... + u_k z_k.
 *
 * Rosser's algorithm
 * ------------------
 * We can't just apply arbitrary column transformations in any order.
 * If we're not careful, the coefficients in matrix D grow exponentially.
 * Rosser's algorithm is a way of controlling coefficient growth.
 *
 */

/*
 * DATA STRUCTURES
 *
 * The solver stores a matrix A and a column vector B.
 * - A is stored as an array of columns
 * - B is a single column
 *
 * The dimensions are stored as
 * - solver->ncolumns = number of columns of A
 * - solver->nrows = number of rows of A = size of B
 *
 * Main components of a solver:
 * - solver->columns = columns of A
 * - solver->constant_column = vector B
 * - solver->rows = dependencies for row i = an array of column indices
 *
 * We use a sparse representation: only the non-zero elements of A
 * and B are stored. If A[i, j] is not zero then
 * - solver->row[i] contains column index j
 * - solver->column[j] contains the entry [i, k, coeff]
 *     where k = integer such that solver->row[i][k] = j
 *       coeff = A[i, j] stored as a rational number
 *
 * Variables
 * ---------
 * When the matrix A is constructed, each column of A is mapped to an
 * external variable x. Conversely, for each variable x, we store the
 * corresponding column index in array solver->col_idx[x]. If x does not
 * occur, then solver->col_idx[x] = -1.
 *
 * After the system is solved, solver->sol_row[x] stores a row index where
 * the solution for x can be recovered.
 *
 * External row ids
 * ----------------
 * Internally, rows are numbered from 0 to nrows - 1.
 * To interact with the simplex solver, each row of A is assigned an
 * external id (which corresponds to a row index in the simplex matrix/tableau).
 * For i between 0 and nrows - 1, row_id[i] stores the external id.
 *
 * Simplification
 * --------------
 * If coefficient A[i, j] is either +1 or -1, and all other elements of
 * column j are zero, then we can remove row i and column j from the system.
 * The row denotes an equation a_i1 x_1 + ... + a_ij x_j + ... + b_i = 0,
 * where a_ij is +1 or -1. We can then solve for x_j and remove the row (and the column).
 * The corresponding substitution x_j := - a_ij (a_i1 x_1 + ... + ... + b_i) is stored
 * in an elimination record as a pair <variable, polynomial>.
 *
 *
 * Rosser's algorithm
 * ------------------
 * To solve the system: we keep three sets of columns
 * - A = active columns = matrix A as above
 * - S = solved columns = left-hand part of the echelon matrix = columns
 * - C = auxiliary set used during processing
 *
 * Initially: S and C are empty, A is the full set of columns
 *
 * Rosser's algorithm:
 * - choose a row i not eliminated yet
 * - C := columns of A where row_index i occurs with a non-zero coefficient.
 * - A := A - C
 * - for each c in C, let c[i] denote the coefficient of row_i in column c
 * - if c[i] is negative, replace c by -c in C
 * - reduction:
 *     while C has at least two columns,
 *       let c_1 be the column with largest coefficient c_1[i]
 *           c_2 be the column with second largest coefficient c_2[i]
 *         remove c_1 from C;
 *         compute c'_1 :=  c_1 - k c_2 where k = (c_1[i] div c_2[i])
 *         if c'_1[i] != 0 then
 *           add c'_1 back to C
 *         else
 *           add c'_1 back to A
 *         endif
 *     end
 * - now C contains a single column c with c[i] != 0, let b[i] be the corresponding
 *   coefficient in the constant vector b.
 *   if b[i] is a multiple of c[i] then
 *      replace b by b - k.c where k = (b[i]/c[i])
 *      add c to S
 *      reset C to emptyset
 *      iterate with a new row j
 *   else
 *      the system is unsat
 *   endif
 *
 * NOTE: the description above is not quite right. It's much better to
 * reduce the constant column by c1 inside the loop, rather than doing
 * it once at the end.
 *
 * Heuristic to select the rows: process the sparser row first.
 */

#ifndef __DIOPHANTINE_SYSTEMS_H
#define __DIOPHANTINE_SYSTEMS_H

#include <assert.h>
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#include "terms/poly_buffer.h"
#include "terms/polynomials.h"
#include "terms/rationals.h"
#include "utils/generic_heap.h"
#include "utils/int_heap2.h"
#include "utils/int_vectors.h"
#include "utils/ptr_heap.h"


/*
 * Column element:
 * - coefficient + row index + row pointer
 * - the coefficient is stored as a rational_t object
 * - a column may be detached from the matrix, in which case, r_ptr is
 *   not used.
 * - if a column j if attached to the matrix, then for every element [i, k, coeff]
 *   of the column, we have row[i][k] = j.
 */
typedef struct dcol_elem_s {
  int32_t r_idx;
  int32_t r_ptr;
  rational_t coeff;
} dcol_elem_t;


/*
 * Column = an array of column element + header
 * - the elements are stored in increasing r_idx
 * - there's an end marker of index max_idx = INT32_MAX
 *   (max_idx is defined in polynomial_manager.h)
 * Header:
 * - one element may be selected as the active element
 *   in a column. In that case, active is its index in
 *   the data array, otherwise active is -1.
 * - var = variable attached to the column (or -1) for the constant vector
 */
typedef struct dcolumn_s {
  int32_t active;      // -1 or index between 0 and nelems
  int32_t var;         // variable corresponding to this column
  uint32_t size;       // size of the data array
  uint32_t nelems;     // number of elements in use, excluding the end marker
  dcol_elem_t data[0];
} dcolumn_t;


#define DEF_DCOLUMN_SIZE 10
#define MAX_DCOLUMN_SIZE ((((size_t) UINT32_MAX)-sizeof(dcolumn_t))/sizeof(dcol_elem_t))


/*
 * Elimination records: store (x := poly) where x does not occur in poly
 * also keep track of the row from which the elimination record was built.
 */
typedef struct delim_record_s {
  int32_t var;
  int32_t source; // row index
  polynomial_t *poly;
} delim_record_t;

/*
 * All eliminated rows are stored in a vector
 */
typedef struct delim_vector_s {
  uint32_t size;
  uint32_t nelems;
  delim_record_t *data;
} delim_vector_t;


#define DEF_DELIMVECTOR_SIZE 10
#define MAX_DELIMVECTOR_SIZE (UINT32_MAX/sizeof(delim_record_t))




/*
 * Status flags: record the solver state
 * - READY: rows can be added
 * - TRIVIALLY_UNSAT: a row (b == 0) was added
 * - GCD_UNSAT: a row was added that failed the GCD test
 * - SIMPLIFIED: after simplifications (row elimination)
 * - SEARCHING: on entry to dsolver_is_feasible
 * - SOLVED_SAT: the system was solved and a solution was found
 * - SOLVED_UNSAT: the system has been solved and it's not SAT
 * - UNSOLVED: the solver gave up (search was too expensive)
 * - INTERRUPTED: the search was stopped
 * For all UNSAT states, then unsat_row is the internal index of a row
 * where unsatisfiability was detected. For GCD_UNSAT or TRIV_UNSAT, this is
 * the last inconsistent row added.
 */
typedef enum dsolver_status {
  DSOLVER_READY,
  DSOLVER_TRIV_UNSAT,
  DSOLVER_GCD_UNSAT,
  DSOLVER_SIMPLIFIED,
  DSOLVER_SEARCHING,
  DSOLVER_SOLVED_SAT,
  DSOLVER_SOLVED_UNSAT,
  DSOLVER_UNSOLVED,
  DSOLVER_INTERRUPTED,
} dsolver_status_t;



/*
 * Full solver
 */
typedef struct dsolver_s {
  /*
   * Dimensions
   */
  uint32_t vsize;     // size of the variable-indexed arrays
  uint32_t nvars;     // number of variables
  uint32_t rsize;     // size of the row-indexed arrays
  uint32_t nrows;     // number of rows
  uint32_t csize;     // size of the column-indexed arrays
  uint32_t ncolumns;  // number of columns

  /*
   * Active row or row under construction (or -1)
   */
  int32_t active_row;


  /*
   * Counters used when solving the equations:
   * - number of solved rows/columns
   * - number of main rows = rows in the input system, before the
   * identity matrix is adjoined.
   */
  uint32_t nsolved;
  uint32_t main_rows;


  /*
   * Statistics: number of reduce_column operations
   */
  uint32_t num_reduce_ops;
  uint32_t num_process_rows;

  /*
   * Size estimates:
   * - max_coeff_size = approximately the number of bits in
   *   the largest coefficient of the matrix.
   * - max_column_size = largest column
   */
  uint32_t max_coeff_size;
  uint32_t max_column_size;

  /*
   * Status and unsat-row index
   */
  dsolver_status_t status;
  int32_t unsat_row;

  /*
   * Flag for construction of new rows
   */
  bool all_coeffs_integer;

  /*
   * Variable data: arrays of vsize elements
   */
  int32_t *col_idx;
  int32_t *sol_row;

  /*
   * Row data:
   * - row_id[r] = external index for the row
   * - row[r] = array of column indices j such that A[r, j] != 0
   *   (row[r] is represented as an int_bag)
   */
  int32_t *row_id;
  int32_t **row;

  /*
   * Matrix/column data
   */
  dcolumn_t **column;             // matrix A is stored as columns[0 ... ncolumns - 1]
  dcolumn_t *constant_column;     // constant B

  /*
   * Structures used during solving
   */
  dcolumn_t *aux_column;          // auxiliary column used in computations
  delim_vector_t elim;            // eliminated rows and variables
  dcolumn_t **solved_columns;     // solved columns (set S above)
  ptr_heap_t active_columns;      // the set C above sorted in decreasing c[i] order
  generic_heap_t rows_to_process; // rows sorted in increasing row-count order

  /*
   * Auxiliary buffers
   */
  rational_t reduce_factor;       // integer coefficient in C'_i = C_i - reduce_factor * C_j
  rational_t lcm;                 // lcm of denominators (used when normalizing rows)
  rational_t gcd;                 // gcd of numerators (used when normalizing rows)
  ivector_t  aux_vector;          // general-purpose array of integers

  /*
   * Structures to store solutions
   * - arrays base_sol and gen_sol are allocated on demand, after solving the system
   * - their size is equal to nvars
   * - for a variable x,
   *   base_sol[x] = solution for variable x as a rational
   *              (or zero if x does not occur in the equations)
   *   gen_sol[x] = "generic solution" for x as a polynomial
   *              (or NULL if x does not occur in the equations)
   * - the variables of gen_sol[x] are integer parameters
   *
   * Parameter numbering: when constructing the general solutions, the parameters are
   * given a variable index in the range [nvars, .., nvars + k-1] (so that they don't clash
   * with the problem variables in [0 ... nvars-1]).
   * - if column[c] is not a solved or eliminated column then param_id[c] is the parameter
   *   id for column c.
   * - otherwise, column[c] is NULL and param_id[c] is -1.
   * - num_params is the number of non-NULL columns = number of parameters.
   *
   * NOTE: param_id and num_params are computed when the generic solution is constructed.
   * - num_params is not meaningful until then
   */
  rational_t *base_sol;
  polynomial_t **gen_sol;
  int32_t *param_id;
  uint32_t num_params;

  /*
   * Structures for building explanations
   * - they are allocated on demand, after solving, if an explanation
   * is requested.
   */
  poly_buffer_t *aux_buffer2;
  poly_buffer_t *aux_buffer;
  int_heap2_t *aux_heap;

} dsolver_t;



#define DEF_DSOLVER_RSIZE 60
#define MAX_DSOLVER_RSIZE MAX_DCOLUMN_SIZE

#define DEF_DSOLVER_VSIZE 60
#define MAX_DSOLVER_VSIZE (UINT32_MAX/sizeof(dcolumn_t *))

#define DEF_DSOLVER_CSIZE 20
#define MAX_DSOLVER_CSIZE (UINT32_MAX/sizeof(dcolumn_t *))

#define DEF_DSOLVER_AUXSIZE 10


/*
 * INITIALIZATION
 */

/*
 * Initialization: prepare empty solver
 * - n = initial rsize (if n = 0, the default size is used)
 * - m = initial vsize (if m = 0, the default size is used)
 * - p = initial csize (if p = 0, the default size is used)
 */
extern void init_dsolver(dsolver_t *solver, uint32_t n, uint32_t m, uint32_t p);


/*
 * Delete: free all memory
 */
extern void delete_dsolver(dsolver_t *solver);


/*
 * Reset to the empty solver.
 */
extern void reset_dsolver(dsolver_t *solver);



/*
 * ADD EQUATIONS
 */

/*
 * Prepare a new equation (i.e., a new row)
 * - id = the external row id
 * - return the internal index for that row
 * There should be no row under construction and the solver status should be READY.
 * The new row is initially empty (constant = 0, no monomials).
 */
extern int32_t dsolver_row_open(dsolver_t *solver, int32_t id);

/*
 * Add monomial a.x to the current row (i.e., the one initialized
 * by the previous call to row_open).
 * - a = coefficient (can be rational)
 * - x = variable
 * If the current row contains a monomial b.x with the same variable,
 * then it's replaced by (a+b).x
 *
 * IMPORTANT: x must be positive, since 0 is used as a marker for
 * constants in polynomials.
 */
extern void dsolver_row_add_mono(dsolver_t *solver, rational_t *a, int32_t x);

/*
 * Add constant a to the current row constant
 */
extern void dsolver_row_add_constant(dsolver_t *solver, rational_t *a);

/*
 * Add constant a * b to the current row constant
 */
extern void dsolver_row_addmul_constant(dsolver_t *solver, rational_t *a, rational_t *b);


/*
 * Close the current row and check local consistency
 * - turn all coefficients to integers and remove the zero coefficients if any.
 * - remove common factors from the coefficients (divide by the GCD)
 * - add the normalized row to the system of equation.
 * - return true if the row is consistent, false otherwise
 *
 * The row is locally inconsistent if either it's of the form
 * b == 0 where b is a nonzero constant or it fails the GCD test,
 * (i.e., it's of the form a_1 x_1 + ... + a_n x_b + b == 0,
 * where a_1, ..., a_n are non-zero integer and b is not integer).
 */
extern bool dsolver_row_close(dsolver_t *solver);



/*
 * Read the status and unsat row (unsat_row == -1 means no unsat row).
 */
static inline dsolver_status_t dsolver_status(dsolver_t *solver) {
  return solver->status;
}

static inline int32_t dsolver_unsat_row(dsolver_t *solver) {
  return solver->unsat_row;
}

// convert to the external index
static inline int32_t dsolver_unsat_row_id(dsolver_t *solver) {
  int32_t k;
  k = solver->unsat_row;
  return k < 0 ? -1 : solver->row_id[k];
}



/*
 * SIMPLIFICATION
 */

/*
 * Eliminate all rows of the form a_1 x_1 + ... + a_n x_n + b = 0
 * where a_i = +/-1 and x_i does not occur in any other row.
 * Store the eliminated variable's definition in an elimination record
 * The solver status must be READY, and it's moved to SIMPLIFIED.
 */
extern void dsolver_simplify(dsolver_t *solver);




/*
 * SOLVING
 */

/*
 * Check for satisfiability of the system.
 * - the solver status must be either READY or SIMPLIFIED
 * - returned code is the status:
 *   DSOLVER_SOLVED_SAT if the system is satisfiable
 *   DSOLVER_SOLVED_UNSAT if the system is unsat
 *   DSOLVER_UNSOLVED if the search is too expensive
 *   DSOLVER_INTERRUPTED if the call is interrupted
 * 
 * - if the search is not interrupted other functions below can be
 *   used after this to get a model or an explanation of
 *   unsatisfiability.
 */
extern dsolver_status_t dsolver_is_feasible(dsolver_t *solver);


/*
 * STOP THE SEARCH
 */

/*
 * If dsolver_is_fesible was called, then this function can be called
 * from an interrupt handler to stop it. It sets solver->status to
 * INTERRUPTED.
 */
static inline void dsolver_stop_search(dsolver_t *solver) {
  if (solver->status == DSOLVER_SEARCHING) {
    solver->status = DSOLVER_INTERRUPTED;
  }
}


/*
 * GET MODEL
 */

/*
 * Build the solution (as a mapping from variables to rationals)
 * - the solver status must be SOLVED_SAT
 * - solver->base_sol[x] is zero for all variables not occurring in the solver
 * - solver->base_sol[0] is one (0 is the constant index)
 * - otherwise, solver->base_sol[x] is the solution found for x
 */
extern void dsolver_build_solution(dsolver_t *solver);


/*
 * Read the value assigned to x in the solution
 * - dsolver_build_solution must be called first
 */
static inline rational_t *dsolver_get_value(dsolver_t *solver, int32_t x) {
  assert(0 <= x && x < solver->nvars && solver->base_sol != NULL);
  return solver->base_sol + x;
}


/*
 * Build the general solution (as a mapping from variables to polynomials)
 * - the solver status must be SOLVED_SAT
 * - solver->gen_sol[x] is NULL for all variable not occurring in the solver
 * - solver->gen_sol[0] is the constant 1 polynomial
 * - solver->param_id[c] is set if column c is not eliminated
 * - solver->num_params is computed here
 * - otherwise, solver->gen_sol[x] is a polynomial
 *   the form b + a_1 i_1 + ... + a_t i_t
 *   where i_1 ... i_t are integer parameters.
 */
extern void dsolver_build_general_solution(dsolver_t *solver);


/*
 * Read the polynomial assigned to x in the generic solution
 * - build_generic_solution must be called first
 */
static inline polynomial_t *dsolver_gen_sol(dsolver_t *solver, int32_t x) {
  assert(0 <= x && x < solver->nvars && solver->gen_sol != NULL);
  return solver->gen_sol[x];
}

/*
 * Read the number of parameters
 * - dsolver_build_general_solution must be called first.
 */
static inline uint32_t dsolver_num_parameters(dsolver_t *solver) {
  return solver->num_params;
}

/*
 * Get the general solution as an array
 */
static inline polynomial_t **dsolver_get_gen_sol(dsolver_t *solver) {
  return solver->gen_sol;
}

/*
 * Check whether variable x is relevant in solver (i.e., if it has a
 * polynomial in the general solution).
 * - x must have an index in the range 1 to nvars - 1
 */
static inline bool dsolver_var_is_relevant(dsolver_t *solver, int32_t x) {
  assert(1 <= x && x < solver->nvars && solver->gen_sol != NULL);
  return solver->gen_sol[x] != NULL;
}



/*
 * EXPLANATIONS
 */

/*
 * Compute an inconsistent set of rows
 * - the solver status must be either TRIV_UNSAT, GCD_UNSAT, or SOLVED_UNSAT
 * - the external ids of the rows in this set are added to vector v
 *   (v is not reset)
 */
extern void dsolver_unsat_rows(dsolver_t *solver, ivector_t *v);


/*
 * Compute a set of rows that explains the solution for a variable x
 * - the solver status must be SOLVED_SAT
 * - the external row ids are added to vector v
 */
extern void dsolver_explain_solution(dsolver_t *solver, int32_t x, ivector_t *v);




/*
 * OTHER FUNCTIONS USED FOR TESTING
 */

/*
 * Make a copy of the constant column then clear it.
 * the resulting system is always satisfiable.
 * - return the copy
 */
extern dcolumn_t *dsolver_save_and_clear_constant_column(dsolver_t *solver);

/*
 * Restore the constant column to c
 * - must be the column returned by the previous operation
 */
extern void dsolver_restore_constant_column(dsolver_t *solver, dcolumn_t *c);

/*
 * Put back the solved columns into the whole system
 */
extern void dsolver_restore_solved_columns(dsolver_t *solver);





#endif /* __DIOPHANTINE_SYSTEMS_H */
