/*
 * Print functions for diophantine solver
 */

#ifndef __DSOLVER_PRINTER_H
#define __DSOLVER_PRINTER_H

#include <stdint.h>
#include <stdio.h>

#include "matrices.h"
#include "diophantine_systems.h"
#include "mini_simplex.h"


/*
 * Print the solver status
 */
extern void dsolver_print_status(FILE *f, dsolver_t *solver);


/*
 * Print the active row = row under construction
 */
extern void dsolver_print_active_row(FILE *f, dsolver_t *solver);


/*
 * Print row k
 * - k must be a valid row index (i.e., 0 <= k < solver->nrows)
 */
extern void dsolver_print_row(FILE *f, dsolver_t *solver, int32_t k);


/*
 * Print elimination record k
 * - k must be a valid index (0 <= k < solver->elim.nelems)
 */
extern void dsolver_print_elim_record(FILE *f, dsolver_t *solver, int32_t k);


/*
 * Print the system of equations (all rows)
 */
extern void dsolver_print_rows(FILE *f, dsolver_t *solver);


/*
 * Print the system of equations:
 * - skip the empty rows
 * - print only the main rows
 */
extern void dsolver_print_main_rows(FILE *f, dsolver_t *solver);


/*
 * Print all eliminated rows
 */
extern void dsolver_print_elim_rows(FILE *f, dsolver_t *solver);


/*
 * Print the solution or elim row for variable x
 */
extern void dsolver_print_sol_row(FILE *f, dsolver_t *solver, int32_t x);


/*
 * Print all solution rows (bottom part of the matrix)
 */
extern void dsolver_print_sol_rows(FILE *f, dsolver_t *solver);


/*
 * Print the list of rows to process
 */
extern void dsolver_print_rows_to_process(FILE *f, dsolver_t *solver);


/*
 * Print the solved columns
 */
extern void dsolver_print_solved_columns(FILE *f, dsolver_t *solver);



/*
 * Print the solution
 */
extern void dsolver_print_solution(FILE *f, dsolver_t *solver);


/*
 * Print the general solution
 */
extern void dsolver_print_gen_solution(FILE *f, dsolver_t *solver);


/*
 * Print a matrix or tableau with the same variable naming convention
 * as in dsolver:
 * - a variable k of index 1 ... m-1 is printed as x_<k>
 * - a variable k of index m ... is printed as i_<k> (i.e., as a parameter)
 */
extern void dsolver_print_tableau(FILE *f, matrix_t *matrix, int32_t param_idx);


/*
 * Same thing for the tableau in a simplex solver s
 */
static inline void dsolver_splx_print_tableau(FILE *f, mini_simplex_t *s) {
  fputs("--- Tableau ---\n", f);
  dsolver_print_tableau(f, &s->matrix, s->nvars);
  fputc('\n', f);
}


/*
 * Print varibable x
 */
extern void dsolver_splx_print_var(FILE *f, mini_simplex_t *s, int32_t x);


/*
 * Print the current assigmment in simplex solver s
 */
extern void dsolver_splx_print_solution(FILE *f, mini_simplex_t *s);


/*
 * Print the asserted bounds in simplex solver s
 */
extern void dsolver_splx_print_bounds(FILE *f, mini_simplex_t *s);


/*
 * Print assignment and bounds in a more compact format
 */
extern void dsolver_splx_print_sol_and_bounds(FILE *f, mini_simplex_t *s);



/*
 * Print the status of simplex solver s
 * + a summary explanation if status is a conflict
 */
extern void dsolver_splx_print_status(FILE *f, mini_simplex_t *s);


/*
 * Print the list of infeasible vars
 */
extern void dsolver_splx_print_infeasible_vars(FILE *f, mini_simplex_t *s);



#endif /* __DSOLVER_PRINTER_H */
