/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * Print functions for diophantine solver
 */

#ifndef __DSOLVER_PRINTER_H
#define __DSOLVER_PRINTER_H

#include <stdint.h>
#include <stdio.h>

#include "solvers/simplex/diophantine_systems.h"
#include "solvers/simplex/matrices.h"


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



#endif /* __DSOLVER_PRINTER_H */
