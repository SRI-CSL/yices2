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
 * PRINT SIMPLEX SOLVER STRUCTURES
 */

#ifndef __SIMPLEX_PRINTER_H
#define __SIMPLEX_PRINTER_H

#include <stdio.h>

#include "solvers/simplex/simplex_types.h"


/*
 * Tables of arithmetic variables and atoms
 */
extern void print_arith_vartable(FILE *f, arith_vartable_t *table);
extern void print_arith_atomtable(FILE *f, arith_vartable_t *vtbl, arith_atomtable_t *atbl);


/*
 * Internals of simplex solver
 */
extern void print_matrix(FILE *f, arith_vartable_t *vtbl, matrix_t *matrix);
extern void print_elim_matrix(FILE *f, arith_vartable_t *vtbl, elim_matrix_t *elim);
extern void print_fixed_var_vector(FILE *f, arith_vartable_t *vtbl, fvar_vector_t *fvars);

extern void print_simplex_flags(FILE *f, simplex_solver_t *solver);
extern void print_simplex_vars(FILE *f, simplex_solver_t *solver);
extern void print_simplex_atoms(FILE *f, simplex_solver_t *solver);
extern void print_simplex_row(FILE *f, simplex_solver_t *solver, row_t *row);
extern void print_simplex_matrix(FILE *f, simplex_solver_t *solver);
extern void print_simplex_saved_rows(FILE *f, simplex_solver_t *solver);
extern void print_simplex_basic_vars(FILE *f, simplex_solver_t *solver);
extern void print_simplex_bounds(FILE *f, simplex_solver_t *solver);
extern void print_simplex_assignment(FILE *f, simplex_solver_t *solver);
extern void print_simplex_bounds_and_assignment(FILE *f, simplex_solver_t *solver);
extern void print_simplex_vars_summary(FILE *f, simplex_solver_t *solver);
extern void print_simplex_allvars(FILE *f, simplex_solver_t *solver);

extern void print_simplex_vardef(FILE *f, simplex_solver_t *solver, thvar_t v);
extern void print_simplex_var(FILE *f, simplex_solver_t *solver, thvar_t v);
extern void print_simplex_atom(FILE *f, simplex_solver_t *solver, int32_t id);
extern void print_simplex_atomdef(FILE *f, simplex_solver_t *solver, bvar_t v);
extern void print_simplex_atom_of_literal(FILE *f, simplex_solver_t *solver, literal_t l);
extern void print_simplex_buffer(FILE *f, simplex_solver_t *solver);
extern void print_simplex_bound(FILE *f, simplex_solver_t *solver, uint32_t i);

// value of v in the current assignment
extern void print_simplex_var_value(FILE *f, simplex_solver_t *solver, thvar_t v);

// bounds on v (prints nothing if v has no bounds)
extern void print_simplex_var_bounds(FILE *f, simplex_solver_t *solver, thvar_t v);

/*
 * Print row in a simplified form: replace fixed variables by their value
 */
extern void print_simplex_reduced_row(FILE *f, simplex_solver_t *solver, row_t *row);


/*
 * Print bounds on non-fixed variables
 * Use the same variable names as in dsolver
 */
extern void print_simplex_bounds2(FILE *f, simplex_solver_t *solver);




#endif /* __SIMPLEX_PRINTER_H */
