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
 * PRINT BVSOLVER STRUCTURES
 */

#ifndef __BVSOLVER_PRINTER_H
#define __BVSOLVER_PRINTER_H

#include <stdio.h>

#include "solvers/bv/bvsolver_types.h"


/*
 * Tables of bitvector variable and atoms
 */
extern void print_bv_vartable(FILE *f, bv_vartable_t *vtbl);
extern void print_bv_atomtable(FILE *f, bv_atomtable_t *atbl);


/*
 * Fully expanded forms: n = number of bits
 */
extern void print_bvexp64(FILE *f, bvmlist64_t *p, uint32_t n);
extern void print_bvexp(FILE *f, bvmlist_t *p, uint32_t n);


/*
 * All variables and atoms in solver
 */
extern void print_bv_solver_vars(FILE *f, bv_solver_t *solver);
extern void print_bv_solver_atoms(FILE *f, bv_solver_t *solver);


/*
 * Variable partitions (in merge table)
 */
extern void print_bv_solver_partition(FILE *f, bv_solver_t *solver);


/*
 * Bounds in the queue
 */
extern void print_bv_solver_bounds(FILE *f, bv_solver_t *solver);


/*
 * DAG/Compiler
 */
extern void print_bvc_dag(FILE *f, bvc_dag_t *dag);
extern void print_bv_solver_dag(FILE *f, bv_solver_t *solver);


/*
 * Individual variable or atom
 */
extern void print_bv_solver_var(FILE *f, bv_solver_t *solver, thvar_t x);
extern void print_bv_solver_vardef(FILE *f, bv_solver_t *solver, thvar_t x);
extern void print_bv_solver_var_litarray(FILE* f, bv_solver_t *solver, thvar_t x);

extern void print_bv_solver_atom(FILE *f, bv_solver_t *solver, int32_t id);
extern void print_bv_solver_atomdef(FILE *f, bv_solver_t *solver, int32_t id);
extern void print_bv_solver_atom_of_literal(FILE *f, bv_solver_t *solver, literal_t l);


#endif
