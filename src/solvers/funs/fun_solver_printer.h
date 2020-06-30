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
 * PRINT FUNCTION/ARRAY SOLVER STRUCTURES
 */

#ifndef __FUN_SOLVER_PRINTER_H
#define __FUN_SOLVER_PRINTER_H

#include <stdint.h>
#include <stdio.h>

#include "solvers/funs/fun_solver.h"
#include "solvers/funs/stratification.h"

extern void print_fsolver_edge(FILE *f, fun_solver_t *solver, uint32_t edge_id);
extern void print_fsolver_edges(FILE *f, fun_solver_t *solver);
extern void print_fsolver_vars(FILE *f, fun_solver_t *solver);
extern void print_fsolver_roots(FILE *f, fun_solver_t *solver);
extern void print_fsolver_classes(FILE *f, fun_solver_t *solver);
extern void print_fsolver_apps(FILE *f, fun_solver_t *solver);
extern void print_fsolver_maps(FILE *f, fun_solver_t *solver);
extern void print_fsolver_base_values(FILE *f, fun_solver_t *solver);
extern void print_fsolver_diseqs(FILE *f, fun_solver_t *solver);
extern void print_fsolver_values(FILE *f, fun_solver_t *solver);
extern void print_fsolver_stratification(FILE *f, stratification_t *s, fun_solver_t *solver);


#endif /* __FUN_SOLVER_PRINTER_H */
