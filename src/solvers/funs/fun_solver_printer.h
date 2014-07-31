/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PRINT FUNCTION/ARRAY SOLVER STRUCTURES
 */

#ifndef __FUN_SOLVER_PRINTER_H
#define __FUN_SOLVER_PRINTER_H

#include <stdint.h>
#include <stdio.h>

#include "solvers/funs/fun_solver.h"

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



#endif /* __FUN_SOLVER_PRINTER_H */
