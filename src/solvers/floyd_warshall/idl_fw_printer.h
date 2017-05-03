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
 * PRINTER FOR THE IDL FLOYD-WARSHALL SOLVER
 */

#ifndef __IDL_FW_PRINTER_H
#define __IDL_FW_PRINTER_H

#include <stdio.h>

#include "solvers/floyd_warshall/idl_floyd_warshall.h"


/*
 * Print name of a vertex x
 */
extern void print_idl_vertex(FILE *f, int32_t x);


/*
 * Value of vertex x in the idl solver
 * - we use distance[0, v] as the value
 * - if the distance is not defined we print ???
 */
extern void print_idl_vertex_value(FILE *f, idl_solver_t *idl, int32_t x);


/*
 * Atom: in format [<bool var> := (x - y <= d)]
 * - x and y are vertices
 */
extern void print_idl_atom(FILE *f, idl_atom_t *atom);
extern void print_idl_atoms(FILE *f, idl_solver_t *idl);


/*
 * Difference logic triple (x - y + d)
 * - x and y are vertices
 */
extern void print_idl_triple(FILE *f, dl_triple_t *triple);


/*
 * Variable triples: in the format u := (x - y + d)
 * - x and y are vertices
 * - u is a theory variable
 */
extern void print_idl_var_name(FILE *f, thvar_t u);
extern void print_idl_var_def(FILE *f, idl_solver_t *solver, thvar_t u);
extern void print_idl_var_table(FILE *f, idl_solver_t *solver);


/*
 * Edges
 */
extern void print_idl_axioms(FILE *f, idl_solver_t *solver);
extern void print_idl_edges(FILE *f, idl_solver_t *solver);


#endif /* __IDL_FW_PRINTER_H */
