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
 * PRINTER FOR THE RDL FLOYD-WARSHALL SOLVER
 */

#ifndef __RDL_FW_PRINTER_H
#define __RDL_FW_PRINTER_H

#include <stdio.h>

#include "solvers/floyd_warshall/rdl_floyd_warshall.h"


/*
 * Name of vertex x
 */
extern void print_rdl_vertex(FILE *f, int32_t x);

/*
 * RDL constant c (q + k.delta)
 */
extern void print_rdl_const(FILE *f, rdl_const_t *c);

/*
 * Value of vertex x in the graph
 * - this prints distance[0, x] as the value
 * - of ??? if there's no path from 0 to x
 */
extern void print_rdl_vertex_value(FILE *f, rdl_solver_t *rdl, int32_t x);

/*
 * Atom in format: [<boolvar> := (x - y <= const)]
 */
extern void print_rdl_atom(FILE *f, rdl_atom_t *atom);
extern void print_rdl_atoms(FILE *f, rdl_solver_t *rdl);


/*
 * Difference logic triple (x - y + d)
 * - x and y are vertices
 */
extern void print_rdl_triple(FILE *f, dl_triple_t *triple);


/*
 * Variable triples: in the format u := (x - y + d)
 * - x and y are vertices
 * - u is a theory variable
 */
extern void print_rdl_var_name(FILE *f, thvar_t u);
extern void print_rdl_var_def(FILE *f, rdl_solver_t *solver, thvar_t u);
extern void print_rdl_var_table(FILE *f, rdl_solver_t *solver);


/*
 * Edges
 */
extern void print_rdl_axioms(FILE *f, rdl_solver_t *solver);
extern void print_rdl_edges(FILE *f, rdl_solver_t *solver);



#endif
