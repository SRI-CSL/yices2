/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
