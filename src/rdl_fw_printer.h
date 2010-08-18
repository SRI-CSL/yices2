/*
 * PRINTER FOR THE RDL FLOYD-WARSHALL SOLVER
 */

#ifndef __RDL_FW_PRINTER_H
#define __RDL_FW_PRINTER_H

#include <stdio.h>

#include "rdl_floyd_warshall.h"


/*
 * Name of RDL variable x
 */
extern void print_rdl_var(FILE *f, int32_t x);

/*
 * RDL constant c (q + k.delta)
 */
extern void print_rdl_const(FILE *f, rdl_const_t *c);

/*
 * Atom in format: [<boolvar> := (x - y <= const)
 */
extern void print_rdl_atom(FILE *f, rdl_atom_t *atom);
extern void print_rdl_atoms(FILE *f, rdl_solver_t *rdl);


extern void print_rdl_var_value(FILE *f, rdl_solver_t *rdl, int32_t x);


#endif
