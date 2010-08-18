/*
 * PRINTER FOR THE IDL FLOYD-WARSHALL SOLVER
 */

#ifndef __IDL_FW_PRINTER_H
#define __IDL_FW_PRINTER_H

#include <stdio.h>

#include "idl_floyd_warshall.h"


/*
 * Print name of variable x
 */
extern void print_idl_var(FILE *f, int32_t x);

/*
 * Atom: in format [<bool var> := (x - y <= d)]
 */
extern void print_idl_atom(FILE *f, idl_atom_t *atom);
extern void print_idl_atoms(FILE *f, idl_solver_t *idl);


/*
 * Value of var x in the idl solver
 * - we use distance[0, v] as the value
 * - if the distance is not defined we print ???
 */
extern void print_idl_var_value(FILE *f, idl_solver_t *idl, int32_t x);


#endif /* __IDL_FW_PRINTER_H */
