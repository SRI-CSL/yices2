/*
 * PRINT BVSOLVER STRUCTURES
 */

#ifndef __BVSOLVER_PRINTER_H
#define __BVSOLVER_PRINTER_H

#include <stdio.h>

#include "bvsolver_types.h"


/*
 * Tables of bitvector variable and atoms
 */
extern void print_bv_vartable(FILE *f, bv_vartable_t *vtbl);
extern void print_bv_atomtable(FILE *f, bv_atomtable_t *atbl);


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
 * Individual variable or atom
 */
extern void print_bv_solver_var(FILE *f, bv_solver_t *solver, thvar_t x);
extern void print_bv_solver_vardef(FILE *f, bv_solver_t *solver, thvar_t x);

extern void print_bv_solver_atom(FILE *f, bv_solver_t *solver, int32_t id);
extern void print_bv_solver_atomdef(FILE *f, bv_solver_t *solver, int32_t id);
extern void print_bv_solver_atom_of_literal(FILE *f, bv_solver_t *solver, literal_t l);


#endif
