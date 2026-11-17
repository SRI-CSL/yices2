/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */


#ifndef __INT_CONSTRAINT_PRINTER_H
#define __INT_CONSTRAINT_PRINTER_H

#include <stdio.h>

#include "solvers/simplex/integrality_constraints.h"
#include "solvers/simplex/simplex_types.h"


/*
 * Print a constraint:
 * - the format is IsInt(....)
 * - list of fixed variables
 */
extern void print_int_constraint(FILE *f, simplex_solver_t *solver, int_constraint_t *cnstr);




#endif /* __INT_CONSTRAINT_PRINTER_H */
