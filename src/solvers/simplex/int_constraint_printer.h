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
