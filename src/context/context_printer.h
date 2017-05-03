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
 * PRINT CONTEXT
 */

#ifndef __CONTEXT_PRINTER_H
#define __CONTEXT_PRINTER_H

#include <stdio.h>

#include "context/context_types.h"


/*
 * Internal structures used in flattening/simplifications/internalization
 */
extern void print_context_subst_eqs(FILE *f, context_t *ctx);
extern void print_context_top_eqs(FILE *f, context_t *ctx);
extern void print_context_top_atoms(FILE *f, context_t *ctx);
extern void print_context_top_formulas(FILE *f, context_t *ctx);
extern void print_context_top_interns(FILE *f, context_t *ctx);

// substitution and internalization mapping
// stored in the internalization table
extern void print_context_intern_subst(FILE *f, context_t *ctx);
extern void print_context_intern_mapping(FILE *f, context_t *ctx);



/*
 * Pretty printing: display the result of flattening + variable elimination
 */
extern void pp_context(FILE *f, context_t *ctx);


#endif /* __CONTEXT_PRINTER_H */
