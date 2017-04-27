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
 * Print types
 */

#ifndef __TYPE_PRINTER_H
#define __TYPE_PRINTER_H

#include <stdio.h>

#include "io/yices_pp.h"
#include "terms/types.h"

/*
 * Type id: either bool, int, real or a default id
 */
extern void print_type_id(FILE *f, type_t tau);


/*
 * Print macro name/macro definition
 * - print id = macro id
 */
extern void print_macro_name(FILE *f, type_table_t *tbl, int32_t id);
extern void print_macro_def(FILE *f, type_table_t *tbl, int32_t id);

/*
 * Print all the macros
 */
extern void print_type_macros(FILE *f, type_table_t *tbl);


/*
 * Print functions:
 * - print type expression
 * - print only the name (or a default id if there's no name)
 * - print definition as 'name := def'
 * - print type: print the name if tau has a name, otherwise expand
 */
extern void print_type_exp(FILE *f, type_table_t *tbl, type_t tau);
extern void print_type_name(FILE *f, type_table_t *tbl, type_t tau);
extern void print_type_def(FILE *f, type_table_t *tbl, type_t tau);

extern void print_type(FILE *f, type_table_t *tbl, type_t tau);

/*
 * Print the type table
 */
extern void print_type_table(FILE *f, type_table_t *tbl);


/*
 * Pretty printing
 * - print type expression
 * - print type name
 * - print type (name or expression)
 */
extern void pp_type_exp(yices_pp_t *printer, type_table_t *tbl, type_t tau);
extern void pp_type_name(yices_pp_t *printer, type_table_t *tbl, type_t tau);
extern void pp_type(yices_pp_t *printer, type_table_t *tbl, type_t tau);

/*
 * Pretty print the type table
 */
extern void pp_type_table(FILE *f, type_table_t *tbl);

#endif /* __TYPE_PRINTER_H */
