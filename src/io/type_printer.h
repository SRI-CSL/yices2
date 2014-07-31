/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
