/*
 * Print types
 */

#ifndef __TYPE_PRINTER_H
#define __TYPE_PRINTER_H

#include <stdio.h>
#include "types.h"

/*
 * Type id: either bool, int, real or a default id
 */
extern void print_type_id(FILE *f, type_t tau);

/*
 * Four print functions:
 * - only the name (or a default id if there's no name)
 * - print type expression
 * - print type definition 'name := def'
 */
extern void print_type(FILE *f, type_table_t *tbl, type_t tau);
extern void print_type_name(FILE *f, type_table_t *tbl, type_t tau);
extern void print_type_def(FILE *f, type_table_t *tbl, type_t tau);

/*
 * Print the full type table
 */
extern void print_type_table(FILE *f, type_table_t *tbl);

#endif /* __TYPE_PRINTER_H */
