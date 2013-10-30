/*
 * PRETTY PRINTER FOR SMT2
 */

/*
 * To support (get-value ...), we must print values in the SMT2 notation.
 * So we can't use the default concrete_value_printer.
 *
 * Examples:
 * - a rational number such as -1/2 must be written (/ (- 1) 2)
 * - a bitvector constant must be printed as #b01..00
 * - abstact constant must be have a name that starts with @
 *
 * This module implements the same functions as concrete_value_printer,
 * but with the SMT2 syntax.
 */

#ifndef __SMT2_PRINTER_H
#define __SMT2_PRINTER_H

#include <stdbool.h>

#include "concrete_values.h"
#include "yices_pp.h"


/*
 * Print object c using a pretty printer object
 * - c must be a valid object in table
 * - functions are printed as abstract objects
 */
extern void smt2_pp_object(yices_pp_t *printer, value_table_t *table, value_t c);

/*
 * Print a function map
 * - c must be a valid object in table and must be a function
 * - the maps of c are printed on separate lines
 * - if show_default is true, then the default value is printed on the last line
 */
extern void smt2_pp_function(yices_pp_t *printer, value_table_t *table, value_t c, bool show_default);

/*
 * Expand update c and print it as a function
 * - name = function name to use
 * - if show_default is true, also print the default value
 */
extern void smt2_normalize_and_pp_update(yices_pp_t *printer, value_table_t *table, char *name, value_t c, bool show_default);

/*
 * Print the maps defining the anonymous functions
 * - i.e., all functions whose name is NULL
 * - if show_default is true, print the default value for each map
 */
extern void smt2_pp_anonymous_functions(yices_pp_t *printer, value_table_t *table, bool show_default);



#endif  /* __SMT2_PRINTER_H */
