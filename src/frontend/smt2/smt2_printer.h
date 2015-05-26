/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PRETTY PRINTER FOR SMT2
 */

/*
 * To support (get-value ...), we must print values in the SMT2 syntax.
 * So we can't use the default concrete_value_printer.
 *
 * Examples:
 * - a rational number such as -1/2 must be written (/ (- 1) 2)
 * - a bitvector constant must be printed as #b01..00
 * - abstract constant must be have a name that starts with @
 *
 * This module implements the same functions as concrete_value_printer,
 * but with the SMT2 syntax.
 */

#ifndef __SMT2_PRINTER_H
#define __SMT2_PRINTER_H

#include <stdbool.h>

#include "io/yices_pp.h"
#include "model/concrete_values.h"


/*
 * Print object c using a pretty printer object
 * - c must be a valid object in table
 * - functions are printed as abstract objects and are stored into the table's
 *   internal queue.
 * - the map of all queued functions can then printed later by calling
 *   smt2_pp_queued_functions
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
 * - if show_default is true, also print the default value
 */
extern void smt2_normalize_and_pp_update(yices_pp_t *printer, value_table_t *table, value_t c, bool show_default);

/*
 * Print the maps of all the queued functions (this may recursively push more
 * functions to the queue and print them).
 * - if show_default is true, print the default value for each map
 * - empty the table's queue
 */
extern void smt2_pp_queued_functions(yices_pp_t *printer, value_table_t *table, bool show_default);



#endif  /* __SMT2_PRINTER_H */
