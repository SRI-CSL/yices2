/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * OUTPUT FUNCTIONS FOR CONCRETE VALUES
 */

#ifndef __CONCRETE_VALUE_PRINTER_H
#define __CONCRETE_VALUE_PRINTER_H

#include <stdio.h>
#include <stdbool.h>

#include "model/concrete_values.h"
#include "io/yices_pp.h"


/*
 * BASIC PRINTING
 */

/*
 * Print object c
 * - c must be a valid object in table
 * - no pretty printing
 * - functions are printed as uninterpreted objects and are pushed into table's internal queue
 */
extern void vtbl_print_object(FILE *f, value_table_t *table, value_t c);


/*
 * Print a function map
 * - c must be a valid object in table and must be a function
 * - the maps of c are printed on separate lines
 * - if show_default is true, then the default value is printed on the last line
 */
extern void vtbl_print_function(FILE *f, value_table_t *table, value_t c, bool show_default);


/*
 * Expand update c and print it as a function
 * - name = function name to use
 * - if name is NULL, a made-up name is used instead (of the form "fun!xxx")
 * - if show_default is true, also print the default value
 */
extern void vtbl_normalize_and_print_update(FILE *f, value_table_t *table, const char *name,
                                            value_t c, bool show_default);


/*
 * Print the maps defining all the queue'd functions
 * (this may recursively queue more objects and print them too).
 * - if show_default is true, print the default value for each map
 * - once all queued functions are printed, reset the queue.
 */
extern void vtbl_print_queued_functions(FILE *f, value_table_t *table, bool show_default);


/*
 * PRETTY PRINTING
 */

/*
 * Same print functions as above, but using a pretty_printer object
 */
extern void vtbl_pp_object(yices_pp_t *printer, value_table_t *table, value_t c);
extern void vtbl_pp_function(yices_pp_t *printer, value_table_t *table, value_t c, bool show_default);
extern void vtbl_normalize_and_pp_update(yices_pp_t *printer, value_table_t *table, const char *name,
                                         value_t c, bool show_default);
extern void vtbl_pp_queued_functions(yices_pp_t *printer, value_table_t *table, bool show_default);


#endif /* __CONCRETE_VALUE_PRINTER_H */
