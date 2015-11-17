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

#include "io/yices_pp.h"
#include "model/concrete_values.h"


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
 * PRETTY PRINTING
 */

/*
 * Same as above, but using a pretty_printer object
 */
extern void vtbl_pp_object(yices_pp_t *printer, value_table_t *table, value_t c);


#endif /* __CONCRETE_VALUE_PRINTER_H */
