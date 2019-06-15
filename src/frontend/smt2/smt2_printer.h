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
