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
 */
extern void smt2_pp_object(yices_pp_t *printer, value_table_t *table, value_t c);


#endif  /* __SMT2_PRINTER_H */
