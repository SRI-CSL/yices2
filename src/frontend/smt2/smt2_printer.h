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
#include <gmp.h>

#include "io/yices_pp.h"
#include "model/concrete_values.h"


/*
 * Pretty printer for SMT2 objects:
 * - a regular pretty printer + some extra options
 * - currently: one option for display of bit-vector constants
 *   if bv_as_decimal is true we use "(_ bvX n)" for a bit-vector of n bits
 *   X is the constant value interpreted as an unsigned integer (between 0 and 2^(n-1))
 *   if bv_as_decimal is false, we use "#b010011" format.
 *
 * - aux: auxiliary GMP integer to convert bitvector constants to integer
 */
typedef struct smt2_pp_s {
  yices_pp_t pp;
  bool bv_as_decimal;
  mpz_t aux;
} smt2_pp_t;


/*
 * Initialize a pretty printer:
 * - use file, area, mode, indent as in yices_pp
 * - dec: value for bv_decimal
 */
static inline void init_smt2_pp(smt2_pp_t *printer, FILE *file, pp_area_t *area, pp_print_mode_t mode, bool dec) {
  init_yices_pp(&printer->pp, PP_LANG_SMT2, file, area, mode, 0);
  mpz_init(printer->aux);
  printer->bv_as_decimal = dec;
}

/*
 * Flush
 */
static inline void flush_smt2_pp(smt2_pp_t *printer) {
  flush_yices_pp(&printer->pp);
}

/*
 * Delete
 * - if flush is true, print everything that's pending and a newline
 */
static inline void delete_smt2_pp(smt2_pp_t *printer, bool flush) {
  delete_yices_pp(&printer->pp, flush);
  mpz_clear(printer->aux);
}



/*
 * Print object c using a pretty printer object
 * - c must be a valid object in table
 * - functions are printed as abstract objects and are stored into the table's
 *   internal queue.
 * - the map of all queued functions can then printed later by calling
 *   smt2_pp_queued_functions
 */
extern void smt2_pp_object(smt2_pp_t *printer, value_table_t *table, value_t c);

/*
 * Print a function map
 * - c must be a valid object in table and must be a function
 * - the maps of c are printed on separate lines
 * - if show_default is true, then the default value is printed on the last line
 */
extern void smt2_pp_function(smt2_pp_t *printer, value_table_t *table, value_t c, bool show_default);

/*
 * Expand update c and print it as a function
 * - if show_default is true, also print the default value
 */
extern void smt2_normalize_and_pp_update(smt2_pp_t *printer, value_table_t *table, value_t c, bool show_default);

/*
 * Print the maps of all the queued functions (this may recursively push more
 * functions to the queue and print them).
 * - if show_default is true, print the default value for each map
 * - empty the table's queue
 */
extern void smt2_pp_queued_functions(smt2_pp_t *printer, value_table_t *table, bool show_default);

/*
 * Print a definition in the SMT2 style:
 *
 *   (define-fun name () tau value)
 */
extern void smt2_pp_def(smt2_pp_t *printer, value_table_t *table, const char *name,
			type_t tau, value_t c);


/*
 * Variant of smt2_pp_object that uses an SMT2-like syntax for arrays
 * - tau = type of the object to print.
 * - tau matters only if c is an integer and tau is real?
 */
extern void smt2_pp_smt2_object(smt2_pp_t *printer, value_table_t *table, value_t c, type_t tau);


#endif  /* __SMT2_PRINTER_H */
