/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PRINT INTERNALIZATION TABLE
 */

#ifndef __INTERNALIZATION_PRINTER_H
#define __INTERNALIZATION_PRINTER_H

#include <stdio.h>

#include "context/internalization_table.h"


/*
 * Print internalization data for term t:
 * - print t's root in the substitution tree
 * - print what's mapped to t if any
 */
extern void print_term_intern(FILE *f, intern_tbl_t *tbl, term_t t);


/*
 * Print all substitution data in tbl
 */
extern void print_intern_substitution(FILE *f, intern_tbl_t *tbl);


/*
 * Print all internalization mappings in tbl
 */
extern void print_intern_mapping(FILE *f, intern_tbl_t *tbl);


/*
 * Variant format for substitution
 */
extern void print_intern_substitution2(FILE *f, intern_tbl_t *tbl);



#endif /* __INTERNALIZATION_PRINTER_H */
