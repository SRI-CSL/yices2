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
 * Print reverse internalization data for code:
 * - print what's mapped to code if any
 */
extern void print_intern_reverse(FILE *f, intern_tbl_t *tbl, int32_t code);

/*
 * Print the term mapped to occurrence x (if any)
 */
extern void intern_tbl_print_reverse(intern_tbl_t *tbl, occ_t x);

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
