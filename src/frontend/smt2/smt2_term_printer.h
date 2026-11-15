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
 * PRINT TERMS IN SMT-LIB 2 SYNTAX
 *
 * The term printer in io/term_printer.h uses the Yices language
 * (bv-add, bv-slt, 0b0101, /=, ^, ...). This module prints terms using
 * only SMT-LIB 2 operators (bvadd, bvslt, #b0101, distinct, (* x x), ...).
 *
 * Shared subterms are expanded (no let-bindings).
 */

#ifndef __SMT2_TERM_PRINTER_H
#define __SMT2_TERM_PRINTER_H

#include <stdbool.h>

#include "frontend/smt2/smt2_printer.h"
#include "terms/terms.h"

/*
 * Print term t in SMT-LIB 2 syntax.
 * - t must be a valid term of tbl
 * - return true if t was printed.
 * - return false if t (or one of its subterms) has no SMT-LIB 2 counterpart
 *   supported here (quantifiers, lambda, update, tuples, root atoms,
 *   finite-field terms, scalar constants). In this case, nothing is added
 *   to the printer.
 */
extern bool smt2_pp_term(smt2_pp_t *printer, term_table_t *tbl, term_t t);

#endif /* __SMT2_TERM_PRINTER_H */
