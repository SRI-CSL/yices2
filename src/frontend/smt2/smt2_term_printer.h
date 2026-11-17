/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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
