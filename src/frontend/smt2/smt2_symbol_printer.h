/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef __SMT2_SYMBOL_PRINTER
#define __SMT2_SYMBOL_PRINTER

#include "frontend/smt2/smt2_printer.h"

/*
 * Print a symbol: add quotes if needed.
 */
extern void smt2_pp_symbol(smt2_pp_t *printer, const char *name);

#endif
